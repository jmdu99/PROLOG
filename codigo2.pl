:- module(_, _, [assertions]).

alumno_prode('Diaz','Urraco','Jose Manuel','Z170085').
alumno_prode('Mori','De La Cruz','Guisell Eliana','Y160065').
alumno_prode('Tagarro','Lopez de Ayala','Eva','Z170183').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% basic_building(X): verifica que X es un edificio, que contiene números naturales y que debe tener
% al menos un nivel y cada nivel al menos una vivienda.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado basic_building(X) comprueba recursivamente, recorriendo el edificio pasado como parametro, elemento por elemento que dicho edificio tenga como minimo un nivel con una vivienda y que todas las viviendas esten representadas con numeros naturales. Como caso base hemos usado [X] para que siempre tenga que haber al menos un elemento. Y si se pasa un edificio vacio de error.

:- pred basic_building(X)
#"Verifica que @var{X} es un edificio, que contiene números naturales y que debe tener al menos un nivel y cada nivel al menos una vivienda. @includedef{basic_building/1}".
basic_building([X]):- pisoValido(X).
basic_building([X|Y]):- pisoValido(X), basic_building(Y).

% pisoValido(L): verifica si L es una lista de números naturales.
:- pred pisoValido(L)
#"Verifica si @var{L} es una lista de números naturales. @includedef{pisoValido/1}".
pisoValido([X]):- natural(X).
pisoValido([E|L]):- natural(E), pisoValido(L).

% natural(X): verifica si X es un número natural.
:- prop natural(X)
#"Verifica si @var{X} es un numero natural. @includedef{natural/1}".
natural(0).
natural(s(X)):- natural(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% building(X): verifica que X es un edificio como el anterior pero ademas todos los niveles deben tener el mismo numero de viviendas.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado building(X) comprueba que el edificio X pasado como parametro sea un basic building y que todos los niveles tengan el mismo numero de viviendas. Para comprobar esta ultima condicion, se crea una nueva lista en la que metemos el numero de viviendas por cada piso. Y, con la lista terminada, comprobamos que todos sus elementos sean iguales. Como caso base usa el del predicado building. Ya que asi aseguramos que haya al menos un elemento en el edificio.

:- pred building(X)
#"Verifica que @var{X} es un edificio como el anterior pero ademas todos los niveles deben tener el mismo numero de viviendas. @includedef{building/1}".
building(X):- basic_building(X), pisoValido2(X,N), todosIguales(N).

% pisoValido2(L1,L2): comprueba que en L2 esta el numero correcto de las casas de cada piso (tamaño de cada sublista).
:- pred pisoValido2(L1,L2)
#"Comprueba que en @var{L2} esta el numero correcto de las casas de cada piso (tamaño de cada sublista). @includedef{pisoValido2/2}".
pisoValido2([],[]).
pisoValido2([X|Y],L):- pisoValido2(Y,L1), tamanoLista(X,N), concatenar([N],L1,L).

% tamanoLista(Y,N): comprueba que el edificio Y tenga N pisos (que la lista Y tenga N elementos).
:- pred tamanoLista(Y,N)
#"Comprueba que el edificio @var{Y} tenga @var{N} pisos (que la lista @var{Y} tenga @var{N} elementos). @includedef{tamanoLista/2}".
tamanoLista([],0).
tamanoLista([_X|Y],s(N)):- tamanoLista(Y,N).

% concatenar(L1, L2, L3): comprueba que L3 es la concatenacion de la lista L1 con la lista L2.
:- pred concatenar(L1,L2,L3)
#"Comprueba que @var{L3} es la concatenacion de la lista @var{L1} con la lista @var{L2}. @includedef{concatenar/3}".
concatenar([],L,L).
concatenar([X|Y],Z,[X|U]):- concatenar(Y,Z,U).

% todosIguales(X): comprueba que la lista X tenga todos sus elementos iguales.
:- pred todosIguales(X)
#"Comprueba que en la lista @var{X} tenga todos sus elementos iguales. @includedef{todosIguales/1}".
todosIguales([]).
todosIguales([_]).
todosIguales([X,X|U]):- todosIguales([X|U]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% level(X,N,C): verifica que C es el nivel N-esimo del edificio X (la lista con todas las viviendas de ese nivel).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado level(X,N,C) comprueba que el edificio X pasado como parametro sea un basic building y despues va recorriendo el edificio piso por piso hasta el piso numero N que queremos. Se realiza con el uso de un contador al que se le va restando una unidad por cada piso que recorre hasta llegar al deseado (que sera cuando el contador tenga un s(0) en el caso base). Como casos base usa el del predicado basic_building (que es el de building), asegurando que haya al menos un elemento en el edificio. Y ademas, el levelAux el decremento del contador hasta s(0) como hemos comentado anteriormente.

:- pred level(X,N,C)
#"Verifica que @var{C} es el nivel @var{N} del edificio @var{X} (la lista con todas las viviendas de ese nivel). @includedef{level/3}".
level(X,N,C):- building(X), levelAux(X,N,C).

% levelAux(X,N,C): predicado auxiliar de level. Se hace cierto en los mismos casos que level pero ademas tambien cuando no se cumple la condicion building, que se comprueba previamente en el propio predicado level(X,N,C).
:- pred levelAux(X,N,C)
#"Predicado auxiliar de level. Se hace cierto en los mismos casos que level pero ademas tambien cuando no se cumple la condicion building, que se comprueba previamente en el propio predicado level(X,N,C).@includedef{levelAux/3}".
levelAux([C],s(0),C).
levelAux([C,_|_],s(0),C).
levelAux([_,Y|Ys],s(s(X)),C):- levelAux([Y|Ys],s(X),C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% column(X,N,C): verifica que C es la lista formada por las viviendas N-esimas de todos los niveles del edificio X.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado column(X,N,C) comprueba que el edificio X pasado como parametro sea un basic building y despues va a comprobar que C es la lista de las viviendas N-esimas de todos los niveles de X. Para ello, mediante el uso de funciones auxiliares, vamos borrando las primeras columnas de la matriz hasta que la primera columna sea la que queremos. Una vez ahi, sacamos la primera columna de la matriz (con otra funcion auxiliar) para asi devolverla como parametro. Como caso base usa el del predicado building. Y en las funciones auxiliares el uso de un contador hasta s(0) y de listas vacias para que se puedan ir construyendo las nuevas matrices.

% Forma de obtencion de column: borrarNPrimerosElementos y sacarPrimeraColumnaEdificio para obtener la lista C que queremos.

:- pred column(X,N,Columna)
#"Verifica que @var{C} es la lista formada por las viviendas de @var{N} de todos los niveles del edificio @var{X}. @includedef{column/3}".
column(X,N,Columna):- building(X), borrarNPrimerosElementos(X,N,Y), sacarPrimeraColumnaEdificio(Y,Columna).

% borrarNPrimerosElementos(X,N,Y): verifica que Y sea submatriz del edificio X cuya columna numero N sea la primera.
:- pred borrarNPrimerosElementos(X,N,Y)
#"Verifica que @var{Y} sea una submatriz del edificio @var{X} cuya columna numero @var{N} sea la primera. @includedef{borrarNPrimerosElementos/3}".
borrarNPrimerosElementos(X,s(0),X).
borrarNPrimerosElementos(X,s(s(N)),Y):- borrarPrimerElemento(X,Y1), borrarNPrimerosElementos(Y1,s(N),Y).

% borrarPrimerElemento(X,Y): verifica que Y es el edificio resultante de borrar la primera columna del edificio X
% (se borra la vivienda 1 de cada piso, que es el primer elemento de cada sublista).
:- pred borrarPrimerElemento(X,Y)
#"Verifica que @var{Y} es el edificio resultante de borrar la primera columna del edificio @var{X} (se borra la vivienda 1 de cada piso, que es el primer elemento de cada sublista). @includedef{borrarPrimerElemento/2}".
borrarPrimerElemento([],[]).
borrarPrimerElemento([[_|X]|Z],[X|Y]) :- borrarPrimerElemento(Z,Y).

% sacarPrimeraColumnaEdificio(X,C): verifica que C sea la primera columna (viviendas 1 de cada piso) del edificio X.
:- pred sacarPrimeraColumnaEdificio(X,C)
#"Verifica que @var{C} sea la primera columna (viviendas 1 de cada piso) del edificio @var{X}. @includedef{sacarPrimeraColumnaEdificio/2}".
sacarPrimeraColumnaEdificio([],[]).
sacarPrimeraColumnaEdificio([[X|_]|Z],[X|Y]) :- sacarPrimeraColumnaEdificio(Z,Y).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% columns(X,C): verifica que C sea la lista de las columnas de viviendas del edificio X.
% O lo que es igual, verificar que C sea la matriz traspuesta del edificio X.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado columns(X,C) comprueba que el edificio X pasado como parametro sea un basic building y despues va a comprobar que C sea la matriz traspuesta de X. Para realizar la trasposicion se llama a la funcion columnsAux que lo que hace, mediante las funciones auxiliares usadas en el predicado column, es borrar la primera columna de la matriz (viviendas 1 de todos los pisos), esa columna nos la guardamos para que se añada a la nueva matriz traspuesta como fila y se vuelve a llamar recursivamente a columnsAux con la matriz resultante de borrar la primera columna. Como caso base usa el del predicado building. Y en columnsAux listas vacias para que se puedan ir construyendo las nuevas matrices.

:- pred columns(X,C)
#"Verifica que @var{C} sea la lista de las columnas de viviendas del edificio @var{X}.O lo que es igual, verificar que @var{C} sea la matriz traspuesta del edificio @var{X}. @includedef{columns/2}".
columns(X,C):- building(X), columnsAux(X,C).

% columnsAux(X,C): predicado auxiliar de columns. Se hace cierto en los mismos casos que columns pero ademas tambien cuando no se cumple la condicion building, que se comprueba previamente en el propio predicado columns(X,C).
% Variables columnsAux: [X: edificio original], [Y: edificio sin primera columna], [C: primera columna del edificio (primera fila matriz traspuesta)], [Cs: resto de la matriz traspuesta].
:- pred columnsAux(X,C)
#"Predicado auxiliar de columns. Se hace cierto en los mismos casos que columns pero ademas tambien cuando no se cumple la condicion building, que se comprueba previamente en el propio predicado columns(@var{X},@var{C}). Variables columnsAux: [@var{X}: edificio original], [@var{Y}: edificio sin primera columna], [@var{C}: primera columna del edificio (primera fila matriz traspuesta)], [Cs: resto de la matriz traspuesta].@includedef{columnsAux/2}".
columnsAux([[]|_],[]).
columnsAux(X, [C|Cs]):- borrarPrimerElemento(X,Y), sacarPrimeraColumnaEdificio(X,C), columnsAux(Y,Cs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% total_people(X,T): verifica que T sea el numero total de personas que viven en el edificio X.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado total_people(X,T) comprueba que el edificio X pasado como parametro sea un basic building y que T sea el numero total de personas de X. Para esto ultimo vamos recorriendo el edificio X vivienda por vivienda y nos guardamos en una lista auxiliar el numero de personas de cada vivienda. Una vez recorrido todo el edificio, sumamos tosos los elementos de la lista auxiliar y nos devuelve el numero total de personas que viven en el edificio. Como caso base usa el del predicado building. Y en las funciones auxiliares listas vacias para que se puedan ir construyendo las nuevas matrices y listas.

:- pred total_people(X,T)
#"Verifica que @var{T} sea el numero total de personas que viven en el edificio @var{X}. @includedef{total_people/2}".
total_people(X,T):- building(X), concatenar_matriz(X,R), suma_elementos_lista(R,T).

% concatenar_matriz(X,R): verifica que R sea una lista con todos los elementos del edificio X.
:- pred concatenar_matriz(X,R)
#"Verifica que @var{R} sea una lista con todos los elementos del edificio @var{X}. @includedef{concatenar_matriz/2}".
concatenar_matriz([],[]).
concatenar_matriz([X|Xs],R):- concatenar_matriz(Xs,Y), concatenar(X,Y,R).

% suma_elementos_lista(X,N): verifica que N sea la suma de todos los elementos de la lista X.
:- pred suma_elementos_lista(X,N)
#"Verifica que @var{N} sea la suma de todos los elementos de la lista @var{X}. @includedef{suma_elementos_lista/2}".
suma_elementos_lista([],0).
suma_elementos_lista([X|Y],S):- suma_elementos_lista(Y,N), suma(N,X,S).

% suma(X,Y,Z): cierto si y solo si Z es la suma de X e Y.
:- pred suma(X,Y,Z)
#"Devuelve cierto si y solo si @var{Z} es la suma de @var{X} y @var{Y}. @includedef{suma/3}".
suma(0,X,X):- natural(X).
suma(s(X),Y,s(Z)):- suma(X,Y,Z).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% average(X,A): verifica que A sea la media de personas que viven en cada vivienda del edificio truncada al numero natural entero.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% El predicado average(X,A) comprueba que el edificio X pasado como parametro sea un basic building (mediante la llamada a total_people) y que A sea la media de personas que viven en cada vivienda del edificio truncada al numero natural entero. Para ello el algoritmo usado es realizar la division de todas las personas que viven en el edificio (obtenidas mediante una llamada a total_people) entre el numero de viviendas (obtenido mediante una funcion auxiliar que guarda el numero de personas de cada vivienda en una lista auxiliar, y al final  obtiene el numero de elementos de dicha lista mediante la llamada a la funcion auxiliar definida previamente tamanoLista). Para realizar la division, al numero total de personas T se le resta el numero de viviendas N del edificio y en un contador se aumenta en 1 unidad. Se vuelve a llamar al predicado division pero con T-N personas comprobando que T-N sea siempre mayor que N (para obetenr el numero natural entero truncado). Como caso base usa el del predicado building. Y en la funcion auxiliar division llegar al punto en el que T sea menor que V, que sera el momento en el que habra que parar las restas sucesivas.

:- pred average(X,A)
#"Verifica que @var{A} sea la media de personas que viven en cada vivienda del edificio @var{X} truncada al numero natural entero. @includedef{average/2}".
average(X,A):- total_people(X,T), numero_viviendas_totales(X,V), division(T,V,A).

% numero_viviendas_totales(X,T): verifica que T sea el numero de viviendas totales del edificio X.
:- pred numero_viviendas_totales(X,T)
#"Verifica que @var{T} sea el numero de viviendas totales del edificio @var{X}. @includedef{numero_viviendas_totales/2}".
numero_viviendas_totales(X,T):- concatenar_matriz(X,R), tamanoLista(R,T).

% division(T,V,S): verifica que se cumpla la operacion T/V=S (division entera con truncamiento).
:- pred division(T,V,S)
#"Verifica que se cumpla la operacion @var{T}/@var{V}=@var{S} (division entera con truncamiento). @includedef{division/3}".
division(T,V,0):- menor_que(T,V).
division(T,V,S):- resta(T,V,T1), division(T1,V,S1), suma(S1,s(0),S).

% menor_que(X,Y): comprueba que X sea menor que Y.
:- pred menor_que(X,Y)
#"Comprueba que @var{X} sea menor que @var{Y}. @includedef{menor_que/2}".
menor_que(0,s(X)):- natural(X).
menor_que(s(X),s(Y)):- menor_que(X,Y).

% resta(X,Y,Z): cierto si y solo si Z es la resta de X menos Y, siendo X mayor que Y (resta de naturales).
:- pred resta(X,Y,Z)
#"Devuelve cierto si y solo si @var{Z} es la resta de @var{X} menos @var{Y}, siendo @var{X} mayor que @var{Y} (resta de naturales). @includedef{resta/3}".
resta(X,Y,Z):- suma(Y,Z,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
TESTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests basic_building(X)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 1 nivel, se verifica que no esta vacio.
:- test basic_building(X) : (X=[[0]]) + not_fails.
% Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.
:- test basic_building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + not_fails.
% Dado un edificio con 3 niveles, se verifica que ninguno de los 3 niveles esta vacio.
:- test basic_building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + not_fails.
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test basic_building(X) : (X=[]) + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test basic_building(X) : (X=[[]]) + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test basic_building(X) : (X=[[],[]]) + fails  #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test basic_building(X) : (X=[[5]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test basic_building(X) : (X=[[hola]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test basic_building(X) : (X=[["hola"]]) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test basic_building(X) : (X=[[0],[]]) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.
:- test basic_building(X) : (X=[[0],[s(0)]]) + not_fails.
% Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.
:- test basic_building(X) : (X=[[0,s(0)],[s(0)]]) + not_fails.
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test basic_building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails  #"No hay vivienda en el tercer nivel.".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests building(X)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #"No hay el mismo numero de viviendas en los dos niveles.".
% Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #"No hay el mismo numero de viviendas en los tres niveles.".
% Dado un edificio con 1 nivel, se verifica que no esta vacio.
:- test building(X) : (X=[[0]]) + not_fails.
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test building(X) : (X=[]) + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test building(X) : (X=[[]]) + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test building(X) : (X=[[],[]]) + fails  #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test building(X) : (X=[[5]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test building(X) : (X=[[hola]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test building(X) : (X=[["hola"]]) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test building(X) : (X=[[0],[]]) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.
:- test building(X) : (X=[[0],[s(0)]]) + not_fails.
% Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.
:- test building(X) : (X=[[0,s(0)],[s(0),0]]) + not_fails.
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails  #"No hay vivienda en el tercer nivel.".
% Dado un edificio con 3 niveles, se verifica que cada nivel tiene 2 viviendas.
:- test building(X) : (X=[[0,s(0)],[s(0),0],[s((0)),0]]) + not_fails.
% Dado un edificio con 3 niveles, se verifica que cada nivel tiene 3 viviendas.
:- test building(X) : (X=[[0,s(0),0],[s(0),0,0],[s(0),0,0]]) + not_fails.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests level(X,N,C)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #"No hay vivienda en el tercer nivel.".
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test level(X,N,C) : (X=[], N=s(0))  + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test level(X,N,C) : (X=[[]], N=s(0))  + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test level(X,N,C) : (X=[[],[]], N=s(0)) + fails  #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test level(X,N,C) : (X=[[5]], N=s(0)) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test level(X,N,C) : (X=[[hola]], N=s(0)) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test level(X,N,C) : (X=[["hola"]], N=s(0)) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test level(X,N,C) : (X=[[0],[]], N=s(0)) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]], N=s(0)) + fails #"No hay el mismo numero de viviendas en los dos niveles.".
% Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]], N=s(0)) + fails #"No hay el mismo numero de viviendas en los tres niveles.".
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #"No hay vivienda en el tercer nivel.".
% Dado un edificio con 2 niveles, se buscan las viviendas del nivel 2.
:- test level(X,N,C) : (X=[[0,s(0)],[s(0),s(0)]], N=s(s(0))) => (C=[s(0),s(0)]) + not_fails.
% Dado un edificio con 3 niveles, se buscan las viviendas del nivel 1.
:- test level(X,N,C) : (X=[[0,s(0),0,s(s(s(0)))],[s(0),s(0),0,s(s(s(s(0))))],[s(0),0,0,s(s(0))]], N=s(0)) => (C=[0,s(0),0,s(s(s(0)))]) + not_fails.
% Dado un edificio con 3 niveles, se buscan las viviendas del nivel 3.
:- test level(X,N,C) : (X=[[s(0)],[0],[s(s(0))]], N=s(s(s(0)))) => (C=[s(s(0))]) + not_fails.
% Dado un edificio con 6 niveles, se buscan las viviendas del nivel 4.
:- test level(X,N,C) : (X=[[s(s(s(0)))],[s(s(s(s(0))))],[s(0)],[s(0)],[0],[s(0)]], N=s(s(s(s(0))))) => (C=[s(0)]) + not_fails.
% Dado un edificio con 3 niveles, se busca en que nivel estan las viviendas especificadas.
:- test level(X,N,C) : (X=[[s(0),s(0),0],[s(0),s(0),s(0)],[0,0,s(0)]], C=[0,0,s(0)]) => (N=s(s(s(0)))) + not_fails.
% Dado un edificio con 2 niveles, se busca en que nivel estan las viviendas especificadas.
:- test level(X,N,C) : (X=[[s(0),s(s(0)),s(s(s(0)))],[0,0,s(s(0))]], C=[0,0,s(s(0))]) => (N=s(s(0))) + not_fails.
% Dado un edificio con 4 niveles, se buscan las viviendas del nivel 4; pero la funcion devuelve las de un nivel incorrecto.
:- test level(X,N,C) : (X=[[0,s(0)],[s(0),s(0)],[0,0],[s(0),0]], N=s(s(s(s(0)))), C=[s(0),s(0)]) + fails #"Lista de viviendas del nivel incorrecto.".
% Dado un edificio con 3 niveles, se buscan las viviendas del nivel 2; pero la funcion devuelve las de un nivel incorrecto.
:- test level(X,N,C) : (X=[[0,s(0)],[s(0),s(0)],[0,0]], N=s(s(0)), C=[0,0]) + fails #"Lista de viviendas del nivel incorrecto.".
% Dado un edificio con 2 niveles, se buscan las viviendas del nivel 1; pero la funcion devuelve las de un nivel incorrecto.
:- test level(X,N,C) : (X=[[0,s(s(s(0)))],[s(s(0)),s(s(s(0)))]], N=s(0), C=[s(s(0)),s(s(s(0)))]) + fails #"Lista de viviendas del nivel incorrecto.".
% Dado un edificio con 3 niveles, se buscan las viviendas del nivel 3; pero la funcion devuelve las de un nivel incorrecto.
:- test level(X,N,C) : (X=[[s(0)],[s(s(s(0)))],[0]], N=s(s(s(0))), C=[s(0)]) + fails #"Lista de viviendas del nivel incorrecto.".
% Dado un edificio con 3 niveles, se buscan las viviendas del nivel 5; pero el edificio no tiene tantos niveles.
:- test level(X,N,C) : (X=[[0,0],[s(0),s(0)],[s(0),0]], N=s(s(s(s(s(0)))))) + fails #"El edificio no tiene ese numero de niveles.".
% Dado un edificio con 3 niveles, se busca en que nivel estan las viviendas especificadas; pero la funcion devuelve un numero de nivel incorrecto.
:- test level(X,N,C) : (X=[[s(0),s(0),0],[s(0),s(0),s(0)],[0,0,s(0)]], N=s(0), C=[0,0,s(0)]) + fails #"Nivel devuelto incorrecto.".
% Dado un edificio con 4 niveles, se busca en que nivel estan las viviendas especificadas; pero la funcion devuelve un numero de nivel incorrecto.
:- test level(X,N,C) : (X=[[0],[s(0)],[s(0)],[s(s(0))]], N=s(s(0)), C=[0]) + fails #"Nivel devuelto incorrecto.".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests column(X,N,C)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #"No hay vivienda en el tercer nivel.".
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test column(X,N,C) : (X=[], N=s(0)) + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test column(X,N,C) : (X=[[]], N=s(0)) + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test column(X,N,C) : (X=[[],[]], N=s(0)) + fails  #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test column(X,N,C) : (X=[[5]], N=s(0)) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test column(X,N,C) : (X=[[hola]], N=s(0)) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test column(X,N,C) : (X=[["hola"]], N=s(0)) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test column(X,N,C) : (X=[[0],[]], N=s(0)) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]], N=s(0)) + fails #"No hay el mismo numero de viviendas en los dos niveles.".
% Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]], N=s(0)) + fails #"No hay el mismo numero de viviendas en los tres niveles.".
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #"No hay vivienda en el tercer nivel.".
% Dado un edificio con 1 nivel, se busca la primera vivienda de ese nivel.
:- test column(X,N,C) : (X=[[s(0)]], N=s(0)) => (C=[s(0)]) + not_fails.
% Dado un edificio con 1 nivel, se busca la tercera vivienda de ese nivel.
:- test column(X,N,C) : (X=[[s(0),0,s(0),s(s(s(s(0))))]], N=s(s(s(0)))) => (C=[s(0)]) + not_fails.
% Dado un edificio con 2 niveles, se buscan las primeras viviendas de todos sus niveles.
:- test column(X,N,C) : (X=[[0,s(0)],[0,s(s(0))]], N=s(0)) => (C=[0,0]) + not_fails.
% Dado un edificio con 5 niveles, se buscan las segundas viviendas de todos sus niveles.
:- test column(X,N,C) : (X=[[s(0),0,s(0)],[s(s(0)),s(0),s(s(0))],[s(0),s(0),0],[0,0,0],[s(0),0,s(0)]], N=s(s(0))) => (C=[0,s(0),s(0),0,0]) + not_fails.
% Dado un edificio con 4 niveles, se buscan las primeras viviendas de todos sus niveles.
:- test column(X,N,C) : (X=[[0,s(0)],[0,s(s(0))],[0,s(0)],[s(0),s(s(s(0)))]], N=s(0)) => (C=[0,0,0,s(0)]) + not_fails.
% Dado un edificio con 8 niveles, se buscan las primeras viviendas de todos sus niveles.
:- test column(X,N,C) : (X=[[s(s(0))],[s(0)],[0],[s(0)],[s(s(0))],[s(0)],[0],[s(0)]], N=s(0)) => (C=[s(s(0)),s(0),0,s(0),s(s(0)),s(0),0,s(0)]) + not_fails.
% Dado un edificio con 3 niveles, se buscan las segundas viviendas de todos sus niveles.
:- test column(X,N,C) : (X=[[s(0),0,s(0)],[s(s(0)),0,s(0)],[s(s(s(0))),s(0),s(s(0))]], N=s(s(0))) => (C=[0,0,s(0)]) + not_fails.
% Dado un edificio con 4 niveles, se buscan las segundas viviendas de todos sus niveles; pero la funcion devuelve las viviendas erroneas.
:- test column(X,N,C) : (X=[[0,s(0)],[s(0),s(0)],[0,0],[s(s(0)),s(0)]], N=s(s(0)), C=[0,s(0),0,s(s(0))]) + fails #"Viviendas devueltas incorrectas.".
% Dado un edificio con 3 niveles, se buscan las primeras viviendas de todos sus niveles; pero la funcion devuelve las viviendas erroneas.
:- test column(X,N,C) : (X=[[s(0),s(0)],[0,s(0)],[s(0),s(s(s(0)))]], N=s(0), C=[s(0),s(0),s(s(s(0)))]) + fails #"Viviendas devueltas incorrectas.".
% Dado un edificio con 2 niveles, se buscan las primeras viviendas de todos sus niveles; pero la funcion devuelve las viviendas erroneas.
:- test column(X,N,C) : (X=[[s(0),s(0),0],[0,s(0),s(s(0))]], N=s(0), C=[s(0),s(0)]) + fails #"Viviendas devueltas incorrectas.".
% Dado un edificio con 3 niveles, se buscan las terceras viviendas de todos sus niveles; pero no hay tres viviendas en cada nivel.
:- test column(X,N,C) : (X=[[s(0)],[s(s(0))],[s(0)]], N=s(s(s(0)))) + fails #"No hay tercera vivienda en cada nivel del edificio.".
% Dado un edificio con 3 niveles, se buscan las segundas viviendas de todos sus niveles; pero no hay dos viviendas en cada nivel.
:- test column(X,N,C) : (X=[[s(0)],[s(s(0))],[0]], N=s(s(0))) + fails #"No hay segunda vivienda en cada nivel del edificio.".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests columns(X,C)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test columns(X,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #"No hay el mismo numero de viviendas en los dos niveles.".
% Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test columns(X,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #"No hay el mismo numero de viviendas en los tres niveles.".
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test columns(X,C) : (X=[]) + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test columns(X,C) : (X=[[]]) + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test columns(X,C) : (X=[[],[]]) + fails  #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test columns(X,C) : (X=[[5]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test columns(X,C) : (X=[[hola]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test columns(X,C) : (X=[["hola"]]) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test columns(X,C) : (X=[[0],[]]) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test columns(X,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails #"No hay vivienda en el tercer nivel.".
% Dado un edificio con 1 nivel, se devuelve la columna del edificio.
:- test columns(X,C) : (X=[[s(0)]]) => (C=[[s(0)]]) + not_fails.
% Dado un edificio con 1 nivel, se devuelve las columnas del edificio.
:- test columns(X,C) : (X=[[s(0),0,s(s(s(0)))]]) => (C=[[s(0)],[0],[s(s(s(0)))]]) + not_fails.
% Dado un edificio con 2 niveles, se devuelve las columnas del edificio.
:- test columns(X,C) : (X=[[s(0)],[0]]) => (C=[[s(0),0]]) + not_fails.
% Dado un edificio con 3 niveles, se devuelve las columnas del edificio.
:- test columns(X,C) : (X=[[s(0),0],[0,s(0)],[s(0),s(0)]]) => (C=[[s(0),0,s(0)],[0,s(0),s(0)]]) + not_fails.
% Dado un edificio con 2 niveles, se devuelve las columnas del edificio.
:- test columns(X,C) : (X=[[s(0),0],[s(0),0]]) => (C=[[s(0),s(0)],[0,0]]) + not_fails.
% Dado un edificio con 3 niveles, se devuelve las columnas del edificio.
:- test columns(X,C) : (X=[[s(0)],[0],[s(0)]]) => (C=[[s(0),0,s(0)]]) + not_fails.
% Dado un edificio con 3 niveles, se devuelve las columnas del edificio.
:- test columns(X,C) : (X=[[s(s(0)),s(0),0],[s(0),0,s(0)],[s(s(s(0))),s(0),0]]) => (C=[[s(s(0)),s(0),s(s(s(0)))],[s(0),0,s(0)],[0,s(0),0]]) + not_fails.
% Dado un edificio con 5 niveles, se devuelven las columnas del edificio.
:- test columns(X,C) : (X=[[s(0)],[0],[s(0)],[0],[s(0)]]) => (C=[[s(0),0,s(0),0,s(0)]]) + not_fails.
% Dado un edificio con 3 niveles, se devuelve las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[s(0),0],[s(0),0],[s(0),0]], C=[[0,0,0],[s(0),s(0),s(0)]]) + fails #"Columnas devueltas incorrectas.".
% Dado un edificio con 1 nivel, se devuelve las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[s(0),0,s(s(0))]], C=[[s(0),0,s(s(0))]]) + fails #"Columnas devueltas incorrectas.".
% Dado un edificio con 2 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[s(0)],[0]], C=[[0,s(0)]]) + fails #"Columnas devueltas incorrectas.".
% Dado un edificio con 2 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[s(0),0],[s(0),s(0)]], C=[[s(0),s(0)],[s(0),0]]) + fails #"Columnas devueltas incorrectas.".
% Dado un edificio con 3 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[s(0)],[0],[s(0)]], C=[[0,s(0),s(0)]]) + fails #"Columnas devueltas incorrectas.".
% Dado un edificio con 3 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[0,s(0)],[s(s(0)),s(0)],[0,0]], C=[[0,s(0),0],[s(0),s(s(0)),0]]) + fails #"Columnas devueltas incorrectas.".
% Dado un edificio con 5 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.
:- test columns(X,C) : (X=[[s(0)],[0],[s(0)],[0],[s(0)]], C=[[s(0),s(0),s(0),0,0]]) + fails #"Columnas devueltas incorrectas.".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests total_people(X,T)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test total_people(X,T) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #"No hay el mismo numero de viviendas en los dos niveles".
% Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test total_people(X,T) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #"No hay el mismo numero de viviendas en los tres niveles".
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test total_people(X,T) : (X=[]) + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test total_people(X,T) : (X=[[]]) + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test total_people(X,T) : (X=[[],[]]) + fails #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test total_people(X,T) : (X=[[5]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test total_people(X,T) : (X=[[hola]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test total_people(X,T) : (X=[["hola"]]) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test total_people(X,T) : (X=[[0],[]]) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 2 niveles y 1 persona en el segundo nivel, se comprueba que solo hay 1 persona en el edificio.
:- test total_people(X,T) : (X=[[0],[s(0)]]) => (T=s(0)) + not_fails.
% Dado un edificio con 2 niveles y 1 persona en cada nivel, se comprueba que hay 2 personas en el edificio.
:- test total_people(X,T) : (X=[[0,s(0)],[s(0),0]]) => (T=s(s(0))) + not_fails.
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test total_people(X,T) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails #"No hay vivienda en el tercer nivel.".
% Dado un edificio con 3 niveles y 1 persona en cada nivel, se comprueba que hay 3 personas en el edificio.
:- test total_people(X,T) : (X=[[0,s(0)],[s(0),0],[s(0),0]]) => (T=s(s(s(0)))) + not_fails.
% Dado un edificio con 3 niveles y 1 persona en cada nivel, se comprueba que hay 3 personas en el edificio.
:- test total_people(X,T) : (X=[[0,s(0),0],[s(0),0,0],[s(0),0,0]]) => (T=s(s(s(0)))) + not_fails.
% Dado un edificio con 2 niveles y 1 persona en cada nivel, se comprueba que no hay 1 persona en el edificio.
:- test total_people(X,T) : (X=[[0,s(0)],[s(0),0]], T=s(0)) + fails #"Hay 2 personas en vez de 1.".
% Dado un edificio con 3 niveles y 1 persona en cada nivel, se comprueba que no hay 2 personas en el edificio.
:- test total_people(X,T) : (X=[[0,s(0),0],[s(0),0,0],[s(0),0,0]], T=s(s(0))) + fails #"Hay 3 personas en vez de 2.".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests average(X,A)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test average(X,A) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #"No hay el mismo numero de viviendas en los dos niveles.".
% Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.
:- test average(X,A) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #"No hay el mismo numero de viviendas en los tres niveles.".
% Se comprueba que da fallo cuando el edificio no tiene ningun nivel.
:- test average(X,A) : (X=[]) + fails #"El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.
:- test average(X,A) : (X=[[]]) + fails #"No hay viviendas en el nivel. Tiene que haber al menos una vivienda.".
% Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.
:- test average(X,A) : (X=[[],[]]) + fails #"No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test average(X,A) : (X=[[5]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test average(X,A) : (X=[[hola]]) + fails #"La vivienda no es un numero natural.".
% Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.
:- test average(X,A) : (X=[["hola"]]) + fails #"La vivienda no es un numero natural.".
% Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.
:- test average(X,A) : (X=[[0],[]]) + fails #"No hay vivienda en el segundo nivel.".
% Dado un edificio con 2 viviendas y 1 persona en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 0.
:- test average(X,A) : (X=[[0],[s(0)]]) => (A=0) + not_fails.
% Dado un edificio con 4 viviendas y 2 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 0.
:- test average(X,A) : (X=[[0,s(0)],[s(0),0]]) => (A=0) + not_fails.
% Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.
:- test average(X,A) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails #"No hay vivienda en el tercer nivel.".
% Dado un edificio con 6 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 1.
:- test average(X,A) : (X=[[0,s(s(s(s(0))))],[s(0),0],[s(0),0]]) => (A=s(0)) + not_fails.
% Dado un edificio con 3 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 2.
:- test average(X,A) : (X=[[s(s(s(0))),s(0),s(s(0))]]) => (A=s(s(0))) + not_fails.
% Dado un edificio con 6 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano no da 0.
:- test average(X,A) : (X=[[0,s(s(s(s(0))))],[s(0),0],[s(0),0]],A=0) + fails #"El resultado es 1 en vez de 0.".
% Dado un edificio con 3 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano no da 1.
:- test average(X,A) : (X=[[s(s(s(0))),s(0),s(s(0))]], A=s(0)) + fails #"El resultado es 2 en vez de 1.".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Documentacion
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- doc(title, "EDIFICIOS DE VIVIENDAS").
:- doc(author, "Jose Manuel Diaz Urraco 170085").
:- doc(author, "Eva Tagarro Lopez de Ayala 170183").
:- doc(author, "Guisell Eliana Mori De La Cruz 160065").

:- doc(module, "Este documento sustituye a la memoria final de la práctica. Debido a la instalación de la nueva versión de ciao (1.19.0), no podemos generar el documento pdf a partir de este html. Por lo que entregamos el html directamente como se propuso en una clase en caso de que ocurriera este error.

 Esta practica consiste en manipular edificios de viviendas como si se tratara de matrices donde cada fila representa a un nivel y cada columna representa a una vivienda.

Como se especifica en el enunciado, los valores almacenados representan el numero de personas que viven en cada vivienda.

De tal manera que estos valores tienen que ser de la forma:
@includedef{natural/1}

A continuacion, expondremos el codigo utilizado para resolver las tareas planteadas junto con las consultas realizadas para probar su correcto funcionamiento.


@section{Codigo utilizado, explicacion y justificacion de las decisiones}
@subsection{basic_building(X)}
@begin{verbatim}
:- pred basic_building(X)

Verifica que @var{X} es un edificio, que contiene numeros naturales y que debe tener al menos un nivel y cada nivel al menos una vivienda. @includedef{basic_building/1}
@end{verbatim}

@subsection{Explicacion basic_building(X)}
@begin{verbatim}
El predicado basic_building(@var{X}) comprueba recursivamente, recorriendo el edificio pasado como parametro, elemento por elemento que dicho edificio tenga como minimo un nivel con una vivienda y que todas las viviendas esten representadas con numeros naturales.Como caso base hemos usado [@var{X}] para que siempre tenga que haber al menos un elemento. Y si se pasa un edificio vacio de error.
@end{verbatim}

@subsection{Predicados auxiliares basic_building(X)}
@begin{verbatim}
:- pred pisoValido(L)

Verifica si @var{L} es una lista de numeros naturales. @includedef{pisoValido/1}

:- prop natural(X)

Verifica si @var{X} es un numero natural. @includedef{natural/1}
@end{verbatim}

@subsection{building(X)}
@begin{verbatim}
:- pred building(X)

Verifica que @var{X} es un edificio como el anterior pero ademas todos los niveles deben tener el mismo numero de viviendas. @includedef{building/1}
@end{verbatim}

@subsection{Explicacion building(X)}
@begin{verbatim}
El predicado building(@var{X}) comprueba que el edificio @var{X} pasado como parametro sea un basic building y que todos los niveles tengan el mismo numero de viviendas. Para comprobar esta ultima condicion, se crea una nueva lista en la que metemos el numero de viviendas por cada piso. Y, con la lista terminada, comprobamos que todos sus elementos sean iguales. Como caso base usa el del predicado building. Ya que asi aseguramos que haya al menos un elemento en el edificio.
@end{verbatim}

@subsection{Predicados auxiliares building(X)}
@begin{verbatim}
:- pred pisoValido2(L1,L2)

Comprueba que en @var{L2} esta el numero correcto de las casas de cada piso (tamaño de cada sublista). @includedef{pisoValido2/2}

:- pred tamanoLista(Y,N)

Comprueba que el edificio @var{Y} tenga @var{N} pisos (que la lista @var{Y} tenga @var{N} elementos). @includedef{tamanoLista/2}

:- pred concatenar(L1,L2,L3)

Comprueba que @var{L3} es la concatenacion de la lista @var{L1} con la lista @var{L2}. @includedef{concatenar/3}

:- pred todosIguales(X)

Comprueba que en la lista @var{X} tenga todos sus elementos iguales. @includedef{todosIguales/1}
@end{verbatim}

@subsection{level(X,N,C)}
@begin{verbatim}
:- pred level(X,N,C)

Verifica que @var{C} es el nivel @var{N} del edificio @var{X} (la lista con todas las viviendas de ese nivel). @includedef{level/3}
@end{verbatim}

@subsection{Explicacion level(X,N,C)}
@begin{verbatim}
El predicado level(@var{X},@var{N},@var{C}) comprueba que el edificio @var{X} pasado como parametro sea un basic building y despues va recorriendo el edificio piso por piso hasta el piso numero @var{N} que queremos. Se realiza con el uso de un contador al que se le va restando una unidad por cada piso que recorre hasta llegar al deseado (que sera cuando el contador tenga un s(0) en el caso base). Como casos base usa el del predicado basic_building (que es el de building), asegurando que haya al menos un elemento en el edificio. Y ademas, el levelAux el decremento del contador hasta s(0) como hemos comentado anteriormente.
@end{verbatim}

@subsection{Predicados auxiliares level(X,N,C)}
@begin{verbatim}
:- pred levelAux(X,N,C)

Predicado auxiliar de level. Se hace cierto en los mismos casos que level pero ademas tambien cuando no se cumple la condicion building, que se comprueba previamente en el propio predicado level(@var{X},@var{N},@var{C}). @includedef{levelAux/3}
@end{verbatim}

@subsection{column(X,N,C)}
@begin{verbatim}
:- pred column(X,N,C)

Verifica que @var{C} es la lista formada por las viviendas de @var{N} de todos los niveles del edificio @var{X}. @includedef{column/3}
@end{verbatim}

@subsection{Explicacion column(X,N,C)}
@begin{verbatim}
El predicado column(@var{X},@var{N},@var{C}) comprueba que el edificio @var{X} pasado como parametro sea un basic building y despues va a comprobar que @var{C} es la lista de las viviendas N-esimas de todos los niveles de @var{X}. Para ello, mediante el uso de funciones auxiliares, vamos borrando las primeras columnas de la matriz hasta que la primera columna sea la que queremos. Una vez ahi, sacamos la primera columna de la matriz (con otra funcion auxiliar) para asi devolverla como parametro.Como caso base usa el del predicado building. Y en las funciones auxiliares el uso de un contador hasta s(0) y de listas vacias para que se puedan ir construyendo las nuevas matrices.
@end{verbatim}

@subsection{Predicados auxiliares column(X,N,C)}
@begin{verbatim}
:- pred borrarNPrimerosElementos(X,N,Y)

Verifica que @var{Y} sea una submatriz del edificio @var{X} cuya columna numero @var{N} sea la primera. @includedef{borrarNPrimerosElementos/3}

:- pred borrarPrimerElemento(X,Y)

Verifica que @var{Y} es el edificio resultante de borrar la primera columna del edificio @var{X} (se borra la vivienda 1 de cada piso, que es el primer elemento de cada sublista). @includedef{borrarPrimerElemento/2}

:- pred sacarPrimeraColumnaEdificio(X,C)

Verifica que @var{C} sea la primera columna (viviendas 1 de cada piso) del edificio @var{X}. @includedef{sacarPrimeraColumnaEdificio/2}
@end{verbatim}

@subsection{columns(X,C)}
@begin{verbatim}
:- pred columns(X,C)

Verifica que @var{C} sea la lista de las columnas de viviendas del edificio @var{X}. O lo que es igual, verificar que @var{C} sea la matriz traspuesta del edificio @var{X}. @includedef{columns/2}
@end{verbatim}

@subsection{Explicacion columns(X,C)}
@begin{verbatim}
El predicado columns(@var{X},@var{C}) comprueba que el edificio @var{X} pasado como parametro sea un basic building y despues va a comprobar que @var{C} sea la matriz traspuesta de @var{X}. Para realizar la trasposicion se llama a la funcion columnsAux que lo que hace, mediante las funciones auxiliares usadas en el predicado column, es borrar la primera columna de la matriz (viviendas 1 de todos los pisos), esa columna nos la guardamos para que se añada a la nueva matriz traspuesta como fila y se vuelve a llamar recursivamente a columnsAux con la matriz resultante de borrar la primera columna.Como caso base usa el del predicado building. Y en columnsAux listas vacias para que se puedan ir construyendo las nuevas matrices.
@end{verbatim}

@subsection{Predicados auxiliares columns(X,C)}
@begin{verbatim}
:- pred columnsAux(X,C)

Predicado auxiliar de columns. Se hace cierto en los mismos casos que columns pero ademas tambien cuando no se cumple la condicion building, que se comprueba previamente en el propio predicado columns(@var{X},@var{C}). Variables columnsAux: [@var{X}: edificio original], [@var{Y}: edificio sin primera columna], [@var{C}: primera columna del edificio (primera fila matriz traspuesta)], [Cs: resto de la matriz traspuesta] .@includedef{columnsAux/2}
@end{verbatim}

@subsection{total_people(X,T)}
@begin{verbatim}
:- pred total_people(X,T)

Verifica que @var{T} sea el numero total de personas que viven en el edificio @var{X}. @includedef{total_people/2}
@end{verbatim}

@subsection{Explicacion total_people(X,T)}
@begin{verbatim}
El predicado total_people(@var{X},@var{T}) comprueba que el edificio @var{X} pasado como parametro sea un basic building y que @var{T} sea el numero total de personas de @var{X}. Para esto ultimo vamos recorriendo el edificio @var{X} vivienda por vivienda y nos guardamos en una lista auxiliar el numero de personas de cada vivienda. Una vez recorrido todo el edificio, sumamos tosos los elementos de la lista auxiliar y nos devuelve el numero total de personas que viven en el edificio. Como caso base usa el del predicado building. Y en las funciones auxiliares listas vacias para que se puedan ir construyendo las nuevas matrices y listas.
@end{verbatim}

@subsection{Predicaos auxiliares total_people(X,T)}
@begin{verbatim}
:- pred concatenar_matriz(X,R)

Verifica que @var{R} sea una lista con todos los elementos del edificio @var{X}. @includedef{concatenar_matriz/2}

:- pred suma_elementos_lista(X,N)

Verifica que @var{N} sea la suma de todos los elementos de la lista @var{X}. @includedef{suma_elementos_lista/2}

:- pred suma(X,Y,Z)

Devuelve cierto si y solo si @var{Z} es la suma de @var{X} y @var{Y}. @includedef{suma/3}
@end{verbatim}

@subsection{average(X,A)}
@begin{verbatim}
:- pred average(X,A)

Verifica que @var{A} sea la media de personas que viven en cada vivienda del edificio @var{X} truncada al numero natural entero. @includedef{average/2}
@end{verbatim}

@subsection{Explicacion average(X,A)}
@begin{verbatim}
El predicado average(@var{X},@var{A}) comprueba que el edificio @var{X} pasado como parametro sea un basic building (mediante la llamada a total_people) y que @var{A} sea la media de personas que viven en cada vivienda del edificio truncada al numero natural entero. Para ello el algoritmo usado es realizar la division de todas las personas que viven en el edificio (obtenidas mediante una llamada a total_people) entre el numero de viviendas (obtenido mediante una funcion auxiliar que guarda el numero de personas de cada vivienda en una lista auxiliar, y al final  obtiene el numero de elementos de dicha lista mediante la llamada a la funcion auxiliar definida previamente tamanoLista). Para realizar la division, al numero total de personas T se le resta el numero de viviendas N del edificio y en un contador se aumenta en 1 unidad. Se vuelve a llamar al predicado division pero con T-N personas comprobando que T-N sea siempre mayor que N (para obetenr el numero natural entero truncado). Como caso base usa el del predicado building. Y en la funcion auxiliar division llegar al punto en el que T sea menor que V, que sera el momento en el que habra que parar las restas sucesivas.
@end{verbatim}

@subsection{Predicados auxiliares average(X,A)}
@begin{verbatim}
:- pred numero_viviendas_totales(X,T)

Verifica que @var{T} sea el numero de viviendas totales del edificio @var{X}. @includedef{numero_viviendas_totales/2}

:- pred division(T,V,S)

Verifica que se cumpla la operacion @var{T}/@var{V}=@var{S} (division entera con truncamiento). @includedef{division/3}

:- pred menor_que(X,Y)

Comprueba que @var{X} sea menor que @var{Y}. @includedef{menor_que/2}

:- pred resta(X,Y,Z)

Devuelve cierto si y solo si @var{Z} es la resta de @var{X} menos @var{Y}, siendo @var{X} mayor que @var{Y} (resta de naturales). @includedef{resta/3}
@end{verbatim}

@section{Consultas realizadas}
@subsection{basic_building(X)}
@begin{verbatim}
Dado un edificio con 1 nivel, se verifica que no esta vacio.

:- test basic_building(X) : (X=[[0]]) + not_fails.

Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.

:- test basic_building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + not_fails.

Dado un edificio con 3 niveles, se verifica que ninguno de los 3 niveles esta vacio.

:- test basic_building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + not_fails.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test basic_building(X) : (X=[]) + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test basic_building(X) : (X=[[]]) + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test basic_building(X) : (X=[[],[]]) + fails  #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test basic_building(X) : (X=[[5]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test basic_building(X) : (X=[[hola]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test basic_building(X) : (X=[[''hola'']]) + fails #''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test basic_building(X) : (X=[[0],[]]) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.

:- test basic_building(X) : (X=[[0],[s(0)]]) + not_fails.

Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.

:- test basic_building(X) : (X=[[0,s(0)],[s(0)]]) + not_fails.

Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test basic_building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails  #''No hay vivienda en el tercer nivel.''.
@end{verbatim}

@subsection{building(X)}
@begin{verbatim}
Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #''No hay el mismo numero de viviendas en los dos niveles.''.

Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #''No hay el mismo numero de viviendas en los tres niveles.''.

Dado un edificio con 1 nivel, se verifica que no esta vacio.

:- test building(X) : (X=[[0]]) + not_fails.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test building(X) : (X=[]) + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test building(X) : (X=[[]]) + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test building(X) : (X=[[],[]]) + fails  #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test building(X) : (X=[[5]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test building(X) : (X=[[hola]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test building(X) : (X=[[''hola'']]) + fails #''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test building(X) : (X=[[0],[]]) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.

:- test building(X) : (X=[[0],[s(0)]]) + not_fails.

Dado un edificio con 2 niveles, se verifica que ninguno de los 2 niveles esta vacio.

:- test building(X) : (X=[[0,s(0)],[s(0),0]]) + not_fails.

Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test building(X) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails  #''No hay vivienda en el tercer nivel.''.

Dado un edificio con 3 niveles, se verifica que cada nivel tiene 2 viviendas.

:- test building(X) : (X=[[0,s(0)],[s(0),0],[s((0)),0]]) + not_fails.

Dado un edificio con 3 niveles, se verifica que cada nivel tiene 3 viviendas.

:- test building(X) : (X=[[0,s(0),0],[s(0),0,0],[s(0),0,0]]) + not_fails.
@end{verbatim}

@subsection{level(X,N,C)}
@begin{verbatim}
Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #''No hay vivienda en el tercer nivel.''.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test level(X,N,C) : (X=[], N=s(0))  + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test level(X,N,C) : (X=[[]], N=s(0))  + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test level(X,N,C) : (X=[[],[]], N=s(0)) + fails  #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test level(X,N,C) : (X=[[5]], N=s(0)) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test level(X,N,C) : (X=[[hola]], N=s(0)) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test level(X,N,C) : (X=[[''hola'']], N=s(0)) + fails ''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test level(X,N,C) : (X=[[0],[]], N=s(0)) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]], N=s(0)) + fails #''No hay el mismo numero de viviendas en los dos niveles.''.

Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]], N=s(0)) + fails #''No hay el mismo numero de viviendas en los tres niveles.''.
Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test level(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #''No hay vivienda en el tercer nivel.''.

Dado un edificio con 2 niveles, se buscan las viviendas del nivel 2.

:- test level(X,N,C) : (X=[[0,s(0)],[s(0),s(0)]], N=s(s(0))) => (C=[s(0),s(0)]) + not_fails.

Dado un edificio con 3 niveles, se buscan las viviendas del nivel 1.

:- test level(X,N,C) : (X=[[0,s(0),0,s(s(s(0)))],[s(0),s(0),0,s(s(s(s(0))))],[s(0),0,0,s(s(0))]], N=s(0)) => (C=[0,s(0),0,s(s(s(0)))]) + not_fails.

Dado un edificio con 3 niveles, se buscan las viviendas del nivel 3.

:- test level(X,N,C) : (X=[[s(0)],[0],[s(s(0))]], N=s(s(s(0)))) => (C=[s(s(0))]) + not_fails.

Dado un edificio con 6 niveles, se buscan las viviendas del nivel 4.

:- test level(X,N,C) : (X=[[s(s(s(0)))],[s(s(s(s(0))))],[s(0)],[s(0)],[0],[s(0)]], N=s(s(s(s(0))))) => (C=[s(0)]) + not_fails.

Dado un edificio con 3 niveles, se busca en que nivel estan las viviendas especificadas.

:- test level(X,N,C) : (X=[[s(0),s(0),0],[s(0),s(0),s(0)],[0,0,s(0)]], C=[0,0,s(0)]) => (N=s(s(s(0)))) + not_fails.

Dado un edificio con 2 niveles, se busca en que nivel estan las viviendas especificadas.

:- test level(X,N,C) : (X=[[s(0),s(s(0)),s(s(s(0)))],[0,0,s(s(0))]], C=[0,0,s(s(0))]) => (N=s(s(0))) + not_fails.

Dado un edificio con 4 niveles, se buscan las viviendas del nivel 4; pero la funcion devuelve las de un nivel incorrecto.

:- test level(X,N,C) : (X=[[0,s(0)],[s(0),s(0)],[0,0],[s(0),0]], N=s(s(s(s(0)))), C=[s(0),s(0)]) + fails #''Lista de viviendas del nivel incorrecto.''.

Dado un edificio con 3 niveles, se buscan las viviendas del nivel 2; pero la funcion devuelve las de un nivel incorrecto.

:- test level(X,N,C) : (X=[[0,s(0)],[s(0),s(0)],[0,0]], N=s(s(0)), C=[0,0]) + fails #''Lista de viviendas del nivel incorrecto.''.

Dado un edificio con 2 niveles, se buscan las viviendas del nivel 1; pero la funcion devuelve las de un nivel incorrecto.

:- test level(X,N,C) : (X=[[0,s(s(s(0)))],[s(s(0)),s(s(s(0)))]], N=s(0), C=[s(s(0)),s(s(s(0)))]) + fails #''Lista de viviendas del nivel incorrecto.''.

Dado un edificio con 3 niveles, se buscan las viviendas del nivel 3; pero la funcion devuelve las de un nivel incorrecto.

:- test level(X,N,C) : (X=[[s(0)],[s(s(s(0)))],[0]], N=s(s(s(0))), C=[s(0)]) + fails #''Lista de viviendas del nivel incorrecto.''.

Dado un edificio con 3 niveles, se buscan las viviendas del nivel 5; pero el edificio no tiene tantos niveles.

:- test level(X,N,C) : (X=[[0,0],[s(0),s(0)],[s(0),0]], N=s(s(s(s(s(0)))))) + fails #''El edificio no tiene ese numero de niveles.''.

Dado un edificio con 3 niveles, se busca en que nivel estan las viviendas especificadas; pero la funcion devuelve un numero de nivel incorrecto.

:- test level(X,N,C) : (X=[[s(0),s(0),0],[s(0),s(0),s(0)],[0,0,s(0)]], N=s(0), C=[0,0,s(0)]) + fails #''Nivel devuelto incorrecto.''.

Dado un edificio con 4 niveles, se busca en que nivel estan las viviendas especificadas; pero la funcion devuelve un numero de nivel incorrecto.

:- test level(X,N,C) : (X=[[0],[s(0)],[s(0)],[s(s(0))]], N=s(s(0)), C=[0]) + fails #''Nivel devuelto incorrecto.''.
@end{verbatim}

@subsection{column(X,N,C)}
@begin{verbatim}
Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #''No hay vivienda en el tercer nivel.''.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test column(X,N,C) : (X=[], N=s(0)) + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test column(X,N,C) : (X=[[]], N=s(0)) + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test column(X,N,C) : (X=[[],[]], N=s(0)) + fails  #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test column(X,N,C) : (X=[[5]], N=s(0)) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test column(X,N,C) : (X=[[hola]], N=s(0)) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test column(X,N,C) : (X=[[''hola'']], N=s(0)) + fails #''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test column(X,N,C) : (X=[[0],[]], N=s(0)) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]], N=s(0)) + fails #''No hay el mismo numero de viviendas en los dos niveles.''.

Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]], N=s(0)) + fails #''No hay el mismo numero de viviendas en los tres niveles.''.

Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test column(X,N,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]], N=s(0)) + fails  #''No hay vivienda en el tercer nivel.''.

Dado un edificio con 1 nivel, se busca la primera vivienda de ese nivel.

:- test column(X,N,C) : (X=[[s(0)]], N=s(0)) => (C=[s(0)]) + not_fails.

Dado un edificio con 1 nivel, se busca la tercera vivienda de ese nivel.

:- test column(X,N,C) : (X=[[s(0),0,s(0),s(s(s(s(0))))]], N=s(s(s(0)))) => (C=[s(0)]) + not_fails.

Dado un edificio con 2 niveles, se buscan las primeras viviendas de todos sus niveles.

:- test column(X,N,C) : (X=[[0,s(0)],[0,s(s(0))]], N=s(0)) => (C=[0,0]) + not_fails.

Dado un edificio con 5 niveles, se buscan las segundas viviendas de todos sus niveles.

:- test column(X,N,C) : (X=[[s(0),0,s(0)],[s(s(0)),s(0),s(s(0))],[s(0),s(0),0],[0,0,0],[s(0),0,s(0)]], N=s(s(0))) => (C=[0,s(0),s(0),0,0]) +
 not_fails.

Dado un edificio con 4 niveles, se buscan las primeras viviendas de todos sus niveles.

:- test column(X,N,C) : (X=[[0,s(0)],[0,s(s(0))],[0,s(0)],[s(0),s(s(s(0)))]], N=s(0)) => (C=[0,0,0,s(0)]) + not_fails.

Dado un edificio con 8 niveles, se buscan las primeras viviendas de todos sus niveles.

:- test column(X,N,C) : (X=[[s(s(0))],[s(0)],[0],[s(0)],[s(s(0))],[s(0)],[0],[s(0)]], N=s(0)) => (C=[s(s(0)),s(0),0,s(0),s(s(0)),s(0),0,s(0)

]) + not_fails.

Dado un edificio con 3 niveles, se buscan las segundas viviendas de todos sus niveles.

:- test column(X,N,C) : (X=[[s(0),0,s(0)],[s(s(0)),0,s(0)],[s(s(s(0))),s(0),s(s(0))]], N=s(s(0))) => (C=[0,0,s(0)]) + not_fails.

Dado un edificio con 4 niveles, se buscan las segundas viviendas de todos sus niveles; pero la funcion devuelve las viviendas erroneas.

:- test column(X,N,C) : (X=[[0,s(0)],[s(0),s(0)],[0,0],[s(s(0)),s(0)]], N=s(s(0)), C=[0,s(0),0,s(s(0))]) + fails #''Viviendas devueltas incor

rectas.''.

Dado un edificio con 3 niveles, se buscan las primeras viviendas de todos sus niveles; pero la funcion devuelve las viviendas erroneas.

:- test column(X,N,C) : (X=[[s(0),s(0)],[0,s(0)],[s(0),s(s(s(0)))]], N=s(0), C=[s(0),s(0),s(s(s(0)))]) + fails #''Viviendas devueltas incorrectas.''.

Dado un edificio con 2 niveles, se buscan las primeras viviendas de todos sus niveles; pero la funcion devuelve las viviendas erroneas.

:- test column(X,N,C) : (X=[[s(0),s(0),0],[0,s(0),s(s(0))]], N=s(0), C=[s(0),s(0)]) + fails #''Viviendas devueltas incorrectas.''.

Dado un edificio con 3 niveles, se buscan las terceras viviendas de todos sus niveles; pero no hay tres viviendas en cada nivel.

:- test column(X,N,C) : (X=[[s(0)],[s(s(0))],[s(0)]], N=s(s(s(0)))) + fails #''No hay tercera vivienda en cada nivel del edificio.''.

Dado un edificio con 3 niveles, se buscan las segundas viviendas de todos sus niveles; pero no hay dos viviendas en cada nivel.

:- test column(X,N,C) : (X=[[s(0)],[s(s(0))],[0]], N=s(s(0))) + fails #''No hay segunda vivienda en cada nivel del edificio.''.
@end{verbatim}

@subsection{columns(X,C)}
@begin{verbatim}
Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test columns(X,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #''No hay el mismo numero de viviendas en los dos niveles.''.

Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test columns(X,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #''No hay el mismo numero de viviendas en los tres niveles.''.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test columns(X,C) : (X=[]) + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test columns(X,C) : (X=[[]]) + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test columns(X,C) : (X=[[],[]]) + fails  #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test columns(X,C) : (X=[[5]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test columns(X,C) : (X=[[hola]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test columns(X,C) : (X=[[''hola'']]) + fails #''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test columns(X,C) : (X=[[0],[]]) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test columns(X,C) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails #''No hay vivienda en el tercer nivel.''.

Dado un edificio con 1 nivel, se devuelve la columna del edificio.

:- test columns(X,C) : (X=[[s(0)]]) => (C=[[s(0)]]) + not_fails.

Dado un edificio con 1 nivel, se devuelve las columnas del edificio.

:- test columns(X,C) : (X=[[s(0),0,s(s(s(0)))]]) => (C=[[s(0)],[0],[s(s(s(0)))]]) + not_fails.

Dado un edificio con 2 niveles, se devuelve las columnas del edificio.

:- test columns(X,C) : (X=[[s(0)],[0]]) => (C=[[s(0),0]]) + not_fails.

Dado un edificio con 3 niveles, se devuelve las columnas del edificio.

:- test columns(X,C) : (X=[[s(0),0],[0,s(0)],[s(0),s(0)]]) => (C=[[s(0),0,s(0)],[0,s(0),s(0)]]) + not_fails.

Dado un edificio con 2 niveles, se devuelve las columnas del edificio.

:- test columns(X,C) : (X=[[s(0),0],[s(0),0]]) => (C=[[s(0),s(0)],[0,0]]) + not_fails.

Dado un edificio con 3 niveles, se devuelve las columnas del edificio.

:- test columns(X,C) : (X=[[s(0)],[0],[s(0)]]) => (C=[[s(0),0,s(0)]]) + not_fails.

Dado un edificio con 3 niveles, se devuelve las columnas del edificio.

:- test columns(X,C) : (X=[[s(s(0)),s(0),0],[s(0),0,s(0)],[s(s(s(0))),s(0),0]]) => (C=[[s(s(0)),s(0),s(s(s(0)))],[s(0),0,s(0)],[0,s(0),0]]) + not_fails.

Dado un edificio con 5 niveles, se devuelven las columnas del edificio.

:- test columns(X,C) : (X=[[s(0)],[0],[s(0)],[0],[s(0)]]) => (C=[[s(0),0,s(0),0,s(0)]]) + not_fails.

Dado un edificio con 3 niveles, se devuelve las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[s(0),0],[s(0),0],[s(0),0]], C=[[0,0,0],[s(0),s(0),s(0)]]) + fails #''Columnas devueltas incorrectas.''.

Dado un edificio con 1 nivel, se devuelve las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[s(0),0,s(s(0))]], C=[[s(0),0,s(s(0))]]) + fails #''Columnas devueltas incorrectas.''.

Dado un edificio con 2 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[s(0)],[0]], C=[[0,s(0)]]) + fails #''Columnas devueltas incorrectas.''.

Dado un edificio con 2 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[s(0),0],[s(0),s(0)]], C=[[s(0),s(0)],[s(0),0]]) + fails #''Columnas devueltas incorrectas.''.

Dado un edificio con 3 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[s(0)],[0],[s(0)]], C=[[0,s(0),s(0)]]) + fails #''Columnas devueltas incorrectas.''.

Dado un edificio con 3 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[0,s(0)],[s(s(0)),s(0)],[0,0]], C=[[0,s(0),0],[s(0),s(s(0)),0]]) + fails #''Columnas devueltas incorrectas.''.

Dado un edificio con 5 niveles, se devuelven las columnas del edificio; pero la funcion no devuelve las columnas correctas.

:- test columns(X,C) : (X=[[s(0)],[0],[s(0)],[0],[s(0)]], C=[[s(0),s(0),s(0),0,0]]) + fails #''Columnas devueltas incorrectas.''.
@end{verbatim}

@subsection{total_people(X,T)}
@begin{verbatim}
Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test total_people(X,T) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #''No hay el mismo numero de viviendas en los dos niveles''.

Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test total_people(X,T) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #''No hay el mismo numero de viviendas en los tres niveles''.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test total_people(X,T) : (X=[]) + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test total_people(X,T) : (X=[[]]) + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test total_people(X,T) : (X=[[],[]]) + fails #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test total_people(X,T) : (X=[[5]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test total_people(X,T) : (X=[[hola]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test total_people(X,T) : (X=[['hola']]) + fails #''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test total_people(X,T) : (X=[[0],[]]) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 2 niveles y 1 persona en el segundo nivel, se comprueba que solo hay 1 persona en el edificio.

:- test total_people(X,T) : (X=[[0],[s(0)]]) => (T=s(0)) + not_fails.

Dado un edificio con 2 niveles y 1 persona en cada nivel, se comprueba que hay 2 personas en el edificio.

:- test total_people(X,T) : (X=[[0,s(0)],[s(0),0]]) => (T=s(s(0))) + not_fails.

Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test total_people(X,T) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails #''No hay vivienda en el tercer nivel.''.

Dado un edificio con 3 niveles y 1 persona en cada nivel, se comprueba que hay 3 personas en el edificio.

:- test total_people(X,T) : (X=[[0,s(0)],[s(0),0],[s(0),0]]) => (T=s(s(s(0)))) + not_fails.

Dado un edificio con 3 niveles y 1 persona en cada nivel, se comprueba que hay 3 personas en el edificio.

:- test total_people(X,T) : (X=[[0,s(0),0],[s(0),0,0],[s(0),0,0]]) => (T=s(s(s(0)))) + not_fails.

Dado un edificio con 2 niveles y 1 persona en cada nivel, se comprueba que no hay 1 persona en el edificio.

:- test total_people(X,T) : (X=[[0,s(0)],[s(0),0]], T=s(0)) + fails #''Hay 2 personas en vez de 1.''.

Dado un edificio con 3 niveles y 1 persona en cada nivel, se comprueba que no hay 2 personas en el edificio.

:- test total_people(X,T) : (X=[[0,s(0),0],[s(0),0,0],[s(0),0,0]], T=s(s(0))) + fails #''Hay 3 personas en vez de 2.''.
@end{verbatim}

@subsection{average(X,A)}
@begin{verbatim}

Dado un edificio con 2 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test average(X,A) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)]]) + fails #''No hay el mismo numero de viviendas en los dos niveles.''.

Dado un edificio con 3 niveles, se verifica que no tienen el mismo numero de viviendas.

:- test average(X,A) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[0]]) + fails #''No hay el mismo numero de viviendas en los tres niveles.''.

Se comprueba que da fallo cuando el edificio no tiene ningun nivel.

:- test average(X,A) : (X=[]) + fails #''El edificio esta vacio. Tiene que tener al menos un nivel y un nivel cada vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 1 nivel vacio.

:- test average(X,A) : (X=[[]]) + fails #''No hay viviendas en el nivel. Tiene que haber al menos una vivienda.''.

Se comprueba que da fallo cuando el edificio tiene 2 niveles vacios.

:- test average(X,A) : (X=[[],[]]) + fails #''No hay viviendas en los niveles. Tiene que haber al menos una vivienda en cada nivel.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test average(X,A) : (X=[[5]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test average(X,A) : (X=[[hola]]) + fails #''La vivienda no es un numero natural.''.

Se comprueba que da fallo cuando se introducen caracteres que no son numeros naturales.

:- test average(X,A) : (X=[['hola']]) + fails #''La vivienda no es un numero natural.''.

Dado un edificio con 2 niveles, se comprueba que da fallo cuando el segundo nivel esta vacio.

:- test average(X,A) : (X=[[0],[]]) + fails #''No hay vivienda en el segundo nivel.''.

Dado un edificio con 2 viviendas y 1 persona en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 0.

:- test average(X,A) : (X=[[0],[s(0)]]) => (A=0) + not_fails.

Dado un edificio con 4 viviendas y 2 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 0.

:- test average(X,A) : (X=[[0,s(0)],[s(0),0]]) => (A=0) + not_fails.

Dado un edificio con 3 niveles, se comprueba que da fallo cuando el tercer nivel esta vacio.

:- test average(X,A) : (X=[[0,s(0),s(s(s(0)))],[s(0),s(0)],[]]) + fails #''No hay vivienda en el tercer nivel.''.

Dado un edificio con 6 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 1.

:- test average(X,A) : (X=[[0,s(s(s(s(0))))],[s(0),0],[s(0),0]]) => (A=s(0)) + not_fails.

Dado un edificio con 3 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano da 2.

:- test average(X,A) : (X=[[s(s(s(0))),s(0),s(s(0))]]) => (A=s(s(0))) + not_fails.

Dado un edificio con 6 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano no da 0.

:- test average(X,A) : (X=[[0,s(s(s(s(0))))],[s(0),0],[s(0),0]],A=0) + fails #''El resultado es 1 en vez de 0.''.

Dado un edificio con 3 viviendas y 6 personas en el edificio, se comprueba que la media redondeada al numero natural mas cercano no da 1.

:- test average(X,A) : (X=[[s(s(s(0))),s(0),s(s(0))]], A=s(0)) + fails #''El resultado es 2 en vez de 1.''.

@end{verbatim}

 "). %%NO ELIMINAR ESTO, CIERRA AL DOC MODULE
