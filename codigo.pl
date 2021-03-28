:- module(_, _, [assertions]).
:- use_module(library(iso_misc)).
:- use_module(library(lists)).

alumno_prode('Diaz','Urraco','Jose Manuel','Z170085').
alumno_prode('Mori','De La Cruz','Guisell Eliana','Y160065').
alumno_prode('Tagarro','Lopez de Ayala','Eva','Z170183').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) es cierto si RegistrosSinComodines/n es una estructura de tipo reg/n, que resulta de sustituir los comodines que aparecen en el argumento Registros/n (tambien una estructura de tipo reg/n) por variables. ListaSimbolos es una lista que contiene todos los simbolos utilizados en el termino Registros/n en el mismo orden en los que estos aparecen en los registros, permitiendose que haya simbolos repetidos.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) es cierto si se cumplen las condiciones mencionadas anteriormente. Para ello, se ha seguido el siguiente procedimiento:
% 1) Se comprueba que Registros sea una estructura (termino compuesto), que tenga como functor regs y con aridad 2 o mayor.
% 2) Se crea una lista L1 que contiene unicamente el contenido de los registros.
% 3) Se construye la lista ListaSimbolos a partir de L1 pero sin añadir los *.
% 4) Se crea una lista L2 que contiene como cabeza de la lista el functor y como resto de la lista el contenido de los registros.
% 5) Se crea una lista L3 que es quivalente a L2 pero cuando L2 tiene un *, a L3 se le mete _ (variable anonima).
% 6) Se construye RegistrosSinComodines a partir de la lista L3.
% 7) Se comprueba que RegistrosSinComodines sea la estructura equivalente a Registros pero con _ en vez de * en los registros.

:- pred eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos)
#"Devuelve cierto si @var{RegistrosSinComodines/n} es una estructura de tipo reg/n, que resulta de sustituir los comodines que aparecen en el argumento @var{Registros/n} (tambien una estructura de tipo reg/n) por variables. @var{ListaSimbolos} es una lista que contiene todos los simbolos utilizados en el termino @var{Registros/n} en el mismo orden en los que estos aparecen en los registros, permitiendose que haya simbolos repetidos. @includedef{eliminar_comodines/3}".
eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos):- es_regs(Registros), crear_lista_regs_sin_functor(Registros,L1), eliminarComodinesListaSimbolos(L1,ListaSimbolos), crear_lista_regs(Registros,L2), listaRegistrosSinComodines(L2,L3), RegistrosSinComodines=..L3, comprobarRegistrosSinComodines(L2,L3).

% es_regs(R) es cierto si R es un termino compuesto, tiene como functor regs y tiene aridad 2 o mayor.
:- pred es_regs(R)
#"Devuelve cierto si @var{R} es un termino compuesto, tiene como functor regs y tiene aridad 2 o mayor. @includedef{es_regs/1}".
es_regs(R):- compound(R), R=..Y, listaAtomica(Y), functor(R,F,N), F==regs, N > 1.

% listaAtomica(Y) es cierto si todos los elementos de la lista Y son atomic.
:- pred listaAtomica(Y)
#"Devuelve cierto si todos los elementos de la lista @var{Y} son atomic. @includedef{listaAtomica/1}".
listaAtomica([]).
listaAtomica([X|Y]):- atomic(X), listaAtomica(Y).

% crear_lista_regs_sin_functor(R,L) es cierto si L es una lista con todos los componentes de la estructura regs
:- pred crear_lista_regs_sin_functor(R,L)
#"Devuelve cierto si @var{L} es una lista con todos los componentes de la estructura regs. @includedef{crear_lista_regs_sin_functor/2}".
crear_lista_regs_sin_functor(R,L):- R=..Ls, borrarPrimerElemento(Ls,L).

% crear_lista_regs(R,L) es cierto si L es una lista que tiene como cabeza el functor y como resto de la lista todos los componentes de la estructura regs
:- pred crear_lista_regs(R,L)
#"Devuelve cierto si @var{L} es una lista que tiene como cabeza el functor y como resto de la lista todos los componentes de la estructura regs. @includedef{crear_lista_regs/2}".
crear_lista_regs(R,L):- R=..L.

% borrarPrimerElemento(Ls,L) es cierto si L es la lista Ls sin su primer elemento
:- pred borrarPrimerElemento(Ls,L)
#"Devuelve cierto si @var{L} es la lista @var{Ls} sin su primer elemento. @includedef{borrarPrimerElemento/2}".
borrarPrimerElemento([_|X],X).

% eliminarComodinesListaSimbolos(L1,L2) verifica que L2 es el resultado de eliminar de L1 todas las ocurrencias de comodines (*).
:- pred eliminarComodinesListaSimbolos(L1,L2)
#"Verifica que @var{L2} es el resultado de eliminar de @var{L1} todas las ocurrencias de comodines (*). @includedef{eliminarComodinesListaSimbolos/2}".
eliminarComodinesListaSimbolos([],[]).
eliminarComodinesListaSimbolos([L|L1],[L|L2]):- '*'\=L, eliminarComodinesListaSimbolos(L1,L2). % No es el elemento que queremos eliminar
eliminarComodinesListaSimbolos([*|L1],L2):- eliminarComodinesListaSimbolos(L1,L2). % Es el elemento que queremos eliminar

% listaRegistrosSinComodines(L1,L2) verifica que L2 es el resultado de sustituir en L1 todas las ocurrencias de comodines (*) por variables anonimas (_).
:- pred listaRegistrosSinComodines(L1,L2)
#"Verifica que @var{L2} es el resultado de sustituir en @var{L1} todas las ocurrencias de comodines (*) por variables anonimas (_). @includedef{listaRegistrosSinComodines/2}".
listaRegistrosSinComodines([],[]).
listaRegistrosSinComodines([L|L1],[L|L2]):- '*'\=L, listaRegistrosSinComodines(L1,L2). % No es el elemento que queremos eliminar
listaRegistrosSinComodines([*|L1],[_|L2]):- listaRegistrosSinComodines(L1,L2). % Es el elemento que queremos eliminar

% comprobarRegistrosSinComodines(L1,L2) es cierto si donde en la lista L1 hay un *, en la L2 hay una variable.
:- pred comprobarRegistrosSinComodines(L1,L2)
#"Devuelve cierto si donde en la lista @var{L1} hay un *, en la @var{L2} hay una variable. @includedef{comprobarRegistrosSinComodines/2}".
comprobarRegistrosSinComodines([],[]).
comprobarRegistrosSinComodines([*|Xs],[Y|Ys]):- var(Y), comprobarRegistrosSinComodines(Xs,Ys).
comprobarRegistrosSinComodines([X|Xs],[X|Ys]):- X\='*', comprobarRegistrosSinComodines(Xs,Ys).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ejecutar_instruccion(EstadoActual,Instruccion,EstadoSiguiente) materializa la transicion entre los estados actual y siguiente mediante la ejecucion de una instruccion. Dado que el movimiento entre estados se produce mediante la ejecucion de instrucciones.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos) es cierto si se cumplen las condiciones mencionadas anteriormente. Para ello, se ha seguido el siguiente procedimiento:
% 1) Se llama a eliminar_comodines para verificar que los registros son correctos y prepararlos (sustituyendo * por _) y asi trabajar mas facilmente.
% 2) En funcion de si nos llega un move o un swap, ejecutar su correspondiente movimiento copiando un registro en el siguiente (move) o intercambiando los registros (swap). Esta funcion nos devuelve una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el movimiento.
% 3) Generamos el estado final al ejecutar el movimiento a partir de la estructura de registros inicial y la que nos ha devuelto el paso anterior.
% 4) En el estado final del anterior apartado, sustituimos en una nueva estructura las variables anonimas por * para devolver esa estructura como estado final de la ejecucion del movimiento.

:- pred ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos)
#"Devuelve cierto si materializa la transicion entre los estados actual @var{EA} y siguiente @var{ESCompletoConAsteriscos} mediante la ejecucion de una @var{Instruccion}. Dado que el movimiento entre estados se producen mediante la ejecucion de instrucciones. @includedef{ejecutar_instruccion/3}".
ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos):- eliminar_comodines(EA,EASinComodines,_ListaSimbolos), movimiento(EASinComodines,Instruccion,ES), completarEstructuraInstruccion(EASinComodines,ES,1,Instruccion,ESCompleto), functor(ESCompleto,regs,Length), functor(ESCompletoConAsteriscos,regs,Length), varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,1).

% movimiento(EASinComodines,move(I),ES) devuelve en ES una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el move. En este caso, al ser un move, solo NO devolvera variable en el registro que se haya copiado el contenido del registro anterior.
% Ya que hablamos de una CPU que cuenta con N registros organizados de forma anular, para el move se han tenido que separar dos casos:
% 1) Si se va a hacer el move de un registro que no es el ultimo:
%     - Se comprueba que I es mayor que 0 y menor que length de regs y que I no es la ultima posicion.
%     - Se hace el movimiento cogiendo el elemento en la posicion I de EASinComodines y se lo meto a ES en la pos I+1.
% 2) Si se va a hacer el move del ultimo registro:
%     - Mismo algoritmo que en el caso anterior, pero cuando I es el ultimo registro, se hace el move al primer registro.

:- pred movimiento(EASinComodines,move(I),ES)
#"Devuelve en @var{ES} una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el move. En este caso, al ser un move, solo NO devolvera variable en el registro que se haya copiado el contenido del registro anterior. @includedef{movimiento/3}".
movimiento(EASinComodines,move(I),ES):- functor(EASinComodines,regs,Length), integer(I), I>0, I<Length, I\=Length, arg(I,EASinComodines,C), functor(ES,regs,Length), I2 is I+1, arg(I2,ES,C).
movimiento(EASinComodines,move(I),ES):- functor(EASinComodines,regs,Length), integer(I), I==Length, arg(I,EASinComodines,C), functor(ES,regs,Length), arg(1,ES,C).

% movimiento(EASinComodines,swap(I,J),ES) devuelve en ES una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el swap. En este caso, al ser un swap, solo NO devolvera variable en los registro intervinientes en el intercambio de contenidos.
% Esta vez, aunque se trate de una CPU que cuenta con N registros organizados de forma anular, en el swap es suficiente contemplar un caso que se cumplira para todos los registros:
%  - Se comprueba que I es distinto que J.
%  - Se comprueba que I y J sean mayores que 0 y menores o iguales que length.
%  - Se intercambian los registros copiando de EASinComodines en la pos I y llevandolo a ES en la pos J, y viceversa.

:- pred movimiento(EASinComodines,swap(I,J),ES)
#"Devuelve en @var{ES} una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar swap. En este caso, al ser un swap, solo NO devolvera variable en los registros intervinientes en el intercambio de contenidos. @includedef{movimiento/3}".
movimiento(EASinComodines,swap(I,J),ES):- I\=J, functor(EASinComodines,regs,Length), integer(I), integer(J), I>0, I=<Length, J>0, J=<Length, arg(I,EASinComodines,CI), arg(J,EASinComodines,CJ), functor(ES,regs,Length), arg(J,ES,CI), arg(I,ES,CJ).

% completarEstructuraInstruccion(EASinComodines,ES,Pos,Instruccion,ESCompleto) genera una nueva estructura ESCompleto en la que se devuelve el estado final al ejecutar el movimiento a partir de la estructura de registros inicial y la que nos ha devuelto la llamada a movimiento(EASinComodines,Instruccion,ES). El algoritmo es crear una platilla de estructura para almacenar el resultado en ESCompleto e ir completando dicha estructura con las posiciones alteradas por el move o swap y las que se mantienen igual de un estado a otro.
% En el caso de haber ejecutado un move, separaremos de nuevo en dos casos posibles:
% 1) Cuando se ha hecho move de cualquier registro excepto del ultimo.
% 2) Cuando se ha hecho el move del ultimo.

:- pred completarEstructuraInstruccion(EASinComodines,ES,Pos,Instruccion,ESCompleto)
#"Genera una nueva estructura @var{ESCompleto} en la que se devuelve el estado final al ejecutar el movimiento a partir de la estructura de registros inicial y la que nos ha devuelto la llamada a @bf{movimiento(EASinComodines,Instruccion,ES)}. El algoritmo es crear una platilla de estructura para almacenar el resultado en @var{ESCompleto} e ir completando dicha estructura con las posiciones alteradas por el move o swap y las que se mantienen igual de un estado a otro. @includedef{completarEstructuraInstruccion/5}".
completarEstructuraInstruccion(EASinComodines,ES,Pos,Instruccion,ESCompleto):- functor(Instruccion,move,1), functor(EASinComodines,regs,Length), functor(ESCompleto,regs,Length), arg(1,Instruccion,N), N1 is N+1, N\=Length, completarEstructuraMove(EASinComodines,ES,Pos,N1,ESCompleto).
completarEstructuraInstruccion(EASinComodines,ES,Pos,Instruccion,ESCompleto):- functor(Instruccion,move,1), functor(EASinComodines,regs,Length), functor(ESCompleto,regs,Length), arg(1,Instruccion,N), N==Length, completarEstructuraMove(EASinComodines,ES,Pos,1,ESCompleto).
% En el caso de haber ejecutado un swap, solo hay un posible caso:
completarEstructuraInstruccion(EASinComodines,ES,Pos,Instruccion,ESCompleto):- functor(Instruccion,swap,2), functor(EASinComodines,regs,Length), functor(ESCompleto,regs,Length), arg(1,Instruccion,N1), arg(2,Instruccion,N2),completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto).

% completarEstructuraMove(EASinComodines,ES,Pos,N,ESCompleto) completa la estructura final a devolver con el estado actual. Se copia del EA al ESCompleto todas las posiciones excepto las alteradas por move. Estas ultimas se copiaran desde el ES al ESCompleto.
:- pred completarEstructuraMove(EASinComodines,ES,Pos,N,ESCompleto)
#"Completa la estructura final a devolver con el estado actual. Se copia del @var{EA} al @var{ESCompleto} todas las posiciones excepto las alteradas por move. Estas ultimas se copiaran desde el @var{ES} al @var{ESCompleto}. @includedef{completarEstructuraMove/5}".
% El caso base se dara cuando se ha recorrido toda la CPU porque el puntero pos es mayor que la longitud del registro.
completarEstructuraMove(EASinComodines,_ES,Pos,_N,_ESCompleto):- functor(EASinComodines,regs,Length), Pos>Length.
% Si el contenido del registro pos no ha sido modificado por move, se reemplaza en ES la pos por el contenido que tenga EA en la misma posicion.
completarEstructuraMove(EASinComodines,ES,Pos,N,ESCompleto):- N\=Pos, arg(Pos,EASinComodines,C), arg(Pos,ESCompleto,C), Pos1 is Pos+1, completarEstructuraMove(EASinComodines,ES,Pos1,N,ESCompleto).
% Si el registro pos es la posicion modificada por move, se copia de ES a ESCompleto lo que hay en pos y se va al siguiente registro.
completarEstructuraMove(EASinComodines,ES,Pos,N,ESCompleto):- N=Pos, arg(Pos,ES,C), arg(Pos,ESCompleto,C), Pos1 is Pos+1, completarEstructuraMove(EASinComodines,ES,Pos1,N,ESCompleto).

% completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto) completa la estructura final a devolver con el estado actual. Se copia del EA al ESCompleto todas las posiciones excepto las alteradas por swap. Estas ultimas se copiaran desde el ES al ESCompleto.
:- pred completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto)
#"Completa la estructura final a devolver con el estado actual. Se copia del @var{EA} al @var{ESCompleto} todas las posiciones excepto las alteradas por swap. Estas ultimas se copiaran desde el @var{ES} al @var{ESCompleto}. @includedef{completarEstructuraSwap/6}".
% El caso base se dara cuando se ha recorrido toda la CPU porque el puntero pos es mayor que la longitud del registro.
completarEstructuraSwap(EASinComodines,_ES,Pos,_N1,_N2,_ESCompleto):- functor(EASinComodines,regs,Length), Pos>Length.
% Si el contenido del registro pos no ha sido modificado por swap, se reemplaza en ES la pos por la que tenga EA en la misma posicion.
completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto):- N1\=Pos, N2\=Pos, arg(Pos,EASinComodines,C), arg(Pos,ESCompleto,C), Pos1 is Pos+1, completarEstructuraSwap(EASinComodines,ES,Pos1,N1,N2,ESCompleto).
%  Si el registro pos es la posicion modificada por swap (N1 o N2), se copia de ES a ESCompleto lo que hay en pos y se va al siguiente registro.
completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto):- N1=Pos, arg(Pos,ES,C), arg(Pos,ESCompleto,C), Pos1 is Pos+1, completarEstructuraSwap(EASinComodines,ES,Pos1,N1,N2,ESCompleto).
completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto):- N2=Pos, arg(Pos,ES,C), arg(Pos,ESCompleto,C), Pos1 is Pos+1, completarEstructuraSwap(EASinComodines,ES,Pos1,N1,N2,ESCompleto).

% varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos) devuelve en ESCompletoConAsteriscos el registro equivalente a sustituir las varAnonimas (_) por * en los registros de ESCompleto.
:- pred varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos)
#"Devuelve en @var{ESCompletoConAsteriscos} el registro equivalente a sustituir las variables anonimas (_) por * en los registros de @var{ESCompleto}. @includedef{varAnonimaToAsterisco/3}".
% El caso base se dara cuando pos > length.
varAnonimaToAsterisco(ESCompleto,_ESCompletoConAsteriscos,Pos):- functor(ESCompleto,regs,Length), Pos>Length.
% Si en la posicion que estamos hay un _, se sustituye por *.
varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos):- arg(Pos,ESCompleto,C), var(C), arg(Pos,ESCompletoConAsteriscos,*), Pos1 is Pos+1, varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos1).
% Si en la posicion en la que estamos no hay _, entonces se copia lo que hay en pos de ESCompleto a ESCompletoConAsteriscos.
varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos):- arg(Pos,ESCompleto,C), nonvar(C), arg(Pos,ESCompletoConAsteriscos,C), Pos1 is Pos+1, varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generador_de_codigo(EstadoInicial,EstadoFinal,ListaInstrucciones) que sera cierto si ListaInstrucciones unifica con una lista de instrucciones de la CPU que aplicadas secuencialmente desde el estado inicial de los registros representado por EstadoInicial permite transitar hacia el estado final de los registros representado por EstadoFinals. Dado que en general existen multiples soluciones para el problema, bastara unicamente con que el programa devuelva una unica solucion valida siempre y cuando esta sea minima. O todas las posibles soluciones minimas existentes. En ningun caso, el programa se debe quedar atrapado en bucles infinitos al devolver alguna solucion.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% generador_de_codigo(EI,EF,ListaInstrucciones) es cierto si se cumplen las condiciones mencionadas anteriormente. Para ello, se ha seguido el siguiente razonamiento y el siguiente procedimiento:
% 1) Se llama a generador_de_codigo_SOLO_UN_CAMINO, el cual nos va a devolver UNO de los caminos minimos para esta solucion. Este camino minimo nos sirve para saber el numero de movimientos minimos que hay del estado inicial al final. Asi, cuando queramos obtener todos los caminos minimos, solo generaremos listas de instrucciones con tamaño igual a esta solucion. Este predicado hace exactamente lo mismo que generador_de_codigo_TODOS_LOS_CAMINOS (explicado mas adelante) pero solo encontrando una solucion.
% 2) Nos almacenamos el tamaño de la minima solucion para pasarselo como parametro al "verdadero" generador_de_codigo (paso 3).
% 3) Se llama a generador_de_codigo_TODOS_LOS_CAMINOS. Este predicado nos va a devolver todas las soluciones minimas existentes (podria haber varias) sin quedarse atrapado en bucles infinitos.

:- pred generador_de_codigo(EI,EF,ListaInstrucciones)
#"Devuelve cierto si @var{ListaInstrucciones} unifica con una lista de instrucciones de la CPU que aplicadas secuencialmente desde el estado inicial @var{EI} de los registros permite transitar hacia el estado final @var{EF} de los registros. Dado que en general existen multiples soluciones para el problema, bastara unicamente con que el programa devuelva una unica solucion valida siempre y cuando esta sea minima. O todas las posibles soluciones minimas existentes. En ningun caso, el programa se debe quedar atrapado en bucles infinitos al devolver alguna solucion. @includedef{generador_de_codigo/3}".
generador_de_codigo(EI,EF,ListaInstrucciones):- generador_de_codigo_SOLO_UN_CAMINO(EI,EF,ListaInstruccionesMin,EISinComodines,EFSinComodines), length(ListaInstruccionesMin,TamanoCaminoMinimo), generador_de_codigo_TODOS_LOS_CAMINOS(EISinComodines,EFSinComodines,ListaInstrucciones,TamanoCaminoMinimo).

% generador_de_codigo_TODOS_LOS_CAMINOS(EISinComodines,EFSinComodines,ListaInstrucciones,TamanoCaminoMinimo) saca en ListaInstrucciones todos los posibles caminos minimos desde el estado inicial EISinComodines al estado final EFSinComodines. Se ha seguido el siguiente procedimiento:
% Como generador_de_codigo_SOLO_UN_CAMINO ya comprueba que los registros sean correctos y elimina los comodines tanto del estado inicial como del final, este generador_de_codigo_TODOS_LOS_CAMINOS no vuelve a hacer esas comprobaciones. Y generador_de_codigo_SOLO_UN_CAMINO nos pasa los estados inicial y final sin comodines (en el anterior predicado). Lo unico que hacemos es calcular el numero de registros y llamar a buscarSolucion para encontrar todas las posibles soluciones de caminos minimos cuyo procedimiento esta explicado junto al predicado. En buscarSolucion, en este caso, arrastraremos el numero de TamanoCaminoMinimo para unicamente calcular los recorridos minimos y descartar todos los demas.
:- pred generador_de_codigo_TODOS_LOS_CAMINOS(EISinComodines,EFSinComodines,ListaInstrucciones,TamanoCaminoMinimo)
#"Saca en @var{ListaInstrucciones} todos los posibles caminos minimos desde el estado inicial @var{EISinComodines} al estado final @var{EFSinComodines}. @includedef{generador_de_codigo_TODOS_LOS_CAMINOS/4}".
generador_de_codigo_TODOS_LOS_CAMINOS(EISinComodines,EFSinComodines,ListaInstrucciones,TamanoCaminoMinimo):-
length(ListaInstrucciones,TamanoCaminoMinimo), functor(EISinComodines,regs,N1),
    buscarSolucion(EISinComodines,EFSinComodines,N1,ListaInstrucciones,TamanoCaminoMinimo).

% generador_de_codigo_SOLO_UN_CAMINO(EI,EF,ListaInstrucciones,EISinComodines,EFSinComodines) tiene como funcionalidad la misma que generador_de_codigo_TODOS_LOS_CAMINOS pero sacando solo la primera solucion (mediante un corte). Sirve para que a partir de este se puedan sacar en generador_de_codigo_TODOS_LOS_CAMINOS SOLO los caminos minimos. En este, ademas, se comprueba que los registros sean correctos y se eliminan los comodines tanto del estado inicial como del final. Y usaremos estos como parametros de salida para generador_de_codigo_TODOS_LOS_CAMINOS no tenga que volver a calcularlos y hacer las comprobaciones necesarias. Ademas, se comprueba que tanto la estructura de registros inicial como final tengan el mismo numero de registros.
:- pred generador_de_codigo_SOLO_UN_CAMINO(EI,EF,ListaInstrucciones,EISinComodines,EFSinComodines)
#"Tiene como funcionalidad la misma que generador_de_codigo_TODOS_LOS_CAMINOS pero sacando solo la primera solucion (mediante un corte). Sirve para que a partir de este se puedan sacar en generador_de_codigo_TODOS_LOS_CAMINOS SOLO los caminos minimos. En este, ademas, se comprueba que los registros sean correctos y se eliminan los comodines tanto del estado inicial @var{EI} como del final @var{EF}. Y usaremos estos como parametros de salida para generador_de_codigo_TODOS_LOS_CAMINOS no tenga que volver a calcularlos y hacer las comprobaciones necesarias. Ademas, se comprueba que tanto la estructura de registros inicial como final tengan el mismo numero de registros. @includedef{generador_de_codigo_SOLO_UN_CAMINO/5}".
generador_de_codigo_SOLO_UN_CAMINO(EI,EF,ListaInstrucciones,EISinComodines,EFSinComodines):-
    eliminar_comodines(EI, EISinComodines, ListaSimbolosI),
    eliminar_comodines(EF, EFSinComodines, ListaSimbolosF),
    comprobarAlfabetoRegistros(ListaSimbolosI,ListaSimbolosF),
    functor(EISinComodines,regs,N1), functor(EFSinComodines,regs,N2), N1==N2, length(ListaInstrucciones,_L),
    buscarSolucionTamMin(EISinComodines,EFSinComodines,N1,ListaInstrucciones), !.

% comprobarSolucion(EF,_ETemporal,Pos) comprueba que la solucion sea valida:
% 1) Pos siempre se inicializa a 1 al llamar a este  predicado. Quiere decir que empezamos a comparar desde el registro numero 1.
% 2) Si el registro final tiene un elemento que no es variable, en la posible solucion ETemporal debe aparecer el mismo en la misma posicion.
% 3) Si el registro final tiene un elemento que si es variable, como no nos importa el contenido que haya en la posible solucion, aumentamos el contador Pos para pasar al siguiente registro y seguir comprobando si la solucion es valida.
:- pred comprobarSolucion(EF,_ETemporal,Pos)
#"Comprueba que la solucion sea valida. @includedef{comprobarSolucion/3}".
comprobarSolucion(EF,_ETemporal,Pos):- functor(EF,regs,Length), Pos>Length.
comprobarSolucion(EF,ETemporal,Pos):- arg(Pos,EF,C1), nonvar(C1), arg(Pos,ETemporal,C2), C1==C2, Pos1 is Pos+1, comprobarSolucion(EF,ETemporal,Pos1).
comprobarSolucion(EF,ETemporal,Pos):- arg(Pos,EF,C1), var(C1), Pos1 is Pos+1, comprobarSolucion(EF,ETemporal,Pos1).

% miembro(X,L) se verifica si X es miembro de la lista L.
:- pred miembro(X,L)
#"Se verifica si @var{X} es miembro de la lista @var{L}. @includedef{miembro/2}".
miembro(X,[X|_U]).
miembro(X,[_Y|Z]):- miembro(X,Z).

% comprobarAlfabetoRegistros(Inicial,[X|Y]) tiene como entrada una lista de contenidos de registros inicial y otra lista de contenidos de registros final. Se verifica si todos los elementos que hay en la lista final estan en la inicial.
:- pred comprobarAlfabetoRegistros(Inicial,[X|Y])
#"Tiene como entrada una lista de contenidos de registros inicial @var{Inicial} y otra lista de contenidos de registros final @var{[X|Y]}. Se verifica si todos los elementos que hay en la lista final estan en la inicial. @includedef{comprobarAlfabetoRegistros/2} ".
comprobarAlfabetoRegistros(_Inicial,[]).
comprobarAlfabetoRegistros(Inicial,[X|Y]):- miembro(X,Inicial), comprobarAlfabetoRegistros(Inicial,Y).

% buscarSolucion(EI,EF,N,ListaInstrucciones,TamanoCaminoMinimo) va a ser unicamente usada por generador_de_codigo_TODOS_LOS_CAMINOS.
% Una vez que sabemos el minimo numero de movimientos de la solucion, el predicado busca todas las soluciones posibles con la misma longitud.
% Para llevarlo a cabo, se han implementado los siguientes pasos:
% 1) Se comprueba que la longitud de la nueva solucion sea menor (cuando se va construyendo) o igual a la minima.
% 2) Consigue una nueva posible instruccion a ejecutar (move o swap).
% 3) Prepara el estado inicial, y en los registros donde tenga _ se ponen * para poder llamar a ejecutar_instruccion.
% 4) Llama a ejecutar_instruccion.
% 5) Al estado siguiente que ha devuelto ejecutar_instruccion, se le vuelven a cambiar los * por _ para poder seguir iterando y sacando mas movimientos.
% 6) Se llama recursivamente a buscarSolucion para encontrar los siguientes movimientos.
% 7) Los casos base seran que el estado inicial sea igual al final o cortar las llamadas recursivas cuando estemos buscando una solucion que tenga mas movimientos que el camino minimo.
:- pred buscarSolucion(EI,EF,N,ListaInstrucciones,TamanoCaminoMinimo)
#"Predicado unicamente usado por generador_de_codigo_TODOS_LOS_CAMINOS. Una vez que sabemos el minimo numero de movimientos de la solucion, el predicado busca todas las soluciones posibles con la misma longitud. @includedef{buscarSolucion/5}".
buscarSolucion(EI,EF,_N,[],_TamanoCaminoMinimo):- comprobarSolucion(EF,EI,1).
buscarSolucion(_EI,_EF,_NRegs,ListaInstrucciones,TamanoCaminoMinimo):- length(ListaInstrucciones,I), I>TamanoCaminoMinimo.
buscarSolucion(EI,EF,N,[I|Is],TamanoCaminoMinimo):- length(Is,I1), I2 is I1+1, I2=<TamanoCaminoMinimo, generarNuevaInstruccion(N,I), functor(EI,regs,Length), functor(EIConAsteriscos,regs,Length), varAnonimaToAsterisco(EI,EIConAsteriscos,1), ejecutar_instruccion(EIConAsteriscos,I,ESiguienteConAsteriscos), eliminar_comodines2(ESiguienteConAsteriscos,ESiguiente), buscarSolucion(ESiguiente,EF,N,Is,TamanoCaminoMinimo).

% buscarSolucionTamMin(EI,EF,N,ListaInstrucciones) va a ser unicamente usada por generador_de_codigo_SOLO_UN_CAMINO.
% Queremos obtener unicamente una solucion para obtener el minimo numero de movimientos de la solucion. Y asi llamar a generador_de_codigo_TODOS_LOS_CAMINOS y poder encontrar todas las demas soluciones con el tamaño minimo. La funcionalidad es igual que la de buscarSolucion pero reducida, ya que se llama desde generar_codigo_SOLO_UN_CAMINO y ya sabemos que nos va a sacar siempre uno de los caminos minimos.
% Para llevarlo a cabo, se han implementado los siguientes pasos:
% 1) Consigue una nueva posible instruccion a ejecutar (move o swap).
% 2) Prepara el estado inicial, y en los registros donde tenga _ se ponen * para poder llamar a ejecutar_instruccion.
% 3) Llama a ejecutar_instruccion.
% 4) Al estado siguiente que ha devuelto ejecutar_instruccion, se le vuelven a cambiar los * por _ para poder seguir iterando y sacando mas movimietos.
% 5) Se llama recursivamente a buscarSolucion para encontrar los siguientes moovimientos.
% 6) En el caso base sera que el estado inicial sea igual al final.
:- pred buscarSolucionTamMin(EI,EF,N,ListaInstrucciones)
#"Predicado unicamente usado por generador_de_codigo_SOLO_UN_CAMINO. Queremos obtener unicamente una solucion para obtener el minimo numero de movimientos de la solucion. Y asi llamar a generador_de_codigo_TODOS_LOS_CAMINOS y poder encontrar todas las demas soluciones con el tamaño minimo. @includedef{buscarSolucionTamMin/4}".
buscarSolucionTamMin(EI,EF,_N,[]):- comprobarSolucion(EF,EI,1).
buscarSolucionTamMin(EI,EF,NRegs,[I|Is]):- generarNuevaInstruccion(NRegs,I), functor(EI,regs,Length), functor(EIConAsteriscos,regs,Length), varAnonimaToAsterisco(EI,EIConAsteriscos,1), ejecutar_instruccion(EIConAsteriscos,I,ESiguienteConAsteriscos), eliminar_comodines2(ESiguienteConAsteriscos,ESiguiente), buscarSolucionTamMin(ESiguiente,EF,NRegs,Is).

% eliminar_comodines2(Registros, RegistrosSinComodines) es un predicado simplificado de eliminar_comodines, ya que no hace las comprobaciones necesarias en los registros porque se han hecho al inicio de generador_de_codigo. Lo unico que hace es preparar los registros para seguir con la ejecucion. Es decir, convierte todos los * en _.
:- pred eliminar_comodines2(Registros, RegistrosSinComodines)
#"Predicado simplificado de eliminar_comodines, ya que no hace las comprobaciones necesarias en los registros porque se han hecho al inicio de generador_de_codigo. Lo unico que hace es preparar los registros para seguir con la ejecucion. Es decir, convierte todos los * en _. @includedef{eliminar_comodines2/2}".
eliminar_comodines2(Registros,RegistrosSinComodines):- crear_lista_regs(Registros,L2), listaRegistrosSinComodines(L2,L3), RegistrosSinComodines=..L3, comprobarRegistrosSinComodines(L2,L3).

% generarNuevaInstruccion(N,Instruccion) consigue una nueva posible instruccion a ejecutar. Primero obtiene todos los posibles move y luego todos los posibles swap. Se llama a un predicado que los obtiene obtenerPosibleMove/Swap y otro que crea el literal del movimiento de cada uno de los obtenidos creaLiteralMove/Swap.
:- pred generarNuevaInstruccion(N,Instruccion)
#"Consigue una nueva posible instruccion a ejecutar. Primero obtiene todos los posibles move y luego todos los posibles swap. @includedef{generarNuevaInstruccion/2}".
generarNuevaInstruccion(N,move(I)):- obtenerPosibleMove(N,NuevoMove), creaLiteralMove(NuevoMove,move(I)).
generarNuevaInstruccion(N,swap(I,J)):- obtenerPosibleSwap(N,N1,N2), creaLiteralSwap(N1,N2,swap(I,J)).

% obtenerPosibleMove(N,NumMove) obtiene un posible movimiento move a partir del numero de registros para ese registro. Va en orden decreciente hasta que llega a 1 y termina (caso base).
:- pred obtenerPosibleMove(N,NumMove)
#"Obtiene un posible movimiento move a partir del numero de registros para ese registro. Va en orden decreciente hasta que llega a 1 y termina (caso base). @includedef{obtenerPosibleMove/2}".
obtenerPosibleMove(N,N).
obtenerPosibleMove(N,NumMove):- N>1, N1 is N-1, obtenerPosibleMove(N1,NumMove).

% obtenerPosibleSwap(N,X,Y) obtiene un posible movimiento swap a partir del numero de registros para ese registro. Obtiene las combinaciones posibles de swap desde Y hacia todos los registros que le quedan a la derecha (fin del registro: X).
:- pred obtenerPosibleSwap(N,X,Y)
#"Obtiene un posible movimiento swap a partir del numero de registros para ese registro. Obtiene las combinaciones posibles de swap desde @var{Y} hacia todos los registros que le quedan a la derecha (fin del registro: @var{X}). @includedef{obtenerPosibleSwap/3}".
obtenerPosibleSwap(N,X,Y) :- N1 is N+1, combinacionesSwap(1,N1,Y), combinacionesSwap(1,Y,X).

% combinacionesSwap(A,B,C) obtiene todos los posibles movimientos de tipo swap. Empezando por A (que siempre es 1), va a dar las posibles combinaciones de swap con B, que van a ser siempre por la izquierda. Es decir, para B=4, nos dara 1, 2 y 3. Que son los swaps posibles de B por su izquierda. Los swaps de B por su derecha los daran posteriormente los elementos que esten a su derecha.
:- pred combinacionesSwap(A,B,C)
#"Obtiene todos los posibles movimientos de tipo swap. Empezando por @var{A} (que siempre es 1), va a dar las posibles combinaciones de swap con @var{B}, que van a ser siempre por la izquierda. Es decir, para @var{B}=4, nos dara 1, 2 y 3. @includedef{combinacionesSwap/3}".
combinacionesSwap(A,B,A):- A<B.
combinacionesSwap(A,B,C):- A<B, A1 is A+1, combinacionesSwap(A1,B,C).

% creaLiteralMove(N,move(N)) es un hecho que genera la estructura del literal move(i) donde i es N. Sirve para añadirlo a la lista de Instrucciones.
:- pred creaLiteralMove(N,move(N))
#"Hecho que genera la estructura del literal @var{move(i)} donde @var{i} es @var{N}. Sirve para añadirlo a la lista de Instrucciones. @includedef{creaLiteralMove/2}".
creaLiteralMove(N,move(N)).

% creaLiteralSwap(N1,N2,swap(N1,N2)) es un hecho que genera la estructura del literal swap(i,j) donde i y j son los registros a intercambiar. Sirve para añadirlo a la lista de Instrucciones.
:- pred creaLiteralSwap(N1,N2,swap(N1,N2))
#"Hecho que genera la estructura del literal @var{swap(i,j)} donde @var{i} y @var{j} son los registros a intercambiar. Sirve para añadirlo a la lista de Instrucciones. @includedef{creaLiteralSwap/3}".
creaLiteralSwap(N1,N2,swap(N1,N2)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
TESTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests eliminar_comodines(X,R,L)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Se comprueba que da fallo cuando la CPU tiene menos de 2 registros
:- test eliminar_comodines(X,R,L) : (X=regs(1)) + fails #"La CPU tiene que tener de 2 a N registros".
% Se comprueba que no da fallo cuando todos los registros tienen constantes
:- test eliminar_comodines(X,R,L) : (X=regs(12,3,4,a,t,+,*,p)) + not_fails #"Registros de la CPU correctos".
% Se comprueba que da fallo cuando algun registro tiene una variable
:- test eliminar_comodines(X,R,L) : (X=regs(1,32,X,u,i9)) + fails #"Algun registro de la CPU tiene una variable".
% Se comprueba que no da fallo cuando no hay variables
:- test eliminar_comodines(X,R,L) : (X=regs(!,2)) + not_fails #"Registros de la CPU correctos".
% Se comprueba que da fallo cuando algun registro tiene un elemento que no es una constante
:- test eliminar_comodines(X,R,L) : (X=regs(1,32,4<5)) + fails #"Algun registro de la CPU tiene un elemento que no es una constante".
% Se comprueba que da fallo cuando no se elimina el comodin
:- test eliminar_comodines(X,R,L) : (X=regs(0,*),R=regs(0,*)) + fails #"No se ha eliminado el comodin".
% Se comprueba que da fallo cuando no se elimina el comodin
:- test eliminar_comodines(X,R,L) : (X=regs(*,0),R=regs(*,0)) + fails #"No se ha eliminado el comodin".
% Se comprueba que da fallo cuando no se elimina el comodin
:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*),R=regs(0,1,4,+,2,*)) + fails #"No se ha eliminado el comodin".
% Se comprueba que da fallo cuando no se elimina el comodin
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(*,1,4,+,2,3)) + fails #"No se ha eliminado el comodin".
% Se comprueba que da fallo cuando no se eliminan todos los comodines
:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_,*)) + fails #"No se han eliminado todos los comodines".
% Se comprueba que da fallo cuando no se eliminan todos los comodines
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,W,*)) + fails #"No se han eliminado todos los comodines".
% Se comprueba que da fallo cuando no se eliminan todos los comodines
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(*,0,0,_L)) + fails #"No se han eliminado todos los comodines".
% Se comprueba que da fallo cuando no se eliminan todos los comodines
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(*,1,*,+,2,*)) + fails #"No se han eliminado todos los comodines".
% Se comprueba que da fallo cuando no se sustituye el comodin por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(0,*),R=regs(0,a)) + fails #"No se ha sustituido el comodin por una variable".
% Se comprueba que da fallo cuando no se sustituye el comodin por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,0),R=regs(1,0)) + fails #"No se ha sustituido el comodin por una variable".
% Se comprueba que da fallo cuando no se sustituye el comodin por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*),R=regs(0,1,4,+,2,<)) + fails #"No se ha sustituido el comodin por una variable".
% Se comprueba que no da fallo cuando se sustituye el comodin por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3)) => (R=regs(_,1,4,+,2,3)) + not_fails #"Se ha sustituido por variable".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,*)) => (R=regs(_,_)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*)) => (R=regs(0,_,_)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*)) => (R=regs(_,0,0,_)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*)) => (R=regs(_,1,_,+,2,_)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituye el comodin por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(_,1,4,+,2,3)) + not_fails #"Se ha sustituido por variable".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_Z,_)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,_Hola,Z)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(P,0,0,_)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se sustituyen los comodines por una variable
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(_Ea,1,_,+,2,W)) + not_fails #"Se han sustituido por variables".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(1,1,+,5,*)) => (R=regs(1,1,+,5,_),L=[1,1,+,5]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(0,*)) => (R=regs(0,_),L=[0]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,0)) => (R=regs(_,0),L=[0]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*)) => (R=regs(0,1,4,+,2,_),L=[0,1,4,+,2]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3)) => (R=regs(_,1,4,+,2,3),L=[1,4,+,2,3]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,*)) => (R=regs(_,_),L=[]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*)) => (R=regs(0,_,_),L=[0]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*)) => (R=regs(_,0,0,_),L=[0,0]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*)) => (R=regs(_,1,_,+,2,_),L=[1,+,2]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3)) => (R=regs(_,1,4,+,2,3),L=[1,4,+,2,3]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,*)) => (R=regs(_Z,_),L=[]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*)) => (R=regs(0,_Hola,Z),L=[0]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*)) => (R=regs(P,0,0,_),L=[0,0]) + not_fails #"Lista generada correctamente".
% Se comprueba que no da fallo cuando se genera la lista correctamente
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*)) => (R=regs(_Ea,1,_,+,2,W),L=[1,+,2]) + not_fails #"Lista generada correctamente".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(1,1,+,5,*),R=regs(1,1,+,5,_),L=[1,1,+]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(0,*),R=regs(0,_),L=[0,1]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,0),R=regs(_,0),L=[0,2]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*),R=regs(0,1,4,+,2,_),L=[0,1,4,+,2,3]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(_,1,4,+,2,3),L=[1,4,+,2]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_,_),L=[1]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,_,_),L=[]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(_,0,0,_),L=[0,0,3]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(_,1,_,+,2,_),L=[1,+,2,5]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(_,1,4,+,2,3),L=[1,4,+,2]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_Z,_),L=[1]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,_Hola,Z),L=[0,5]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(P,0,0,_),L=[0,0,0]) + fails #"Lista generada de forma incorrecta".
% Se comprueba que da fallo cuando se genera la lista
:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(_Ea,1,_,+,2,W),L=[1,+,2,0]) + fails #"Lista generada de forma incorrecta".


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests ejecutar_instruccion(EA,I,ES)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Se comprueba que da fallo cuando la CPU tiene menos de 2 registros
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1)) + fails #"La CPU tiene que tener de 2 a N registros".
% Se comprueba que no da fallo cuando todos los registros tienen constantes
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(12,3,4,a,t,+,*,p),I=move(1)) + not_fails #"Registros de la CPU correctos".
% Se comprueba que da fallo cuando algun registro tiene una variable
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,32,X,u,i9),I=swap(1,7)) + fails #"Algun registro de la CPU tiene una variable".
% Se comprueba que no da fallo cuando no hay variables
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(!,2),I=swap(1,2)) + not_fails #"Registros de la CPU correctos".
% Se comprueba que da fallo cuando algun registro tiene un elemento que no es una constante
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,32,4<5),I=move(1)) + fails #"Algun registro de la CPU tiene un elemento que no es una constante".
% Se comprueba que da fallo cuando se meten parametros al swap que no son numeros
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,a)) + fails #"Parametro no valido en swap".
% Se comprueba que da fallo cuando se meten parametros al swap que no son numeros
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(b,2)) + fails #"Parametro no valido en swap".
% Se comprueba que da fallo cuando se meten parametros al swap que no son numeros
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,'a')) + fails #"Parametro no valido en swap".
% Se comprueba que da fallo cuando se meten parametros al swap que no son numeros
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,"a")) + fails #"Parametro no valido en swap".
% Se comprueba que da fallo cuando se meten mas de 2 numeros al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,2,4)) + fails #"Swap solo tiene 2 parametros".
% Se comprueba que da fallo cuando se mete solo 1 numero al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1)) + fails #"Swap necesita 2 parametros".
% Se comprueba que da fallo cuando primer parametro es igual que el segundo en swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(5,5)) + fails #"i tiene que ser menor que j en swap".
% Se comprueba que da fallo cuando se mete 0 al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(0,1)) + fails #"No hay registro 0".
% Se comprueba que da fallo cuando se mete 1 numero negativo al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(-1,1)) + fails #"No hay registros negativos".
% Se comprueba que da fallo cuando se mete algun numero mayor que el numero de registros al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(5,1)) + fails #"Los numeros de swap tienen que ser menores que el numero de registro".
% Se comprueba que da fallo cuando se mete algun numero mayor que el numero de registros al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,5)) + fails #"Los numeros de swap tienen que ser menores que el numero de registro".
% Se comprueba que da fallo cuando se mete algun numero mayor que el numero de registros al swap
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(5,7)) + fails #"Los numeros de swap tienen que ser menores que el numero de registro".
% Se comprueba que da fallo cuando se mete mas de 1 numero al move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(1,2)) + fails #"Move solo tiene 1 parametro".
% Se comprueba que da fallo cuando se mete mas de 1 numero al move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(1,2,3)) + fails #"Move solo tiene 1 parametro".
% Se comprueba que da fallo cuando se mete 1 numero negativo a move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(-1)) + fails #"El numero de move tiene que ser positivo".
% Se comprueba que da fallo cuando se mete 0 a move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(0)) + fails #"El numero de move tiene que ser positivo".
% Se comprueba que da fallo cuando se mete 1 numero mayor que numero de registros a move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(4)) + fails #"El numero de move tiene que ser menor que el numero de registros".
% Se comprueba que da fallo cuando se mete 1 parametro que no es un numero al move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(a)) + fails #"Parametro de move solo puede ser 1 numero".
% Se comprueba que da fallo cuando se mete 1 parametro que no es un numero al move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move("a")) + fails #"Parametro de move solo puede ser 1 numero".
% Se comprueba que da fallo cuando se mete 1 parametro que no es un numero al move
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move('a')) + fails #"Parametro de move solo puede ser 1 numero".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=swap(1,2)) => (ES=regs(2,1)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=swap(2,3)) => (ES=regs(1,<,*)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=swap(1,4)) => (ES=regs(-1,*,<,2)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=swap(1,2)) => (ES=regs(2,1,+,5,*)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=swap(1,2), ES=regs(1,2)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=swap(2,3), ES=regs(*,1,<)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=swap(1,4), ES=regs(*,<,-1,2)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=swap(1,2), ES=regs(*,1,2,5,+)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=move(1)) => (ES=regs(1,1)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=move(2)) => (ES=regs(1,*,*)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<,1), I=move(3)) => (ES=regs(1,*,<,<)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=move(4)) => (ES=regs(-1,*,<,-1)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=move(5)) => (ES=regs(*,2,+,5,*)) + not_fails #"Instruccion ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=move(1), ES=regs(1,2)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=move(3), ES=regs(1,<,1)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=move(4), ES=regs(2,*,*,-1)) + fails #"Instruccion no ejecutada correctamente".
% Se comprueba que no se ejecuta la instruccion correctamente
:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=move(2), ES=regs(1,1,+,5,*)) + fails #"Instruccion no ejecutada correctamente".


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests generador_de_codigo(EI,EF,L)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Se comprueba que da fallo cuando EI tiene menos de 2 registros
:- test generador_de_codigo(EI,EF,L) : (EI=regs(1)) + fails #"EI tiene que tener de 2 a N registros ".
% Se comprueba que da fallo cuando EF tiene menos de 2 registros
:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,2),EF=regs(1)) + fails #"EF tiene que tener de 2 a N registros ".
% Se comprueba que da fallo cuando algun registro tiene una variable
:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,32,X,u,i9),EF=regs(i9,32,X,u,1)) + fails #"Algun registro de la CPU tiene una variable".
% Se comprueba que no da fallo cuando no hay variables
:- test generador_de_codigo(EI,EF,L) : (EI=regs(!,2),EF=regs(2,!)) + not_fails #"Registros de la CPU correctos".
% Se comprueba que da fallo cuando algun registro tiene un elemento que no es una constante
:- test generador_de_codigo(EI,EF,L) : (IA=regs(1,32,4<5),EF=regs(32,1,4<5)) + fails #"Algun registro de la CPU tiene un elemento que no es una constante".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(<,2),EF=regs(2,<)) => (L = [swap(1,2)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(<,2),EF=regs(*,*)) => (L = []) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(<,2),EF=regs(<,<)) => (L = [move(1)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(*,*),EF=regs(a,b)) + fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c),EF=regs(b,c,b)) => (L =[swap(2,3),move(3)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,c,*),EF=regs(c,a,*)) => (L =[swap(1,2)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,2,3),EF=regs(1,1,1)) => (L =[move(1),move(2)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,<,z),EF=regs(<,<,<)) => (L =[move(2),move(3)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c),EF=regs(a,a,*)) => (L =[move(1)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(*,*,*),EF=regs(*,*,*)) => (L =[]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(*,a,*),EF=regs(a,*,*)) => (L =[swap(1,2)]) + not_fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con el tamaño minimo de instrucciones
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c,d,*),EF=regs(a,b,c,d,e)) + fails #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,*,c),EF=regs(c,a,*)) => (L=[move(1),move(3)];L=[move(1),swap(1,3)];L=[swap(1,2),move(3)];L=[swap(1,2),swap(1,3)];L=[swap(1,3),swap(2,3)];L=[swap(2,3),swap(1,2)]) + (try_sols(6), not_fails) #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c,d),EF=regs(a,d,a,b)) => (L=[move(2),move(1),swap(2,3),swap(2,4)];L=[move(2),move(1),swap(2,4),swap(3,4)];L=[move(2),move(1),swap(3,4),swap(2,3)];L=[move(2),swap(3,4),move(1),swap(2,3)];L=[swap(1,2),move(2),swap(1,2),swap(2,4)];L=[swap(1,2),move(2),swap(1,4),swap(1,2)];L=[swap(1,2),move(2),swap(2,4),swap(1,4)];L=[swap(1,2),swap(1,4),move(2),swap(1,2)];L=[swap(2,3),move(1),swap(2,3),swap(2,4)];L=[swap(2,3),move(1),swap(2,4),swap(3,4)];L=[swap(2,3),move(1),swap(3,4),swap(2,3)];L=[swap(2,3),swap(3,4),move(1),swap(2,3)];L=[swap(1,4),swap(2,4),move(2),swap(1,2)];L=[swap(2,4),move(2),move(1),swap(2,3)];L=[swap(2,4),swap(1,2),move(2),swap(1,2)];L=[swap(2,4),swap(2,3),move(1),swap(2,3)];L=[swap(3,4),swap(2,4),move(1),swap(2,3)]) + (try_sols(17), not_fails) #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c),EF=regs(a,a,*)) => (L=[move(1)]) + (try_sols(1), not_fails) #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos
:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c,d,*,e,*),EF=regs(a,*,*,a,b,e,e)) => (L = [move(6),swap(2,5),move(1),swap(2,4)];L=[swap(2,5),move(6),move(1),swap(2,4)];L=[swap(2,5),move(1),move(6),swap(2,4)];L=[swap(2,5),move(1),swap(2,4),move(6)]) + (try_sols(4), not_fails) #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos
:- test generador_de_codigo(EI,EF,L) : (EI=regs(p,r,t,*,*,w,o,w),EF=regs(*,*,*,*,*,*,p,t)) => (L=[swap(1,7),swap(3,8)];L=[swap(3,8),swap(1,7)]) + (try_sols(6), not_fails) #"Lista minima generada correctamente".
% Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos
:- test generador_de_codigo(EI,EF,L) : (EI=regs(p,r,t,*,*,w,o,w),EF=regs(*,p,w,*,o,*,p,t)) => (L=[move(1),swap(1,5),swap(5,7),swap(3,8)];L=[move(1),swap(1,5),swap(3,8),swap(5,7)];L=[move(1),swap(1,7),swap(1,5),swap(3,8)];L=[move(1),swap(1,7),swap(3,8),swap(1,5)];L=[move(1),swap(5,7),swap(1,7),swap(3,8)];L=[move(1),swap(5,7),swap(3,8),swap(1,7)];L=[move(1),swap(3,8),swap(1,5),swap(5,7)];L=[move(1),swap(3,8),swap(1,7),swap(1,5)];L=[move(1),swap(3,8),swap(5,7),swap(1,7)];L=[swap(5,7),move(1),swap(1,7),swap(3,8)];L=[swap(5,7),move(1),swap(3,8),swap(1,7)];L=[swap(5,7),swap(3,8),move(1),swap(1,7)];L=[swap(3,8),move(1),swap(1,5),swap(5,7)];L=[swap(3,8),move(1),swap(1,7),swap(1,5)];L=[swap(3,8),move(1),swap(5,7),swap(1,7)];L=[swap(3,8),swap(5,7),move(1),swap(1,7)]) + (try_sols(6), not_fails) #"Lista minima generada correctamente".


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Documentacion
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- doc(title, "CPU ANULAR").
:- doc(author, "Jose Manuel Diaz Urraco 170085").
:- doc(author, "Guisell Eliana Mori De La Cruz 160065").
:- doc(author, "Eva Tagarro Lopez de Ayala 170183").

:- doc(module, "Este documento sustituye a la memoria final de la practica. Debido a la instalacion de la nueva version de ciao (1.19.0), no podemos generar el documento pdf a partir de este html. Por lo que entregamos el html directamente como se propuso en una clase en caso de que ocurriera este error.

Esta practica consiste en construir un programa que permita generar automaticamente una lista de instrucciones que induzca a la maquina a transitar desde un estado inicial conocido (es decir, a partir de un conjunto conocido de valores para los registros) hacia un estado final determinado (de nuevo representado por un conjunto de valores conocidos para los registros).

A continuacion, expondremos el codigo utilizado para resolver las tareas planteadas junto con las consultas realizadas para probar su correcto funcionamiento.


@section{Codigo utilizado, explicacion y justificacion de las decisiones}
@subsection{eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos)}
@begin{verbatim}
:- pred eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos)

Devuelve cierto si @var{RegistrosSinComodines/n} es una estructura de tipo reg/n, que resulta de sustituir los comodines que aparecen en el argumento @var{Registros/n} (tambien una estructura de tipo reg/n) por variables. @var{ListaSimbolos} es una lista que contiene todos los simbolos utilizados en el termino @var{Registros/n} en el mismo orden en los que estos aparecen en los registros, permitiendose que haya simbolos repetidos. @includedef{eliminar_comodines/3}
@end{verbatim}

@subsection{Explicacion eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos)}
@begin{verbatim}
El predicado eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) es cierto si se cumplen las condiciones mencionadas anteriormente. Para ello, se ha seguido el siguiente procedimiento:
 1) Se comprueba que @var{Registros} sea una estructura (termino compuesto), que tenga como functor regs y con aridad 2 o mayor.
 2) Se crea una lista @var{L1} que contiene unicamente el contenido de los registros.
 3) Se construye la lista @var{ListaSimbolos} a partir de @var{L1} pero sin añadir los *.
 4) Se crea una lista @var{L2} que contiene como cabeza de la lista el functor y como resto de la lista el contenido de los registros.
 5) Se crea una lista @var{L3} que es quivalente a @var{L2} pero cuando @var{L2} tiene un *, a @var{L3} se le mete _ (variable anonima).
 6) Se construye @var{RegistrosSinComodines} a partir de la lista @var{L3}.
 7) Se comprueba que @var{RegistrosSinComodines} sea la estructura equivalente a @var{Registros} pero con _ en vez de * en los registros.
@end{verbatim}

@subsection{Predicados auxiliares de eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos)}
@begin{verbatim}
:- pred es_regs(R)

Devuelve cierto si @var{R} es un termino compuesto, tiene como functor regs y tiene aridad 2 o mayor. @includedef{es_regs/1}

:- pred listaAtomica(Y)

Devuelve cierto si todos los elementos de la lista @var{Y} son atomic. @includedef{listaAtomica/1}

:- pred crear_lista_regs_sin_functor(R,L)

Devuelve cierto si @var{L} es una lista con todos los componentes de la estructura regs. @includedef{crear_lista_regs_sin_functor/2}

:- pred crear_lista_regs(R,L)

Devuelve cierto si @var{L} es una lista que tiene como cabeza el functor y como resto de la lista todos los componentes de la estructura regs. @includedef{crear_lista_regs/2}

:- pred borrarPrimerElemento(Ls,L)

Devuelve cierto si @var{L} es la lista @var{Ls} sin su primer elemento. @includedef{borrarPrimerElemento/2}

:- pred eliminarComodinesListaSimbolos(L1,L2)

Verifica que @var{L2} es el resultado de eliminar de @var{L1} todas las ocurrencias de comodines (*). @includedef{eliminarComodinesListaSimbolos/2}

:- pred listaRegistrosSinComodines(L1,L2)

Verifica que @var{L2} es el resultado de sustituir en @var{L1} todas las ocurrencias de comodines (*) por variables anonimas (_). @includedef{listaRegistrosSinComodines/2}

:- pred comprobarRegistrosSinComodines(L1,L2)

Devuelve cierto si donde en la lista @var{L1} hay un *, en la @var{L2} hay una variable. @includedef{comprobarRegistrosSinComodines/2}
@end{verbatim}

@subsection{ejecutar_instruccion(EstadoActual,Instruccion,EstadoSiguiente)}
@begin{verbatim}
:- pred ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos)

Devuelve cierto si materializa la transicion entre los estados actual @var{EA} y siguiente @var{ESCompletoConAsteriscos} mediante la ejecucion de una @var{Instruccion}. Dado que el movimiento entre estados se producen mediante la ejecucion de instrucciones. @includedef{ejecutar_instruccion/3}
@end{verbatim}

@subsection{Explicacion ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos)}
@begin{verbatim}
El predicado ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos) es cierto si se cumplen las condiciones mencionadas anteriormente. Para ello, se ha seguido el siguiente procedimiento:
 1) Se llama a eliminar_comodines para verificar que los registros son correctos y prepararlos (sustituyendo * por _) y asi trabajar mas facilmente.
 2) En funcion de si nos llega un move o un swap, ejecutar su correspondiente movimiento copiando un registro en el siguiente (move) o intercambiando los registros (swap). Esta funcion nos devuelve una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el movimiento.
 3) Generamos el estado final al ejecutar el movimiento a partir de la estructura de registros inicial y la que nos ha devuelto el paso anterior.
 4) En el estado final del anterior apartado, sustituimos en una nueva estructura las variables anonimas por * para devolver esa estructura como estado final de la ejecucion del movimiento.
@end{verbatim}

@subsection{Predicados auxiliares de ejecutar_instruccion(EA,Instruccion,ESCompletoConAsteriscos)}
@begin{verbatim}
:- pred movimiento(EASinComodines,move(I),ES)

Devuelve en @var{ES} una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el @var{move}. En este caso, al ser un move, solo NO devolvera variable en el registro que se haya copiado el contenido del registro anterior.
Ya que hablamos de una CPU que cuenta con N registros organizados de forma anular, para el move se han tenido que separar dos casos:
 1) Si se va a hacer el move de un registro que no es el ultimo:
     - Se comprueba que @var{I} es mayor que 0 y menor que length de regs y que @var{I} no es la ultima posicion.
     - Se hace el movimiento cogiendo el elemento en la posicion @var{I} de @var{EASinComodines} y se lo meto a @var{ES} en la pos @var{I+1}.
 2) Si se va a hacer el move del ultimo registro:
     - Mismo algoritmo que en el caso anterior, pero cuando @var{I} es el ultimo registro, se hace el move al primer registro.
@includedef{movimiento/3}

:- pred movimiento(EASinComodines,swap(I,J),ES)

Devuelve en @var{ES} una estructura con variables en todos los registros excepto en los que se ha producido algun cambio al ejecutar el @var{swap}. En este caso, al ser un swap, solo NO devolvera variable en los registro intervinientes en el intercambio de contenidos.
Esta vez, aunque se trate de una CPU que cuenta con N registros organizados de forma anular, en el swap es suficiente contemplar un caso que se cumplira para todos los registros:
  - Se comprueba que @var{I} es distinto que @var{J}.
  - Se comprueba que @var{I} y @var{J} sean mayores que 0 y menores o iguales que length.
  - Se intercambian los registros copiando de @var{EASinComodines} en la pos @var{I} y llevandolo a @var{ES} en la pos @var{J}, y viceversa.
@includedef{movimiento/3}

:- pred completarEstructuraInstruccion(EASinComodines,ES,Pos,Instruccion,ESCompleto)

Genera una nueva estructura @var{ESCompleto} en la que se devuelve el estado final al ejecutar el movimiento a partir de la estructura de registros inicial y la que nos ha devuelto la llamada a @bf{movimiento(EASinComodines,Instruccion,ES)}. El algoritmo es crear una platilla de estructura para almacenar el resultado en @var{ESCompleto} e ir completando dicha estructura con las posiciones alteradas por el move o swap y las que se mantienen igual de un estado a otro.
En el caso de haber ejecutado un @var{move}, separaremos de nuevo en dos casos posibles:
 1) Cuando se ha hecho move de cualquier registro excepto del ultimo.
 2) Cuando se ha hecho el move del ultimo.
@includedef{completarEstructuraInstruccion/5}

:- pred completarEstructuraMove(EASinComodines,ES,Pos,N,ESCompleto)

Completa la estructura final a devolver con el estado actual. Se copia del @var{EA} al @var{ESCompleto} todas las posiciones excepto las alteradas por move. Estas ultimas se copiaran desde el @var{ES} al @var{ESCompleto}. 
El caso base se dara cuando se ha recorrido toda la CPU porque el puntero @var{pos} es mayor que la longitud del registro.
  - Si el contenido del registro @var{pos} no ha sido modificado por move, se reemplaza en @var{ES} la pos por el contenido que tenga @var{EA} en la misma posicion.
  - Si el registro @var{pos} es la posicion modificada por move, se copia de @var{ES} a @var{ESCompleto} lo que hay en @var{pos} y se va al siguiente registro.
@includedef{completarEstructuraMove/5}

:- pred completarEstructuraSwap(EASinComodines,ES,Pos,N1,N2,ESCompleto)

Completa la estructura final a devolver con el estado actual. Se copia del @var{EA} al @var{ESCompleto} todas las posiciones excepto las alteradas por swap. Estas ultimas se copiaran desde el @var{ES} al @var{ESCompleto}.
El caso base se dara cuando se ha recorrido toda la CPU porque el puntero @var{pos} es mayor que la longitud del registro.
  - Si el contenido del registro @var{pos} no ha sido modificado por swap, se reemplaza en @var{ES} la pos por la que tenga @var{EA} en la misma posicion.
  - Si el registro @var{pos} es la posicion modificada por swap (@var{N1} o @var{N2}), se copia de @var{ES} a @var{ESCompleto} lo que hay en @var{pos} y se va al siguiente registro.
@includedef{completarEstructuraSwap/6}

:- pred varAnonimaToAsterisco(ESCompleto,ESCompletoConAsteriscos,Pos)

Devuelve en @var{ESCompletoConAsteriscos} el registro equivalente a sustituir las variables anonimas (_) por * en los registros de @var{ESCompleto}.
El caso base se dara cuando @var{pos} > length.
  - Si en la posicion que estamos hay un _, se sustituye por *.
  - Si en la posicion en la que estamos no hay _, entonces se copia lo que hay en @var{pos} de @var{ESCompleto} a @var{ESCompletoConAsteriscos}.
@includedef{varAnonimaToAsterisco/3}
@end{verbatim}

@subsection{generador_de_codigo(EstadoInicial,EstadoFinal,ListaInstrucciones)}
@begin{verbatim}
:- pred generador_de_codigo(EI,EF,ListaInstrucciones)

Devuelve cierto si @var{ListaInstrucciones} unifica con una lista de instrucciones de la CPU que aplicadas secuencialmente desde el estado inicial @var{EI} de los registros permite transitar hacia el estado final @var{EF} de los registros. Dado que en general existen multiples soluciones para el problema, bastara unicamente con que el programa devuelva una unica solucion valida siempre y cuando esta sea minima. O todas las posibles soluciones minimas existentes. En ningun caso, el programa se debe quedar atrapado en bucles infinitos al devolver alguna solucion. @includedef{generador_de_codigo/3}
@end{verbatim}

@subsection{Explicacion generador_de_codigo(EI,EF,ListaInstrucciones)}
@begin{verbatim}
El predicado generador_de_codigo(EI,EF,ListaInstrucciones) es cierto si se cumplen las condiciones mencionadas anteriormente. Para ello, se ha seguido el siguiente procedimiento:
 1) Se llama a @bf{generador_de_codigo_SOLO_UN_CAMINO}, el cual nos va a devolver UNO de los caminos minimos para esta solucion. Este camino minimo nos sirve para saber el numero de movimientos minimos que hay del estado inicial @var{EI} al final @var{EF}. Asi, cuando queramos obtener todos los caminos minimos, solo generaremos listas de instrucciones con tamaño igual a esta solucion. Este predicado hace exactamente lo mismo que generador_de_codigo_TODOS_LOS_CAMINOS (explicado mas adelante) pero solo encontrando una solucion.
 2) Nos almacenamos el tamaño de la minima solucion para pasarselo como parametro al ''verdadero'' generador_de_codigo (paso 3).
 3) Se llama a @bf{generador_de_codigo_TODOS_LOS_CAMINOS}. Este predicado nos va a devolver todas las soluciones minimas existentes (podria haber varias) sin quedarse atrapado en bucles infinitos.
@end{verbatim}

@subsection{Predicados auxiliares de generador_de_codigo(EI,EF,ListaInstrucciones)}
@begin{verbatim}
:- pred generador_de_codigo_TODOS_LOS_CAMINOS(EISinComodines,EFSinComodines,ListaInstrucciones,TamanoCaminoMinimo)

Saca en @var{ListaInstrucciones} todos los posibles caminos minimos desde el estado inicial @var{EISinComodines} al estado final @var{EFSinComodines}. Se ha seguido el siguiente procedimiento:
  - Como @bf{generador_de_codigo_SOLO_UN_CAMINO} ya comprueba que los registros sean correctos y elimina los comodines tanto del estado inicial como del final, este generador_de_codigo_TODOS_LOS_CAMINOS no vuelve a hacer esas comprobaciones. Y @bf{generador_de_codigo_SOLO_UN_CAMINO} nos pasa los estados inicial y final sin comodines (en el anterior predicado).
  - Lo unico que hacemos es calcular el numero de registros y llamar a @bf{buscarSolucion} para encontrar todas las posibles soluciones de caminos minimos cuyo procedimiento esta explicado junto al predicado. En @bf{buscarSolucion}, en este caso, arrastraremos el numero de @var{TamanoCaminoMinimo} para unicamente calcular los recorridos minimos y descartar todos los demas.
@includedef{generador_de_codigo_TODOS_LOS_CAMINOS/4}

:- pred generador_de_codigo_SOLO_UN_CAMINO(EI,EF,ListaInstrucciones,EISinComodines,EFSinComodines)

Tiene como funcionalidad la misma que generador_de_codigo_TODOS_LOS_CAMINOS pero sacando solo la primera solucion (mediante un corte). Sirve para que a partir de este se puedan sacar en generador_de_codigo_TODOS_LOS_CAMINOS SOLO los caminos minimos. En este, ademas, se comprueba que los registros sean correctos y se eliminan los comodines tanto del estado inicial @var{EI} como del final @var{EF}. Y usaremos estos como parametros de salida para generador_de_codigo_TODOS_LOS_CAMINOS no tenga que volver a calcularlos y hacer las comprobaciones necesarias. Ademas, se comprueba que tanto la estructura de registros inicial como final tengan el mismo numero de registros. @includedef{generador_de_codigo_SOLO_UN_CAMINO/5}

:- pred comprobarSolucion(EF,_ETemporal,Pos)

Comprueba que la solucion sea valida:
 1) @var{Pos} siempre se inicializa a 1 al llamar a este  predicado. Quiere decir que empezamos a comparar desde el registro numero 1.
 2) Si el registro final @var{EF} tiene un elemento que no es variable, en la posible solucion @var{ETemporal} debe aparecer el mismo en la misma posicion.
 3) Si el registro final @var{EF} tiene un elemento que si es variable, como no nos importa el contenido que haya en la posible solucion, aumentamos el contador @var{Pos} para pasar al siguiente registro y seguir comprobando si la solucion es valida.
@includedef{comprobarSolucion/3}

:- pred miembro(X,L)

Se verifica si @var{X} es miembro de la lista @var{L}. @includedef{miembro/2}

:- pred comprobarAlfabetoRegistros(Inicial,[X|Y])

Tiene como entrada una lista de contenidos de registros inicial @var{Inicial} y otra lista de contenidos de registros final @var{[X|Y]}. Se verifica si todos los elementos que hay en la lista final estan en la inicial. @includedef{comprobarAlfabetoRegistros/2}

:- pred buscarSolucion(EI,EF,N,ListaInstrucciones,TamanoCaminoMinimo)

Predicado unicamente usado por generador_de_codigo_TODOS_LOS_CAMINOS. Una vez que sabemos el minimo numero de movimientos de la solucion, el predicado busca todas las soluciones posibles con la misma longitud. 
Para llevarlo a cabo, se han implementado los siguientes pasos:
 1) Se comprueba que la longitud de la nueva solucion sea menor (cuando se va construyendo) o igual a la minima.
 2) Consigue una nueva posible instruccion a ejecutar (move o swap).
 3) Prepara el estado inicial @var{EI}, y en los registros donde tenga _ se ponen * para poder llamar a @bf{ejecutar_instruccion}.
 4) @bf{Llama a ejecutar_instruccion}.
 5) Al estado siguiente que ha devuelto ejecutar_instruccion, se le vuelven a cambiar los * por _ para poder seguir iterando y sacando mas movimientos.
 6) Se llama recursivamente a @bf{buscarSolucion} para encontrar los siguientes movimientos.
 7) Los casos base seran que el estado inicial @var{EI} sea igual al final @var{EF} o cortar las llamadas recursivas cuando estemos buscando una solucion que tenga mas movimientos que el camino minimo.
@includedef{buscarSolucion/5}

:- pred buscarSolucionTamMin(EI,EF,N,ListaInstrucciones)

Predicado unicamente usado por generador_de_codigo_SOLO_UN_CAMINO. Queremos obtener unicamente una solucion para obtener el minimo numero de movimientos de la solucion. Y asi llamar a @bf{generador_de_codigo_TODOS_LOS_CAMINOS} y poder encontrar todas las demas soluciones con el tamaño minimo. La funcionalidad es igual que la de buscarSolucion pero reducida, ya que se llama desde @bf{generar_codigo_SOLO_UN_CAMINO} y ya sabemos que nos va a sacar siempre uno de los caminos minimos.
Para llevarlo a cabo, se han implementado los siguientes pasos:
 1) Consigue una nueva posible instruccion a ejecutar (move o swap).
 2) Prepara el estado inicial @var{EI}, y en los registros donde tenga _ se ponen * para poder llamar a @bf{ejecutar_instruccion}.
 3) @bf{Llama a ejecutar_instruccion}.
 4) Al estado siguiente que ha devuelto ejecutar_instruccion, se le vuelven a cambiar los * por _ para poder seguir iterando y sacando mas movimietos.
 5) Se llama recursivamente a @bf{buscarSolucion} para encontrar los siguientes moovimientos.
 6) En el caso base sera que el estado inicial @var{EI} sea igual al final @var{EF}.
@includedef{buscarSolucionTamMin/4}

:- pred eliminar_comodines2(Registros, RegistrosSinComodines)

Predicado simplificado de eliminar_comodines, ya que no hace las comprobaciones necesarias en los registros porque se han hecho al inicio de generador_de_codigo. Lo unico que hace es preparar los registros para seguir con la ejecucion. Es decir, convierte todos los * en _. @includedef{eliminar_comodines2/2}

:- pred generarNuevaInstruccion(N,Instruccion)

Consigue una nueva posible instruccion a ejecutar. Primero obtiene todos los posibles move y luego todos los posibles swap. Se llama a un predicado que los obtiene obtenerPosibleMove/Swap y otro que crea el literal del movimiento de cada uno de los obtenidos creaLiteralMove/Swap. @includedef{generarNuevaInstruccion/2}

:- pred obtenerPosibleMove(N,NumMove)

Obtiene un posible movimiento move a partir del numero de registros para ese registro. Va en orden decreciente hasta que llega a 1 y termina (caso base). @includedef{obtenerPosibleMove/2}

:- pred obtenerPosibleSwap(N,X,Y)

Obtiene un posible movimiento swap a partir del numero de registros para ese registro. Obtiene las combinaciones posibles de swap desde @var{Y} hacia todos los registros que le quedan a la derecha (fin del registro: @var{X}). @includedef{obtenerPosibleSwap/3}

:- pred combinacionesSwap(A,B,C)

Obtiene todos los posibles movimientos de tipo swap. Empezando por @var{A} (que siempre es 1), va a dar las posibles combinaciones de swap con @var{B}, que van a ser siempre por la izquierda. Es decir, para @var{B}=4, nos dara 1, 2 y 3. Que son los swaps posibles de @var{B} por su izquierda. Los swaps de @var{B} por su derecha los daran posteriormente los elementos que esten a su derecha. @includedef{combinacionesSwap/3}

:- pred creaLiteralMove(N,move(N))

Hecho que genera la estructura del literal @var{move(i)} donde @var{i} es @var{N}. Sirve para añadirlo a la lista de Instrucciones. @includedef{creaLiteralMove/2}

:- pred creaLiteralSwap(N1,N2,swap(N1,N2))

Hecho que genera la estructura del literal @var{swap(i,j)} donde @var{i} y @var{j} son los registros a intercambiar. Sirve para añadirlo a la lista de Instrucciones. @includedef{creaLiteralSwap/3}
@end{verbatim}

@section{Consultas realizadas}
@subsection{eliminar_comodines(X,R,L)}
@begin{verbatim}
Se comprueba que da fallo cuando la CPU tiene menos de 2 registros

:- test eliminar_comodines(X,R,L) : (X=regs(1)) + fails #''La CPU tiene que tener de 2 a N registros''.

Se comprueba que no da fallo cuando todos los registros tienen constantes

:- test eliminar_comodines(X,R,L) : (X=regs(12,3,4,a,t,+,*,p)) + not_fails #''Registros de la CPU correctos''.

Se comprueba que da fallo cuando algun registro tiene una variable

:- test eliminar_comodines(X,R,L) : (X=regs(1,32,X,u,i9)) + fails #''Algun registro de la CPU tiene una variable''.

Se comprueba que no da fallo cuando no hay variables

:- test eliminar_comodines(X,R,L) : (X=regs(!,2)) + not_fails #''Registros de la CPU correctos''.

Se comprueba que da fallo cuando algun registro tiene un elemento que no es una constante

:- test eliminar_comodines(X,R,L) : (X=regs(1,32,4<5)) + fails #''Algun registro de la CPU tiene un elemento que no es una constante''.

Se comprueba que da fallo cuando no se elimina el comodin

:- test eliminar_comodines(X,R,L) : (X=regs(0,*),R=regs(0,*)) + fails #''No se ha eliminado el comodin''.

Se comprueba que da fallo cuando no se elimina el comodin

:- test eliminar_comodines(X,R,L) : (X=regs(*,0),R=regs(*,0)) + fails #''No se ha eliminado el comodin''.

Se comprueba que da fallo cuando no se elimina el comodin

:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*),R=regs(0,1,4,+,2,*)) + fails #''No se ha eliminado el comodin''.

Se comprueba que da fallo cuando no se elimina el comodin

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(*,1,4,+,2,3)) + fails #''No se ha eliminado el comodin''.

Se comprueba que da fallo cuando no se eliminan todos los comodines

:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_,*)) + fails #''No se han eliminado todos los comodines''.

Se comprueba que da fallo cuando no se eliminan todos los comodines

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,W,*)) + fails #''No se han eliminado todos los comodines''.

Se comprueba que da fallo cuando no se eliminan todos los comodines

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(*,0,0,_L)) + fails #''No se han eliminado todos los comodines''.

Se comprueba que da fallo cuando no se eliminan todos los comodines

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(*,1,*,+,2,*)) + fails #''No se han eliminado todos los comodines''.

Se comprueba que da fallo cuando no se sustituye el comodin por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(0,*),R=regs(0,a)) + fails #''No se ha sustituido el comodin por una variable''.

Se comprueba que da fallo cuando no se sustituye el comodin por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,0),R=regs(1,0)) + fails #''No se ha sustituido el comodin por una variable''.

Se comprueba que da fallo cuando no se sustituye el comodin por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*),R=regs(0,1,4,+,2,<)) + fails #''No se ha sustituido el comodin por una variable''.

Se comprueba que no da fallo cuando se sustituye el comodin por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3)) => (R=regs(_,1,4,+,2,3)) + not_fails #''Se ha sustituido por variable''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,*)) => (R=regs(_,_)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*)) => (R=regs(0,_,_)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*)) => (R=regs(_,0,0,_)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*)) => (R=regs(_,1,_,+,2,_)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituye el comodin por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(_,1,4,+,2,3)) + not_fails #''Se ha sustituido por variable''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_Z,_)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,_Hola,Z)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(P,0,0,_)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se sustituyen los comodines por una variable

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(_Ea,1,_,+,2,W)) + not_fails #''Se han sustituido por variables''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(1,1,+,5,*)) => (R=regs(1,1,+,5,_),L=[1,1,+,5]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(0,*)) => (R=regs(0,_),L=[0]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,0)) => (R=regs(_,0),L=[0]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*)) => (R=regs(0,1,4,+,2,_),L=[0,1,4,+,2]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3)) => (R=regs(_,1,4,+,2,3),L=[1,4,+,2,3]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,*)) => (R=regs(_,_),L=[]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*)) => (R=regs(0,_,_),L=[0]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*)) => (R=regs(_,0,0,_),L=[0,0]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*)) => (R=regs(_,1,_,+,2,_),L=[1,+,2]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3)) => (R=regs(_,1,4,+,2,3),L=[1,4,+,2,3]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,*)) => (R=regs(_Z,_),L=[]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*)) => (R=regs(0,_Hola,Z),L=[0]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*)) => (R=regs(P,0,0,_),L=[0,0]) + not_fails #''Lista generada correctamente''.

Se comprueba que no da fallo cuando se genera la lista correctamente

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*)) => (R=regs(_Ea,1,_,+,2,W),L=[1,+,2]) + not_fails #''Lista generada correctamente''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(1,1,+,5,*),R=regs(1,1,+,5,_),L=[1,1,+]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(0,*),R=regs(0,_),L=[0,1]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,0),R=regs(_,0),L=[0,2]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(0,1,4,+,2,*),R=regs(0,1,4,+,2,_),L=[0,1,4,+,2,3]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(_,1,4,+,2,3),L=[1,4,+,2]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_,_),L=[1]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,_,_),L=[]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(_,0,0,_),L=[0,0,3]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(_,1,_,+,2,_),L=[1,+,2,5]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,4,+,2,3),R=regs(_,1,4,+,2,3),L=[1,4,+,2]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,*),R=regs(_Z,_),L=[1]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(0,*,*),R=regs(0,_Hola,Z),L=[0,5]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,0,0,*),R=regs(P,0,0,_),L=[0,0,0]) + fails #''Lista generada de forma incorrecta''.

Se comprueba que da fallo cuando se genera la lista

:- test eliminar_comodines(X,R,L) : (X=regs(*,1,*,+,2,*),R=regs(_Ea,1,_,+,2,W),L=[1,+,2,0]) + fails #''Lista generada de forma incorrecta''.
@end{verbatim}

@subsection{ejecutar_instruccion(EA,I,ES)}
@begin{verbatim}
Se comprueba que da fallo cuando la CPU tiene menos de 2 registros

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1)) + fails #''La CPU tiene que tener de 2 a N registros''.

Se comprueba que no da fallo cuando todos los registros tienen constantes

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(12,3,4,a,t,+,*,p),I=move(1)) + not_fails #''Registros de la CPU correctos''.

Se comprueba que da fallo cuando algun registro tiene una variable

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,32,X,u,i9),I=swap(1,7)) + fails #''Algun registro de la CPU tiene una variable''.

Se comprueba que no da fallo cuando no hay variables

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(!,2),I=swap(1,2)) + not_fails #''Registros de la CPU correctos''.

Se comprueba que da fallo cuando algun registro tiene un elemento que no es una constante

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,32,4<5),I=move(1)) + fails #''Algun registro de la CPU tiene un elemento que no es una constante''.

Se comprueba que da fallo cuando se meten parametros al swap que no son numeros

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,a)) + fails #''Parametro no valido en swap''.

Se comprueba que da fallo cuando se meten parametros al swap que no son numeros

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(b,2)) + fails #''Parametro no valido en swap''.

Se comprueba que da fallo cuando se meten parametros al swap que no son numeros

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,'a')) + fails #''Parametro no valido en swap''.

Se comprueba que da fallo cuando se meten parametros al swap que no son numeros

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,''a'')) + fails #''Parametro no valido en swap''.

Se comprueba que da fallo cuando se meten mas de 2 numeros al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,2,4)) + fails #''Swap solo tiene 2 parametros''.

Se comprueba que da fallo cuando se mete solo 1 numero al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1)) + fails #''Swap necesita 2 parametros''.

Se comprueba que da fallo cuando primer parametro es igual que el segundo en swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(5,5)) + fails #''i tiene que ser menor que j en swap''.

Se comprueba que da fallo cuando se mete 0 al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(0,1)) + fails #''No hay registro 0''.

Se comprueba que da fallo cuando se mete 1 numero negativo al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(-1,1)) + fails #''No hay registros negativos''.

Se comprueba que da fallo cuando se mete algun numero mayor que el numero de registros al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(5,1)) + fails #''Los numeros de swap tienen que ser menores que el numero de registro''.

Se comprueba que da fallo cuando se mete algun numero mayor que el numero de registros al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(1,5)) + fails #''Los numeros de swap tienen que ser menores que el numero de registro''.

Se comprueba que da fallo cuando se mete algun numero mayor que el numero de registros al swap

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=swap(5,7)) + fails #''Los numeros de swap tienen que ser menores que el numero de registro''.

Se comprueba que da fallo cuando se mete mas de 1 numero al move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(1,2)) + fails #''Move solo tiene 1 parametro''.

Se comprueba que da fallo cuando se mete mas de 1 numero al move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(1,2,3)) + fails #''Move solo tiene 1 parametro''.

Se comprueba que da fallo cuando se mete 1 numero negativo a move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(-1)) + fails #''El numero de move tiene que ser positivo''.

Se comprueba que da fallo cuando se mete 0 a move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(0)) + fails #''El numero de move tiene que ser positivo''.

Se comprueba que da fallo cuando se mete 1 numero mayor que numero de registros a move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(4)) + fails #''El numero de move tiene que ser menor que el numero de registros''.

Se comprueba que da fallo cuando se mete 1 parametro que no es un numero al move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(a)) + fails #''Parametro de move solo puede ser 1 numero''.

Se comprueba que da fallo cuando se mete 1 parametro que no es un numero al move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move(''a'')) + fails #''Parametro de move solo puede ser 1 numero''.

Se comprueba que da fallo cuando se mete 1 parametro que no es un numero al move

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,4),I=move('a')) + fails #''Parametro de move solo puede ser 1 numero''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=swap(1,2)) => (ES=regs(2,1)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=swap(2,3)) => (ES=regs(1,<,*)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=swap(1,4)) => (ES=regs(-1,*,<,2)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=swap(1,2)) => (ES=regs(2,1,+,5,*)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=swap(1,2), ES=regs(1,2)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=swap(2,3), ES=regs(*,1,<)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=swap(1,4), ES=regs(*,<,-1,2)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=swap(1,2), ES=regs(*,1,2,5,+)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=move(1)) => (ES=regs(1,1)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=move(2)) => (ES=regs(1,*,*)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<,1), I=move(3)) => (ES=regs(1,*,<,<)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=move(4)) => (ES=regs(-1,*,<,-1)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=move(5)) => (ES=regs(*,2,+,5,*)) + not_fails #''Instruccion ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2), I=move(1), ES=regs(1,2)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,*,<), I=move(3), ES=regs(1,<,1)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(2,*,<,-1), I=move(4), ES=regs(2,*,*,-1)) + fails #''Instruccion no ejecutada correctamente''.

Se comprueba que no se ejecuta la instruccion correctamente

:- test ejecutar_instruccion(EA,I,ES) : (EA=regs(1,2,+,5,*), I=move(2), ES=regs(1,1,+,5,*)) + fails #''Instruccion no ejecutada correctamente''.
@end{verbatim}

@subsection{generador_de_codigo(EI,EF,L)}
@begin{verbatim}
Se comprueba que da fallo cuando EI tiene menos de 2 registros

:- test generador_de_codigo(EI,EF,L) : (EI=regs(1)) + fails  #''EI tiene que tener de 2 a N registros ''.

Se comprueba que da fallo cuando EF tiene menos de 2 registros

:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,2),EF=regs(1)) + fails  #''EF tiene que tener de 2 a N registros ''.

Se comprueba que da fallo cuando algun registro tiene una variable

:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,32,X,u,i9),EF=regs(i9,32,X,u,1)) + fails  #''Algun registro de la CPU tiene una variable''.

Se comprueba que no da fallo cuando no hay variables

:- test generador_de_codigo(EI,EF,L) : (EI=regs(!,2),EF=regs(2,!)) + not_fails  #''Registros de la CPU correctos''.

Se comprueba que da fallo cuando algun registro tiene un elemento que no es una constante

:- test generador_de_codigo(EI,EF,L) : (IA=regs(1,32,4<5),EF=regs(32,1,4<5)) + fails  #''Algun registro de la CPU tiene un elemento que no es una constante''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(<,2),EF=regs(2,<)) => (L = [swap(1,2)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(<,2),EF=regs(*,*)) => (L = []) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(<,2),EF=regs(<,<)) => (L = [move(1)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(*,*),EF=regs(a,b)) + fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c),EF=regs(b,c,b)) => (L =[swap(2,3),move(3)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,c,*),EF=regs(c,a,*)) => (L =[swap(1,2)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,2,3),EF=regs(1,1,1)) => (L =[move(1),move(2)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(1,<,z),EF=regs(<,<,<)) => (L =[move(2),move(3)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c),EF=regs(a,a,*)) => (L =[move(1)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(*,*,*),EF=regs(*,*,*)) => (L =[]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(*,a,*),EF=regs(a,*,*)) => (L =[swap(1,2)]) + not_fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con el tamaño minimo de instrucciones

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c,d,*),EF=regs(a,b,c,d,e)) + fails #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,*,c),EF=regs(c,a,*)) => (L=[move(1),move(3)];L=[move(1),swap(1,3)];L=[swap(1,2),move(3)];L=[swap(1,2),swap(1,3)];L=[swap(1,3),swap(2,3)];L=[swap(2,3),swap(1,2)]) + (try_sols(6), not_fails) #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c,d),EF=regs(a,d,a,b)) => (L=[move(2),move(1),swap(2,3),swap(2,4)];L=[move(2),move(1),swap(2,4),swap(3,4)];L=[move(2),move(1),swap(3,4),swap(2,3)];L=[move(2),swap(3,4),move(1),swap(2,3)];L=[swap(1,2),move(2),swap(1,2),swap(2,4)];L=[swap(1,2),move(2),swap(1,4),swap(1,2)];L=[swap(1,2),move(2),swap(2,4),swap(1,4)];L=[swap(1,2),swap(1,4),move(2),swap(1,2)];L=[swap(2,3),move(1),swap(2,3),swap(2,4)];L=[swap(2,3),move(1),swap(2,4),swap(3,4)];L=[swap(2,3),move(1),swap(3,4),swap(2,3)];L=[swap(2,3),swap(3,4),move(1),swap(2,3)];L=[swap(1,4),swap(2,4),move(2),swap(1,2)];L=[swap(2,4),move(2),move(1),swap(2,3)];L=[swap(2,4),swap(1,2),move(2),swap(1,2)];L=[swap(2,4),swap(2,3),move(1),swap(2,3)];L=[swap(3,4),swap(2,4),move(1),swap(2,3)]) + (try_sols(17), not_fails) #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c),EF=regs(a,a,*)) => (L=[move(1)]) + (try_sols(1), not_fails) #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos

:- test generador_de_codigo(EI,EF,L) : (EI=regs(a,b,c,d,*,e,*),EF=regs(a,*,*,a,b,e,e)) => (L = [move(6),swap(2,5),move(1),swap(2,4)];L=[swap(2,5),move(6),move(1),swap(2,4)];L=[swap(2,5),move(1),move(6),swap(2,4)];L=[swap(2,5),move(1),swap(2,4),move(6)]) + (try_sols(4), not_fails) #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos

:- test generador_de_codigo(EI,EF,L) : (EI=regs(p,r,t,*,*,w,o,w),EF=regs(*,*,*,*,*,*,p,t)) => (L=[swap(1,7),swap(3,8)];L=[swap(3,8),swap(1,7)]) + (try_sols(6), not_fails) #''Lista minima generada correctamente''.

Se comprueba que se genera una lista con todas las soluciones que tienen el tamaño minimo de movimientos

:- test generador_de_codigo(EI,EF,L) : (EI=regs(p,r,t,*,*,w,o,w),EF=regs(*,p,w,*,o,*,p,t)) => (L=[move(1),swap(1,5),swap(5,7),swap(3,8)];L=[move(1),swap(1,5),swap(3,8),swap(5,7)];L=[move(1),swap(1,7),swap(1,5),swap(3,8)];L=[move(1),swap(1,7),swap(3,8),swap(1,5)];L=[move(1),swap(5,7),swap(1,7),swap(3,8)];L=[move(1),swap(5,7),swap(3,8),swap(1,7)];L=[move(1),swap(3,8),swap(1,5),swap(5,7)];L=[move(1),swap(3,8),swap(1,7),swap(1,5)];L=[move(1),swap(3,8),swap(5,7),swap(1,7)];L=[swap(5,7),move(1),swap(1,7),swap(3,8)];L=[swap(5,7),move(1),swap(3,8),swap(1,7)];L=[swap(5,7),swap(3,8),move(1),swap(1,7)];L=[swap(3,8),move(1),swap(1,5),swap(5,7)];L=[swap(3,8),move(1),swap(1,7),swap(1,5)];L=[swap(3,8),move(1),swap(5,7),swap(1,7)];L=[swap(3,8),swap(5,7),move(1),swap(1,7)]) + (try_sols(6), not_fails) #''Lista minima generada correctamente''.
@end{verbatim}

 "). % NO ELIMINAR