module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTree

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

@[expose] def starTree : Tree 4 :=
  (.branch ⟨(2, true), 1⟩ ⟨(3, true), 1⟩
    (.collapse 200000)
    (.collapse 200000)
    (.collapse 200000)
    (.success ⟨(2, true), 1⟩)
    (.branch ⟨(0, true), 1⟩ ⟨(3, true), 1⟩
      (.collapse 200000)
      (.collapse 200000)
      (.collapse 200000)
      (.branch ⟨(1, true), 1⟩ ⟨(3, true), 1⟩
        (.collapse 200000)
        (.collapse 200000)
        (.collapse 200000)
        (.branch ⟨(0, true), 1⟩ ⟨(3, true), FreeGroup.mk [(0, false)]⟩
          (.collapse 200000)
          (.collapse 200000)
          (.collapse 200000)
          (.branch ⟨(0, true), 1⟩ ⟨(3, true), FreeGroup.mk [(1, false)]⟩
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.branch ⟨(0, true), 1⟩ ⟨(3, true), FreeGroup.mk [(2, false)]⟩
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)))
          (.collapse 200000)
          (.collapse 200000))
        (.collapse 200000)
        (.collapse 200000))
      (.collapse 200000)
      (.collapse 200000))
    (.branch ⟨(0, true), 1⟩ ⟨(3, true), 1⟩
      (.collapse 200000)
      (.collapse 200000)
      (.collapse 200000)
      (.branch ⟨(1, true), 1⟩ ⟨(3, true), 1⟩
        (.collapse 200000)
        (.collapse 200000)
        (.collapse 200000)
        (.branch ⟨(0, true), 1⟩ ⟨(3, true), FreeGroup.mk [(0, false)]⟩
          (.collapse 200000)
          (.collapse 200000)
          (.collapse 200000)
          (.branch ⟨(0, true), 1⟩ ⟨(3, true), FreeGroup.mk [(1, false)]⟩
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.branch ⟨(0, true), 1⟩ ⟨(3, true), FreeGroup.mk [(2, false)]⟩
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)
              (.collapse 200000)))
          (.collapse 200000)
          (.collapse 200000))
        (.collapse 200000)
        (.collapse 200000))
      (.collapse 200000)
      (.collapse 200000)))

@[expose] def starRels : List (FreeGroup (Fin 4)) :=
  [(FreeGroup.of (0 : Fin 4)) ^ 3, (FreeGroup.of (1 : Fin 4)) ^ 3, (FreeGroup.of (2 : Fin 4)) ^ 3, (FreeGroup.of (3 : Fin 4)) ^ 3,
    (FreeGroup.of (0 : Fin 4) * FreeGroup.of (1 : Fin 4)) ^ 2, (FreeGroup.of (0 : Fin 4) * FreeGroup.of (2 : Fin 4)) ^ 2, (FreeGroup.of (1 : Fin 4) * FreeGroup.of (2 : Fin 4)) ^ 2,
    (FreeGroup.of (0 : Fin 4) * FreeGroup.of (3 : Fin 4)) ^ 2, (FreeGroup.of (1 : Fin 4) * FreeGroup.of (3 : Fin 4)) ^ 2]

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
