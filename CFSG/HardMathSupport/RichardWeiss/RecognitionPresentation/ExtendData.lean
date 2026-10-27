module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTree

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

@[expose] def extendTree : Tree 4 :=
  (.branch ⟨(1, true), 1⟩ ⟨(3, true), 1⟩
    (.collapse 200000)
    (.collapse 200000)
    (.collapse 200000)
    (.success ⟨(1, true), 1⟩)
    (.branch ⟨(2, true), 1⟩ ⟨(3, true), 1⟩
      (.collapse 200000)
      (.collapse 200000)
      (.collapse 200000)
      (.success ⟨(2, true), 1⟩)
      (.branch ⟨(1, true), FreeGroup.mk [(0, true)]⟩ ⟨(3, true), 1⟩
        (.collapse 200000)
        (.collapse 200000)
        (.collapse 200000)
        (.success ⟨(1, true), FreeGroup.mk [(0, true)]⟩)
        (.collapse 200000)
        (.collapse 200000))
      (.branch ⟨(1, true), FreeGroup.mk [(0, true)]⟩ ⟨(3, true), 1⟩
        (.collapse 200000)
        (.collapse 200000)
        (.collapse 200000)
        (.success ⟨(1, true), FreeGroup.mk [(0, true)]⟩)
        (.branch ⟨(2, true), FreeGroup.mk [(0, true)]⟩ ⟨(3, true), 1⟩
          (.collapse 200000)
          (.collapse 200000)
          (.collapse 200000)
          (.success ⟨(2, true), FreeGroup.mk [(0, true)]⟩)
          (.collapse 200000)
          (.collapse 200000))
        (.collapse 200000)))
    (.branch ⟨(2, true), 1⟩ ⟨(3, true), 1⟩
      (.collapse 200000)
      (.collapse 200000)
      (.collapse 200000)
      (.success ⟨(2, true), 1⟩)
      (.branch ⟨(1, true), FreeGroup.mk [(0, true)]⟩ ⟨(3, true), 1⟩
        (.collapse 200000)
        (.collapse 200000)
        (.collapse 200000)
        (.success ⟨(1, true), FreeGroup.mk [(0, true)]⟩)
        (.collapse 200000)
        (.collapse 200000))
      (.branch ⟨(1, true), FreeGroup.mk [(0, true)]⟩ ⟨(3, true), 1⟩
        (.collapse 200000)
        (.collapse 200000)
        (.collapse 200000)
        (.success ⟨(1, true), FreeGroup.mk [(0, true)]⟩)
        (.collapse 200000)
        (.branch ⟨(2, true), FreeGroup.mk [(0, true)]⟩ ⟨(3, true), 1⟩
          (.collapse 200000)
          (.collapse 200000)
          (.collapse 200000)
          (.success ⟨(2, true), FreeGroup.mk [(0, true)]⟩)
          (.collapse 200000)
          (.branch ⟨(1, true), FreeGroup.mk [(0, false)]⟩ ⟨(3, true), 1⟩
            (.collapse 200000)
            (.collapse 200000)
            (.collapse 200000)
            (.success ⟨(1, true), FreeGroup.mk [(0, false)]⟩)
            (.collapse 200000)
            (.collapse 200000))))))

@[expose] def extendRels : List (FreeGroup (Fin 4)) :=
  [(FreeGroup.of (0 : Fin 4)) ^ 3, (FreeGroup.of (1 : Fin 4)) ^ 3, (FreeGroup.of (2 : Fin 4)) ^ 3, (FreeGroup.of (3 : Fin 4)) ^ 3,
    (FreeGroup.of (0 : Fin 4) * FreeGroup.of (1 : Fin 4)) ^ 2, (FreeGroup.of (0 : Fin 4) * FreeGroup.of (2 : Fin 4)) ^ 2, (FreeGroup.of (1 : Fin 4) * FreeGroup.of (2 : Fin 4)) ^ 2,
    (FreeGroup.of (0 : Fin 4) * FreeGroup.of (3 : Fin 4)) ^ 2]

@[expose] def extendSucc : List (CDesc 4) :=
  [⟨(1, true), 1⟩, ⟨(2, true), 1⟩, ⟨(1, true), FreeGroup.mk [(0, true)]⟩,
    ⟨(2, true), FreeGroup.mk [(0, true)]⟩, ⟨(1, true), FreeGroup.mk [(0, false)]⟩,
    ⟨(2, true), FreeGroup.mk [(0, false)]⟩]

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
