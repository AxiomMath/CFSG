module

public import CFSG.LieType.SeitzGeneration.HeisSmallSound

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

variable {R : Type}

@[expose] def ofMat (A : Matrix (Fin 3) (Fin 3) R) : M3 R :=
  ⟨A 0 0, A 0 1, A 0 2, A 1 0, A 1 1, A 1 2, A 2 0, A 2 1, A 2 2⟩

theorem toMat_id_ofMat {L : Type} [Field L] (A : Matrix (Fin 3) (Fin 3) L) :
    toMat (RingHom.id L) (ofMat A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_injective {L K : Type} [Field L] [Field K] {ι : L →+* K}
    (hι : Function.Injective ι) : Function.Injective (toMat ι) := by
  have hof : ∀ A : M3 L, ofMat (toMat (RingHom.id L) A) = A := by
    intro A
    ext <;> rfl
  have hmapid : ∀ A : M3 L, toMat ι A = (toMat (RingHom.id L) A).map ι := by
    intro A
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hid : Function.Injective (toMat (RingHom.id L)) := by
    intro A B hAB
    have h' := congrArg ofMat hAB
    rwa [hof A, hof B] at h'
  have hmap : Function.Injective (fun A : Matrix (Fin 3) (Fin 3) L => A.map ι) := by
    intro A B hAB
    ext i j
    exact hι (by simpa [Matrix.map] using congrFun (congrFun hAB i) j)
  intro A B h
  apply hid
  apply hmap
  change (toMat (RingHom.id L) A).map ι = (toMat (RingHom.id L) B).map ι
  rw [← hmapid A, ← hmapid B]
  exact h

end CFSG.LieType.SeitzGeneration.HeisSmall
