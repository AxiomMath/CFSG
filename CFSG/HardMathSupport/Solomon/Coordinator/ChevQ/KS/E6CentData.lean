module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  TwE6UniqAbs

@[expose] def cls (β : Fin Tag.E6.rank → ℤ) : Fin 3 :=
  if β 1 ≠ 0 then 2 else if β 0 ≠ 0 ∨ β 2 ≠ 0 then 0 else 1

@[expose] def b3 : Fin 6 → (Fin Tag.E6.rank → ℤ) :=
  ![Pi.single 0 1, Pi.single 2 1, Pi.single 4 1, Pi.single 5 1, Pi.single 1 1,
    -(![1, 2, 2, 3, 2, 1] : Fin Tag.E6.rank → ℤ)]

@[expose] def B3inv : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, 1, 0, 0, 0; 1, 0, 2, 0, 0, 0; 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 1, 2;
    -1, 0, -2, -3, -2, -1; -2, -3, -4, -6, -4, -2]

theorem cls_respects : ∀ β ∈ R6, 3 ∣ β 3 → ∀ β' ∈ R6, 3 ∣ β' 3 →
    iform β β' ≠ 0 → cls β = cls β' := by
  decide +kernel

theorem cls_connected : ∀ β ∈ R6, 3 ∣ β 3 → ∀ β' ∈ R6, 3 ∣ β' 3 →
    cls β = cls β' → iform β β' ≠ 0 := by
  decide +kernel

theorem cls_surj : ∀ k : Fin 3, ∃ β ∈ R6, 3 ∣ β 3 ∧ cls β = k := by
  decide +kernel

theorem card_cls (k : Fin 3) :
    (R6.filter fun β => 3 ∣ β 3 ∧ cls β = k).length = 6 := by
  revert k
  decide +kernel

theorem b3_mul_B3inv (j j' : Fin 6) :
    ∑ b, iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (b3 b) * B3inv b j' =
      if j = j' then 3 else 0 := by
  revert j j'
  decide +kernel

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
