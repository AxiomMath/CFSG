module

public import CFSG.ClassicalInvolution.Q3.TL4MF163Psl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint

theorem model163L2Q8_proved :
    ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f → p ^ f ≠ 9 →
        LieModel (FStarQuot X) .PSL 2 p f →
        ∀ (P : Subgroup X) (e : ↥P ≃* QuaternionGroup 2) (β : MulAut X), β * β = 1 →
          (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj ((e.symm (QuaternionGroup.a 2) : ↥P) : X) := by
  intro X _ _ hs _ p f _ hp2 _ _ hl P e β hβ2 hβP
  have := hs
  exact MF163.eq_one_or_conj_of_quat_psl2 hp2 hl (P.subtype.comp e.symm.toMonoidHom)
    (fun g h hgh => e.symm.injective (Subtype.ext hgh)) β hβ2 fun g => hβP _ (e.symm g).2

end CFSG.ClassicalInvolution.Q3.TL4
