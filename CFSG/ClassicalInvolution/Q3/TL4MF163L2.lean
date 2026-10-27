module

public import CFSG.ClassicalInvolution.Q3.TL4MF163Psl
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution

namespace MF163

variable {X : Type} [Group X] [Finite X]

theorem exists_quat_of_member {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) :
    ∃ ι : QuaternionGroup 2 →* X, Function.Injective ι ∧ (∀ g, ι g ∈ tightCore R) ∧
      ι (QuaternionGroup.a 2) = z := by
  obtain ⟨eQ⟩ := hm.cls.1
  let ι : QuaternionGroup 2 →* X :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eQ.symm.toMonoidHom)
  have hι : Function.Injective ι := fun g h hgh =>
    eQ.symm.injective (Subtype.ext (Subtype.ext hgh))
  have hV : IsPGroup 2 ((S : Subgroup R).map R.subtype) := S.isPGroup'.map _
  have hmem : ∀ g, ι g ∈ (S : Subgroup R).map R.subtype := fun g => ⟨_, (eQ.symm g).2, rfl⟩
  refine ⟨ι, hι, fun g => ?_, ?_⟩
  · exact Subgroup.subset_closure ⟨Subgroup.map_subtype_le _ (hmem g),
      hV.to_le (Subgroup.zpowers_le.mpr (hmem g))⟩
  · have h2 : orderOf (ι (QuaternionGroup.a 2)) = 2 := by
      rw [orderOf_injective ι hι]
      exact orderOf_eq_prime (by decide) (by decide)
    exact hm.datum.eq_of_orderOf_eq_two (Subgroup.map_subtype_le _ (hmem _)) h2

end MF163

theorem model163L2_proved : Model163L2 := by
  intro X _ _ R S z hm hs _ p f _ hp2 _ hl β hβ2 hβK
  obtain ⟨ι, hι, hιK, hιz⟩ := MF163.exists_quat_of_member hm
  rw [← hιz]
  exact MF163.eq_one_or_conj_of_quat_psl2 hp2 hl ι hι β hβ2 fun g => hβK _ (hιK g)

end CFSG.ClassicalInvolution.Q3.TL4
