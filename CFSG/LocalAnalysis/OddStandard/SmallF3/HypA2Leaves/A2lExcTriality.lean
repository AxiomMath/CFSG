module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (Shape)

open CFSG.GH74.GLS.IVK.GHInv (exists_shape_D4 isQuasisimple_sl2 normal_I₁)


section Shape

variable {X : Type} [Group X] {z : X} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem a2l_datum_of_shape [Finite X] [Finite F₁] (hz : orderOf z = 2)
    (S : Shape ↥(centralizer ({z} : Set X)) F₁ F₂) (hSz : (S.z : X) = z)
    (hodd : Odd (Nat.card F₁)) (h9 : 9 ≤ Nat.card F₁) : a2lDatum X := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  let T : Subgroup X := S.I₁.map (centralizer ({z} : Set X)).subtype
  let e : ↥T ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    (S.I₁.equivMapOfInjective _ Subtype.val_injective).symm.trans S.e₁
  have hzT : z ∈ T := ⟨S.z, S.z_mem₁, hSz⟩
  have hTc : T ≤ centralizer ({z} : Set X) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hJn : ∀ g ∈ centralizer ({z} : Set X), ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (normal_I₁ S).conj_mem y hy ⟨g, hg⟩, rfl⟩
  have hJq : CFSG.IsQuasisimple ↥T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 (by omega))
  have hN : HarrisLit.IsSLTwoOver (Nat.card F₁) ↥T := by
    haveI := Fintype.ofFinite F₁
    exact ⟨F₁, inferInstance, inferInstance, Nat.card_eq_fintype_card.symm, ⟨e⟩⟩
  refine a2lDatum_of_block_normal (P := X) (S := X) (MonoidHom.id X) Function.surjective_id ?_
    hodd (by omega) hz2 hz1 (J := T) (N := T) le_rfl hzT hTc hJn hJq (fun x _ h => h) hN
    (a2l_typU_of_isSLTwoOver hodd h9 hN)
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact one_mem _

end Shape

section Triality


theorem a2lRowTrialityD4_holds : a2lRowTrialityD4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro X _ _ f hX
  have hf : 1 ≤ f := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.one_le_of_lieModel_D4 hX
  obtain ⟨φ⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_concrete (p := 3) (f := f)
    (by norm_num) hX
  have hD := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.d4Data_sig0 (p := 3) (f := f) (by norm_num) hf
  have hz : orderOf (φ.symm (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.τL hD.sigma3)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.orderOf_tauL hD.sigma3 hD.neg_one
  obtain ⟨F₁, F₂, _, _, _, _, S, hc₁, -, hSz⟩ :=
    exists_shape_D4 Nat.prime_three (by norm_num) hX _ hz
  have h3 : 3 ≤ 3 ^ f := Nat.le_self_pow (by omega) 3
  refine a2l_datum_of_shape hz S hSz ?_ ?_
  · rw [hc₁]
    exact (Odd.pow (by decide : Odd 3)).pow
  · rw [hc₁]
    calc 9 ≤ 3 ^ 3 := by norm_num
      _ ≤ (3 ^ f) ^ 3 := Nat.pow_le_pow_left h3 3

end Triality

end CFSG.OddStandard.SmallF3.HypA2Leaves
