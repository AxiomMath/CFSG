module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6SylowC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313U

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

theorem gms61CaseOneC
    (hF : Foundation) : GMS61CaseOneC := by
  intro G _ _ L T K f hf he h3 hKL hKo hKH gb hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  have h313 := h3.lemma313_of_psu3 hF hf e
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  obtain ⟨-, -, hAX', -, -, -, -, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  have hP := h3.isSylowOf_T₁
  obtain ⟨-, hA₁card, hA₁sq, -⟩ := sylow_of_psu3 hZ hf e hP
  set G₁ := centralizer (K : Set G)
  set O := standardComponentOddCore G₁
  set π := QuotientGroup.mk' O
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  set A₁ := gmsA L T with hA₁def
  set X₀ := u3X₀ L K with hX₀def
  have hX₀G₁ : X₀ ≤ G₁ := by
    refine (commutator_le).mpr fun x hx y hy => ?_
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).2 (mem_inf.mp hy).2)
      (inv_mem (mem_inf.mp hx).2)) (inv_mem (mem_inf.mp hy).2)
  have hA₁X₀ : A₁ ≤ X₀ := hAX'.trans (commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O gb
  set Ag : Subgroup G := A₁.map (MulAut.conj (g : G)).toMonoidHom with hAgdef
  have hAgŶ : Ag ≤ u3X₀CentralizerPre L K := by
    rintro _ ⟨a, ha, rfl⟩
    have haG₁ : a ∈ G₁ := hX₀G₁ (hA₁X₀ ha)
    refine ⟨g * ⟨a, haG₁⟩ * g⁻¹, ?_, rfl⟩
    show π (g * ⟨a, haG₁⟩ * g⁻¹) ∈ u3X₀CentralizerC L K
    rw [mem_centralizer_iff]
    intro x hx
    have h1 : π (g * ⟨a, haG₁⟩ * g⁻¹) ∈
        (oddQuotImageC K X₀).map (MulAut.conj (π g)).toMonoidHom := by
      refine ⟨π ⟨a, haG₁⟩, ⟨⟨a, haG₁⟩, hA₁X₀ ha, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    have h2 := Subgroup.commutator_mem_commutator hx h1
    rw [hcomm, mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hsyl := h3.isSylowOf_T₀_centralizerPre hf e hKL hKo hKH
  have hAg2 : IsPGroup 2 Ag := (hP.isPGroup.to_le inf_le_left).map _
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hsyl hAgŶ hAg2
  have hone : ∀ a ∈ A₁, a = 1 := by
    intro a ha
    have h1 := hk _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : k * (g : G) * a * (k * (g : G))⁻¹ ∈ T₀ := by
      have e1 : k * (g : G) * a * (k * (g : G))⁻¹ = k * ((g : G) * a * (g : G)⁻¹) * k⁻¹ := by
        group
      rw [e1]
      exact h1
    have h3' : k * (g : G) * a * (k * (g : G))⁻¹ ∈ A₁ :=
      h313.stronglyClosed a ha _ (mem_sup_right h2)
    have hxL : k * (g : G) * a * (k * (g : G))⁻¹ ∈ L := (mem_inf.mp (mem_inf.mp h3').1).2
    have hxZ : (⟨_, hxL⟩ : L) ∈ center L :=
      mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp (mem_inf.mp h2).2 y y.2)
    have hx2 : (⟨_, hxL⟩ : L) ^ 2 ^ 1 = 1 := Subtype.ext (by
      rw [pow_one]
      exact hA₁sq _ h3')
    have hx1 := congrArg Subtype.val (eq_one_of_pow_two_pow_of_mem_odd hZ hxZ hx2)
    calc a = (k * (g : G))⁻¹ * (k * (g : G) * a * (k * (g : G))⁻¹) * (k * (g : G)) := by group
      _ = 1 := by
        rw [show k * (g : G) * a * (k * (g : G))⁻¹ = 1 from hx1]
        group
  have hbot : A₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hone
  have h1 : Nat.card A₁ = 1 := by rw [hbot, card_bot]
  have h2 : Nat.card A₁ = 2 ^ f := hA₁card
  have h3'' : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  omega

end CFSG.ComponentClassification.GMS78
