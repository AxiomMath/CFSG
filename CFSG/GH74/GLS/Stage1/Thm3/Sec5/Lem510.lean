module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem conj_mem_Qof {K : Subgroup G} {b : G} (hbS : b ∈ S) (hbn : b ∈ normalizer (K : Set G))
    {q : G} (hq : q ∈ Qof S K) : b * q * b⁻¹ ∈ Qof S K :=
  ⟨S.mul_mem (S.mul_mem hbS hq.1) (S.inv_mem hbS), cSec_conj K hbn hq.2⟩

theorem claimA (hII : II4_4_4_center) (hsq : IVK_f_sq) (hin : IVK_f_inner) (hco : IVK_f_coset)
    (hce : IVK_f_cent) (hnc : P_noncyclic) (hq2 : TwoGroup_coset_sq)
    (h : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z) (hm₁ : pRank 2 ↥(Qof S K₁) = 1)
    {b : G} (hbS : b ∈ S) (hb2 : b * b ∈ Rz S z) (hfb : InducesFAut b K₁) (hnb : b ∉ cSec K₁) :
    ∃ a₀ ∈ S, orderOf a₀ = 2 ∧ InducesFAut a₀ K₁ ∧ a₀ ∉ cSec K₁ := by
  have hM := m4_of_std hII h
  have hK₁ : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hK₂ : K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  have hbn : b ∈ normalizer (K₁ : Set G) := hfb.1
  have hzP : z ∈ Pz S z := by
    rw [Pz_eq h]; exact hM.z_mem_P
  have hR : Rz S z = Pz S z := by
    unfold Rz; rw [hQ]; exact sup_eq_left.2 (zpowers_le.2 hzP)
  have hbP : b * b ∈ Pz S z := by rwa [hR] at hb2
  have hbK : b * b ∈ K₁ ⊔ K₂ := by
    have : b * b ∈ M.Pm S K₁ K₂ := by rwa [Pz_eq h] at hbP
    exact this.2
  have hbb : b * b ∈ innSub K₁ := by
    have hle : K₁ ⊔ K₂ ≤ innSub K₁ :=
      sup_le (le_innSub K₁) (fun x hx => cSec_le_innSub K₁ (hM.cs₁ hx))
    exact hle hbK
  have hbbc : b * b ∈ cSec K₁ := hsq G z S K₁ K₂ h K₁ hK₁ b hfb hbb
  have hbbQ : b * b ∈ Qof S K₁ := ⟨mul_mem hbS hbS, hbbc⟩
  have hbQ : b ∉ Qof S K₁ := fun hmem => hnb hmem.2
  have hb_norm : b ∈ normalizer ((Qof S K₁ : Subgroup G) : Set G) :=
    M.mem_normalizer_of_both (fun q hq => conj_mem_Qof hbS hbn hq)
      (fun q hq => by
        have := conj_mem_Qof (inv_mem hbS) (inv_mem hbn) hq
        simpa using this)
  set X : Subgroup G := Qof S K₁ ⊔ zpowers b with hX
  have hXS : X ≤ S := sup_le inf_le_left (zpowers_le.2 hbS)
  have hXp : IsPGroup 2 ↥X := hM.S_pgroup.to_le hXS
  have hQX : Qof S K₁ ≤ X := le_sup_left
  have hbX : b ∈ X := mem_sup_right (mem_zpowers b)
  have hcov : ∀ x ∈ X, x ∈ Qof S K₁ ∨ x * b⁻¹ ∈ Qof S K₁ := fun x hx =>
    mem_or_mul_inv_mem hb_norm hbbQ hx
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hzQ : z ∈ Qof S K₁ := z_mem_Qof hM (Or.inl rfl)
  by_cases hcase : ∃ u ∈ X, u ∉ Qof S K₁ ∧ u * u = 1
  · obtain ⟨u, huX, huQ, hu2⟩ := hcase
    have hub : u * b⁻¹ ∈ Qof S K₁ := (hcov u huX).resolve_left huQ
    have hu1 : u ≠ 1 := fun e => huQ (e ▸ Subgroup.one_mem _)
    refine ⟨u, hXS huX, orderOf_eq_two_of_mul_self_eq_one hu2 hu1,
      inducesFAut_of_mul_cSec hfb hub.2, fun hc => huQ ⟨hXS huX, hc⟩⟩
  · push Not at hcase
    have huniq : ∀ u ∈ X, u * u = 1 → u = 1 ∨ u = z := by
      intro u huX hu2
      by_cases huQ : u ∈ Qof S K₁
      · by_cases hu1 : u = 1
        · exact Or.inl hu1
        · exact Or.inr (eq_z_of_mem_Qof hM (Or.inl rfl) hm₁ hz2 huQ
            (orderOf_eq_two_of_mul_self_eq_one hu2 hu1))
      · exact absurd hu2 (hcase u huX huQ)
    have hnoncyc : ¬ IsCyclic ↥(Qof S K₁) := by
      intro hcyc
      have hle : S ⊓ K₂ ≤ Qof S K₁ := Pof_le_Qof hM (A := K₂) (B := K₁) (Or.inr ⟨rfl, rfl⟩)
      exact hnc G z S K₁ K₂ h K₂ hK₂ (isCyclic_of_le' hle hcyc)
    obtain ⟨t, htX, htQ, ht2⟩ := hq2 G X (Qof S K₁) z b hXp hQX hbX hbQ hbbQ hcov huniq hnoncyc
    have htS : t ∈ S := hXS htX
    have htb : t * b⁻¹ ∈ Qof S K₁ := (hcov t htX).resolve_left htQ
    have hFAt : InducesFAut t K₁ := inducesFAut_of_mul_cSec hfb htb.2
    have htn : t ∉ cSec K₁ := fun hc => htQ ⟨htS, hc⟩
    have htz : t * t ∈ cSec K₁ := by rw [ht2]; exact hzQ.2
    obtain ⟨y, hyP, hy2, hyt⟩ := hce G z S K₁ K₂ h K₁ hK₁ t htS hFAt htn htz
    have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
    have ha2 : (y * t) * (y * t) = 1 := by
      calc (y * t) * (y * t) = y * (t * y) * t := by group
        _ = y * (y * t) * t := by rw [← hyt]
        _ = (y * y) * (t * t) := by group
        _ = 1 := by rw [hy2, ht2, hz2']
    have hancs : y * t ∉ cSec K₁ := by
      intro hc
      have hy1 : y⁻¹ ∈ innSub K₁ := le_innSub K₁ (inv_mem hyP.2)
      have hc1 : y * t ∈ innSub K₁ := cSec_le_innSub K₁ hc
      have ht1 : t ∈ innSub K₁ := by
        have := mul_mem hy1 hc1
        simpa using this
      exact htn (hin G z S K₁ K₂ h K₁ hK₁ t hFAt ht1)
    have hnorm_a : y * t ∈ normalizer (K₁ : Set G) :=
      mul_mem (le_normalizer hyP.2) hFAt.1
    have hFA : InducesFAut (y * t) K₁ := by
      refine hco G z S K₁ K₂ h K₁ hK₁ (y * t) t hnorm_a hFAt.1 ?_ htz htn ?_ hFAt
      · rw [ha2]; exact (cSec K₁).one_mem
      · have : y * t * t⁻¹ = y := by group
        rw [this]; exact le_innSub K₁ hyP.2
    have ha1 : y * t ≠ 1 := fun e => hancs (e ▸ (cSec K₁).one_mem)
    exact ⟨y * t, mul_mem hyP.1 htS, orderOf_eq_two_of_mul_self_eq_one ha2 ha1, hFA, hancs⟩

theorem lemma510_aux (hII : II4_4_4_center) (h51 : Prop5_1) (hsq : IVK_f_sq) (hin : IVK_f_inner)
    (hco : IVK_f_coset) (hce : IVK_f_cent) (hnc : P_noncyclic) (hq2 : TwoGroup_coset_sq)
    (h32a : IVK_3_2a_strong) (h : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z)
    (hm₁ : pRank 2 ↥(Qof S K₁) = 1) (hm₂ : pRank 2 ↥(Qof S K₂) = 1)
    {b : G} (hbS : b ∈ S) (hb2 : b * b ∈ Rz S z) (hfb : InducesFAut b K₁) (hnb : b ∉ cSec K₁) :
    ∃ a ∈ S, orderOf a = 2 ∧ InducesFAut a K₁ ∧ a ∉ commBar z := by
  obtain ⟨a₀, ha₀S, ha₀2, ha₀f, ha₀n⟩ :=
    claimA hII hsq hin hco hce hnc hq2 h hQ hm₁ hbS hb2 hfb hnb
  have hM := m4_of_std hII h
  have hzK : z ∈ cSec K₁ := (z_mem_Qof hM (Or.inl rfl)).2
  have haz : a₀ ≠ z := fun e => ha₀n (e ▸ hzK)
  have haz' : a₀ ∉ zpowers z := by
    intro hmem
    rcases (M.mem_zpowers_of_sq (mul_self_eq_one_of_orderOf_eq_two h.orderOf_z)).1 hmem with e | e
    · exact ne_one_of_orderOf_eq_two ha₀2 e
    · exact haz e
  refine ⟨a₀, ha₀S, ha₀2, ha₀f, ?_⟩
  intro hcomm
  obtain ⟨hf2, _⟩ := h32a G z S K₁ K₂ a₀ ⟨h, hQ, hm₁, hm₂⟩ ha₀S ha₀2 haz ha₀f ha₀n hcomm
  exact h51 G z S K₁ K₂ h hm₁ hm₂ a₀ ha₀S ha₀2 haz' ha₀f hf2 hcomm

theorem lemma_5_10 (hII : II4_4_4_center) (h41 : Prop4_1) (h51 : Prop5_1) (hsq : IVK_f_sq)
    (hin : IVK_f_inner) (hco : IVK_f_coset) (hce : IVK_f_cent) (hnc : P_noncyclic)
    (hq2 : TwoGroup_coset_sq) (h32a : IVK_3_2a_strong) : Lemma5_10 := by
  intro G _ _ z S K₁ K₂ h hm₁ hm₂ b hbS hb2 K hK hfb hnb
  have hQ : Qz S z = zpowers z := (h41 G z S K₁ K₂ h).1
  rcases hK with rfl | hK
  · exact lemma510_aux hII h51 hsq hin hco hce hnc hq2 h32a h hQ hm₁ hm₂ hbS hb2 hfb hnb
  · rw [Set.mem_singleton_iff] at hK
    subst hK
    exact lemma510_aux hII h51 hsq hin hco hce hnc hq2 h32a h.swap hQ hm₂ hm₁ hbS hb2 hfb hnb

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
