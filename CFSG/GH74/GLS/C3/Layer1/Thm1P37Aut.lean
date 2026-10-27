module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutL2
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem le_sup_zpowers_of_notation (hF : L2Field F) {e' : K ≃* L2 F} (N : L2Notation e') {σ : MulAut K}
    (hσR : σ ∈ N.R) (hσ2 : orderOf σ = 2) {E : Subgroup (MulAut K)}
    (hET : E ≤ (N.T : Subgroup (MulAut K))) (hE : IsElementaryAbelian 2 ↥E)
    (hE8 : 8 ≤ Nat.card ↥E) : E ≤ N.P ⊔ zpowers σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := sq_eq_one_of_isElementaryAbelian' hE
  have hcomm := comm_of_isElementaryAbelian' hE
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hinnle : innAut K ≤ innDiagSub e' := innAut_le_innDiagSub e'
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hσc : ∀ r ∈ N.P, σ * r = r * σ := fun r hr => (N.R_cent σ hσR hσ2 r hr).symm
  have hEnot : ¬ E ≤ innDiagSub e' := fun hle => by
    have := card_le_four_of_le_inf e' hF N.T E hET hle hcomm hsq
    omega
  obtain ⟨y, hyE, hyD⟩ : ∃ y ∈ E, y ∉ innDiagSub e' := by
    by_contra hcon
    push Not at hcon
    exact hEnot hcon
  have hy2 : y * y = 1 := hsq y hyE
  have hy1 : y ≠ 1 := fun h => hyD (h ▸ (innDiagSub e').one_mem)
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hyT : y ∈ (N.T : Subgroup (MulAut K)) := hET hyE
  obtain ⟨p, hpP, hyp⟩ : ∃ p ∈ N.P, y = p * σ := by
    rcases ivk_1_2i_c F hF K e' N σ hσR hσ2 y hyT hyord with h | ⟨h, -⟩ | ⟨p, hpP, hyp⟩
    · exact absurd (hinnle h.2) hyD
    · exact absurd h.2 hyD
    · exact ⟨p, hpP, hyp⟩
  intro g hg
  have hg2 : g * g = 1 := hsq g hg
  by_cases hg1 : g = 1
  · rw [hg1]
    exact one_mem _
  have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hg2) hg1
  have hgT : g ∈ (N.T : Subgroup (MulAut K)) := hET hg
  rcases ivk_1_2i_c F hF K e' N σ hσR hσ2 g hgT hgord with h | ⟨h, hgP⟩ | ⟨q, hqP, hgq⟩
  · exact Subgroup.mem_sup_left h
  · exfalso
    have hgD : g ∈ innDiagSub e' := h.2
    have hw2 : (y * g) * (y * g) = 1 := by
      calc y * g * (y * g) = y * (g * y) * g := by group
        _ = y * (y * g) * g := by rw [hcomm g hg y hyE]
        _ = (y * y) * (g * g) := by group
        _ = 1 := by rw [hy2, hg2, one_mul]
    have hw1 : y * g ≠ 1 := by
      intro h1
      apply hyD
      have : y = g⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (innDiagSub e').inv_mem hgD
    have hword : orderOf (y * g) = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
    have hwT : y * g ∈ (N.T : Subgroup (MulAut K)) := (N.T : Subgroup (MulAut K)).mul_mem hyT hgT
    have hyw : y = (y * g) * g⁻¹ := by group
    rcases ivk_1_2i_c F hF K e' N σ hσR hσ2 (y * g) hwT hword with h1 | ⟨h1, -⟩ | ⟨q, hqP, hwq⟩
    · apply hyD
      rw [hyw]
      exact (innDiagSub e').mul_mem (hinnle (hPinn h1)) ((innDiagSub e').inv_mem hgD)
    · apply hyD
      rw [hyw]
      exact (innDiagSub e').mul_mem h1.2 ((innDiagSub e').inv_mem hgD)
    ·
      apply hgP
      have hc : σ * (p⁻¹ * q) = (p⁻¹ * q) * σ := hσc _ (N.P.mul_mem (N.P.inv_mem hpP) hqP)
      have hgeq : g = p⁻¹ * q := by
        calc g = y⁻¹ * (y * g) := by group
          _ = (p * σ)⁻¹ * (q * σ) := by rw [hwq, hyp]
          _ = σ⁻¹ * (p⁻¹ * q) * σ := by group
          _ = σ⁻¹ * ((p⁻¹ * q) * σ) := by group
          _ = σ⁻¹ * (σ * (p⁻¹ * q)) := by rw [hc]
          _ = p⁻¹ * q := by group
      rw [hgeq]
      exact N.P.mul_mem (N.P.inv_mem hpP) hqP
  · rw [hgq]
    exact mul_mem (Subgroup.mem_sup_left hqP) (Subgroup.mem_sup_right (mem_zpowers σ))

theorem exists_mul_of_mem_sup_of_le_normalizer {X : Type*} [Group X] {N H : Subgroup X}
    (h : H ≤ normalizer (N : Set X)) {x : X} (hx : x ∈ N ⊔ H) : ∃ n ∈ N, ∃ k ∈ H, x = n * k := by
  have h1 : x ∈ ((N ⊔ H : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N H h] at h1
  obtain ⟨n, hn, k, hk, hnk⟩ := h1
  exact ⟨n, hn, k, hk, hnk.symm⟩

@[expose] def AutLevelJ (Kb : Type) [Group Kb] : Prop :=
  ∀ B : Subgroup (MulAut Kb), IsPGroup 2 ↥B → IsSylowOf 2 (B ⊓ innAut Kb) (innAut Kb) →
    ∀ E : Subgroup (MulAut Kb), E ≤ B → IsElementaryAbelian 2 ↥E → 8 ≤ Nat.card ↥E →
    ∀ z : MulAut Kb, z ∈ B ⊓ innAut Kb → orderOf z = 2 → (∀ q ∈ B ⊓ innAut Kb, z * q = q * z) →
      (∀ w ∈ B ⊓ innAut Kb, (∀ q ∈ B ⊓ innAut Kb, w * q = q * w) → w = 1 ∨ w = z) →
    ∀ σ ∈ B, orderOf σ = 2 → σ ∉ innAut Kb → (∀ q ∈ B ⊓ innAut Kb, σ * q = q * σ) →
      E ≤ (B ⊓ innAut Kb) ⊔ zpowers σ ∧
      ∀ P₀ : Subgroup (MulAut Kb), P₀ ≤ B ⊓ innAut Kb →
        (P₀.subgroupOf (B ⊓ innAut Kb)).index = 2 → (∃ n : ℕ, IsDihedralTwoGroup ↥P₀ n) →
        ∃ (R : Subgroup (MulAut Kb)) (σ₀ : MulAut Kb), IsCyclic ↥R ∧ σ₀ ∈ R ∧
          (σ = σ₀ ∨ σ = σ₀ * z) ∧
          (∀ τ ∈ B, τ ∈ normalizer (P₀ : Set (MulAut Kb)) ↔ τ * σ₀ = σ₀ * τ) ∧
          ∀ τ ∈ B, τ ∈ normalizer (P₀ : Set (MulAut Kb)) → ∃ q ∈ B ⊓ innAut Kb, q⁻¹ * τ ∈ R

theorem autLevelJ_of_L2
    (h2hb : IVK_1_2h_b) (hF : L2Field F) (e : K ≃* L2 F) : AutLevelJ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro B hB hSyl E hEB hE hE8 z hzP hz2 hzc hzu σ hσB hσ2 hσinn hσc
  obtain ⟨e', N, σ₁, y, p, hBN, hPeq, hyE, hpB, hσ₁R, hσ₁2, hσ₁eq, hσ₁inn⟩ :=
    exists_notation_field_inv hF e B hB hSyl E hEB hE hE8
  have hzN : z ∈ N.P := by rw [hPeq]; exact hzP
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hcls := (fus_L2 h2hb hF N B hPeq hσ₁R hσ₁2 hzN hz2
    (fun q hq => hzc q (by rw [← hPeq]; exact hq))
    (fun w hw hwc => hzu w (by rw [← hPeq]; exact hw)
      (fun q hq => hwc q (by rw [hPeq]; exact hq)))).1 σ hσB hσ2 hσinn hσc
  refine ⟨?_, ?_⟩
  · have h1 := le_sup_zpowers_of_notation hF N hσ₁R hσ₁2 (hEB.trans hBN) hE hE8
    refine h1.trans (sup_le (by rw [hPeq]; exact le_sup_left) ?_)
    rw [zpowers_le]
    rcases hcls with h | h
    · rw [← h]
      exact Subgroup.mem_sup_right (mem_zpowers σ)
    · have hσ₁ : σ₁ = σ * z := by
        calc σ₁ = σ₁ * (z * z) := by rw [hzz, mul_one]
          _ = σ₁ * z * z := by rw [mul_assoc]
          _ = σ * z := by rw [← h]
      rw [hσ₁]
      exact mul_mem (Subgroup.mem_sup_right (mem_zpowers σ))
        (Subgroup.mem_sup_left hzP)
  · intro P₀ hP₀ hidx hdih
    rw [← hPeq] at hP₀ hidx
    obtain ⟨hN1, hN2⟩ := Proofs2.ivk_1_3g F hF K e' N P₀ hP₀ hidx hdih
    have hRle : N.R ≤ fieldAutSub e' := inf_le_right
    have hRcyc : IsCyclic ↥N.R := by
      have := (ivk_1_2e F hF K e').1
      exact Subgroup.isCyclic_of_le hRle
    refine ⟨N.R, σ₁, hRcyc, hσ₁R, hcls, ?_, ?_⟩
    · intro τ hτ
      have hτN : τ ∈ (N.T : Subgroup (MulAut K)) := hBN hτ
      have := hN2 σ₁ hσ₁R hσ₁2
      constructor
      · intro hn
        have h1 : τ ∈ normalizer (P₀ : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) := ⟨hn, hτN⟩
        rw [this] at h1
        exact mem_centralizer_singleton_iff.1 h1.1
      · intro hc
        have h1 : τ ∈ centralizer ({σ₁} : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) :=
          ⟨mem_centralizer_singleton_iff.2 hc, hτN⟩
        rw [← this] at h1
        exact h1.1
    · intro τ hτ hn
      have hτN : τ ∈ (N.T : Subgroup (MulAut K)) := hBN hτ
      have h1 : τ ∈ normalizer (P₀ : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) := ⟨hn, hτN⟩
      rw [hN1] at h1
      have hRN : N.R ≤ normalizer ((N.P : Subgroup (MulAut K)) : Set (MulAut K)) := by
        intro r hr
        refine Subgroup.mem_normalizer_iff.2 fun w => ?_
        have hrT : r ∈ (N.T : Subgroup (MulAut K)) := hr.1
        have hconj : ∀ r ∈ (N.T : Subgroup (MulAut K)), ∀ w ∈ N.P, r * w * r⁻¹ ∈ N.P := by
          intro r hr w hw
          refine ⟨(N.T : Subgroup (MulAut K)).mul_mem
            ((N.T : Subgroup (MulAut K)).mul_mem hr hw.1) ((N.T : Subgroup (MulAut K)).inv_mem hr), ?_⟩
          exact Subgroup.Normal.conj_mem (innAut_normal (K := K)) w hw.2 r
        refine ⟨fun hw => hconj r hrT w hw, fun hw => ?_⟩
        have := hconj r⁻¹ ((N.T : Subgroup (MulAut K)).inv_mem hrT) _ hw
        simpa [mul_assoc] using this
      obtain ⟨q, hq, r, hr, hτ'⟩ := exists_mul_of_mem_sup_of_le_normalizer hRN h1
      refine ⟨q, by rw [← hPeq]; exact hq, ?_⟩
      rw [hτ']
      simpa using hr

end CFSG.GH74.GLS.C3.Layer1.Thm1
