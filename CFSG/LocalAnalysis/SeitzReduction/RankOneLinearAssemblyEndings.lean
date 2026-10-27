module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearAssemblyLift
public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelian

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)
open CFSG.ComponentClassification.GMS78.Finkelstein (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LinearPushChain

variable {G : Type} [Group G] [Finite G] {t d : G} {T A : Subgroup G} {f m : ℕ}
  {C : ℕ → Subgroup G}

theorem commutator_mem_base (h : LinearPushChain t d T A f m C) (hf : 2 ≤ f) (htt : t * t = 1)
    (hdfix : ∀ k : ℕ, ∀ a ∈ A, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1) :
    ∀ x ∈ C (m + 1), ∀ y ∈ C (m + 1), x * y * x⁻¹ * y⁻¹ ∈ A := by
  intro x hx y hy
  by_cases hc : ∀ a b : C (m + 1), a * b = b * a
  · have hxy : x * y = y * x := congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  push Not at hc
  have hH := h.finkHyp hf htt hdfix (j := m + 1) (by omega) le_rfl
  obtain ⟨hcomm, -, -⟩ := hH.special_of_not_comm hc
  have h1 := (h.mem_fixSubgroup_iff le_rfl _).mp (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  simpa [commutatorElement_def] using h1

theorem le_card_inf_centralizer (h : LinearPushChain t d T A f m C) (hf : 2 ≤ f)
    (htt : t * t = 1)
    (hdfix : ∀ k : ℕ, ∀ a ∈ A, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    {w : G} (hw : w ∈ C (m + 1)) :
    2 ^ (f * (m + 1)) ≤ 2 ^ f * Nat.card (C (m + 1) ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  set I : Set G := (fun a => a * w) '' (A : Set G) with hI
  have hcount := card_le_mul_card_inf_centralizer_of_conj_mem (C (m + 1)) w I (fun s hs =>
    ⟨s * w * s⁻¹ * w⁻¹, h.commutator_mem_base hf htt hdfix s hs w hw, by group⟩)
  have hIc : Nat.card I ≤ 2 ^ f := by
    rw [Nat.card_coe_set_eq]
    calc I.ncard ≤ (A : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 2 ^ f := by
        rw [← Nat.card_coe_set_eq]
        have := h.card 1 (by omega)
        rwa [h.base, mul_one] at this
  rw [h.card (m + 1) le_rfl] at hcount
  exact hcount.trans (Nat.mul_le_mul_right _ hIc)

theorem sq_dichotomy_of_eq_one (h : LinearPushChain t d T A f 1 C) (hf : 2 ≤ f)
    (htt : t * t = 1)
    (hdfix : ∀ k : ℕ, ∀ a ∈ A, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1) :
    (∀ a ∈ C 2, ∀ b ∈ C 2, a * b = b * a) ∧
      ((∀ x ∈ C 2, x * x = 1) ∨
        ((∀ x ∈ C 2, x * x = 1 → x ∈ A) ∧ ∀ a ∈ A, ∃ x ∈ C 2, x * x = a)) := by
  have hH := h.finkHyp hf htt hdfix (j := 2) (by omega) le_rfl
  have hc : ∀ a b : C 2, a * b = b * a := by
    by_contra hnc
    push Not at hnc
    have h1 := hH.le_natCard_of_not_comm hnc
    rw [h.card 2 le_rfl] at h1
    have h2 : 3 * f ≤ f * 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    omega
  refine ⟨fun a ha b hb => congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩), ?_⟩
  by_cases hel : ∀ x ∈ C 2, x * x = 1
  · exact Or.inl hel
  right
  push Not at hel
  obtain ⟨x₀, hx₀, hx₀1⟩ := hel
  refine ⟨fun x hx hxx => ?_, fun a ha => ?_⟩
  · rcases hH.abelian_omega_or_elem hc with hom | ⟨hel', -⟩
    · have h1 := hom ⟨x, hx⟩ (Subtype.ext (by simp [sq, hxx]))
      exact (h.mem_fixSubgroup_iff le_rfl _).mp h1
    · exact absurd (by simpa [sq] using congrArg Subtype.val (hel' ⟨x₀, hx₀⟩)) hx₀1
  · by_cases ha1 : a = 1
    · exact ⟨1, one_mem _, by rw [ha1, mul_one]⟩
    have ha₀ : x₀ * x₀ ∈ A := h.base ▸ h.layer_sq 1 le_rfl x₀ hx₀
    obtain ⟨k, hk⟩ := h.d_reg _ ha₀ a ha hx₀1 ha1
    refine ⟨d ^ k * x₀ * (d ^ k)⁻¹, ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (pow_mem (h.d_norm 2 le_rfl) k) x₀).mp hx₀
    · rw [← hk]
      group

end LinearPushChain

variable {G : Type} [Group G] [Finite G]

theorem false_of_chain_of_two_le (hGold : Goldschmidt1974) {L T : Subgroup G} {f m : ℕ}
    {t d : G} {C : ℕ → Subgroup G} (hS : Endings.Setting G L f t T)
    (h : LinearPushChain t d T (T ⊓ L) f m C) (hm : 2 ≤ m)
    (hdfix : ∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    (hsyl : IsSylowOf 2 (C (m + 1) ⊔ T) (pushNormalizer C (m + 1))) : False := by
  obtain ⟨-, htt, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := Endings.psl2_ending_facts hGold hS
  have hf : 2 ≤ f := by have := hS.three_le; omega
  have hW'ab := h.comm_of_one_le (by omega) htt
  have hUW' : T ⊓ L ≤ C m := h.base_le (by omega) (by omega)
  have hW'W : C m ≤ C (m + 1) := h.mono m le_rfl
  have hΩ' : ∀ w ∈ C m, w * w = 1 → w ∈ T ⊓ L := fun w hw hww =>
    h.mem_base_of_sq_eq_one (by omega) htt hw hww
  have h℧' := h.exists_sq_eq_of_two_le hm htt
  have hWW' : C (m + 1) ≤ normalizer (C m : Set G) := h.normal m le_rfl
  have hTW' : T ≤ normalizer (C m : Set G) := h.T_norm m (by omega)
  have hTW : T ≤ normalizer (C (m + 1) : Set G) := h.T_norm (m + 1) le_rfl
  have hcomm := h.commute_base hf htt hdfix (j := m + 1) (by omega) le_rfl
  have hWU : C (m + 1) ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun a ha => (hcomm x hx a ha).symm
  have hcent : ∀ w ∈ C (m + 1), w * w = 1 →
      (2 ^ f) ^ 2 ≤ Nat.card (C (m + 1) ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    intro w hw _
    have h1 := h.le_card_inf_centralizer hf htt hdfix hw
    have h2 : 2 ^ (f * (m + 1)) = 2 ^ f * 2 ^ (f * m) := by rw [← pow_add]; ring_nf
    rw [h2] at h1
    have h3 := Nat.le_of_mul_le_mul_left h1 (by positivity)
    calc (2 ^ f) ^ 2 = 2 ^ (f * 2) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (f * m) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left f hm)
      _ ≤ _ := h3
  have hUW : T ⊓ L ≤ C (m + 1) := hUW'.trans hW'W
  have hconj := Endings.not_conj_of_homocyclic hGold hS hUW hTW hWU hW'ab hUW' hΩ' h℧' hWW' hTW'
  have hSyl := h.exists_sylow_of_not_conj hGold hS (by omega) hdfix hsyl hconj
  exact Endings.false_of_gms41 hGold hS hW'ab hUW' hW'W hΩ' h℧' hWW' hTW' hWU hTW h.t_not_mem
    hcent hSyl

theorem false_of_chain_of_eq_one_of_not_elem (hGold : Goldschmidt1974) {L T : Subgroup G}
    {f : ℕ} {t d : G} {C : ℕ → Subgroup G} (hS : Endings.Setting G L f t T)
    (h : LinearPushChain t d T (T ⊓ L) f 1 C)
    (hdfix : ∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    (hsyl : IsSylowOf 2 (C 2 ⊔ T) (pushNormalizer C 2)) (hnel : ¬ ∀ x ∈ C 2, x * x = 1) :
    False := by
  obtain ⟨-, htt, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := Endings.psl2_ending_facts hGold hS
  have hf : 2 ≤ f := by have := hS.three_le; omega
  obtain ⟨hWab, hcases⟩ := h.sq_dichotomy_of_eq_one hf htt hdfix
  obtain ⟨hΩ, h℧⟩ := hcases.resolve_left hnel
  have hUW : T ⊓ L ≤ C 2 := h.base_le (by omega) le_rfl
  have hTW : T ≤ normalizer (C 2 : Set G) := h.T_norm 2 le_rfl
  have hWU : C 2 ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun a ha => hWab a (hUW ha) x hx
  have hWW : C 2 ≤ normalizer (C 2 : Set G) := le_normalizer
  have hcent : ∀ w ∈ C 2, w * w = 1 →
      (2 ^ f) ^ 2 ≤ Nat.card (C 2 ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    intro w hw _
    have heq : C 2 ⊓ centralizer ({w} : Set G) = C 2 :=
      inf_eq_left.mpr fun x hx => mem_centralizer_singleton_iff.mpr (hWab x hx w hw)
    rw [heq, h.card 2 le_rfl, ← pow_mul, mul_comm]
  have hconj := Endings.not_conj_of_homocyclic hGold hS hUW hTW hWU hWab hUW hΩ h℧ hWW hTW
  have hSyl := h.exists_sylow_of_not_conj hGold hS le_rfl hdfix hsyl hconj
  exact Endings.false_of_gms41 hGold hS hWab hUW le_rfl hΩ h℧ hWW hTW hWU hTW h.t_not_mem
    hcent hSyl

end CFSG.SeitzReduction.RankOne
