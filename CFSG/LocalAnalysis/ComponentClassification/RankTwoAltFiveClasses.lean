module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveSylow
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_normal_index_two (hGs : IsSimpleGroup G) (hG : 2 < Nat.card G) :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hNidx⟩
  have := hGs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN1 | hN1
  · rw [hN1, Subgroup.index_bot] at hNidx
    omega
  · rw [hN1, Subgroup.index_top] at hNidx
    omega

theorem exists_conj_mem_sylow (S : Sylow 2 G) {x : G} (hx : IsPGroup 2 (zpowers x)) :
    ∃ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨S', hS'⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g x ∈ MulAut.conj g • (S' : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (mem_zpowers x))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  simpa [MulAut.conj_apply] using h1

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem two_lt_card : 2 < Nat.card G := by
  obtain ⟨eA⟩ := h.equiv
  have h1 := Subgroup.card_le_card_group A
  rw [Nat.card_congr eA.toEquiv, card_A5] at h1
  omega

theorem isConj_of_mem_V₀ {a b : G} (ha : a ∈ V₀) (ha1 : a ≠ 1) (hb : b ∈ V₀) (hb1 : b ≠ 1) :
    IsConj a b := by
  obtain ⟨eA⟩ := h.equiv
  obtain ⟨b₀, -, -, -, hb₀tr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  obtain ⟨k, hk⟩ := hb₀tr a ha b hb ha1 hb1
  exact isConj_iff.mpr ⟨(b₀ ^ k)⁻¹, by rw [inv_inv]; exact hk⟩

theorem not_isConj_of_mem_V₀ {a v : G} (ha : a ∈ V₀) (ha1 : a ≠ 1) (hv : v ∈ R ⊔ T)
    (hv0 : v ∉ V₀) : ¬ IsConj a v := by
  intro hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  exact h.conj_V₀_ne ha ha1 hv hv0 c⁻¹ (by rw [inv_inv]; exact hc)

theorem not_isConj_of_mem_R {a r : G} (ha : a ∈ V₀) (ha1 : a ≠ 1) (hr : r ∈ R) (hr1 : r ≠ 1) :
    ¬ IsConj a r := by
  refine h.not_isConj_of_mem_V₀ ha ha1 (mem_sup_left hr) fun hr0 => hr1 ?_
  have h1 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, hr0⟩
  rwa [h.inf_R_V₀, mem_bot] at h1

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem isConj_of_mem_R {r r' : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hr' : r' ∈ R) (hr'1 : r' ≠ 1) :
    IsConj r r' := by
  obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hIIa
  obtain ⟨hyK, hyN⟩ := mem_inf.mp hy
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  have hRc : R ≤ centralizer (R : Set G) := le_centralizer_self_of_isElemAbelian h.elemR
  have hconjR : ∀ u ∈ normalizer (R : Set G), u * r * u⁻¹ ∈ R := fun u hu =>
    (mem_normalizer_iff.mp hu r).mp hr
  have hne1 : ∀ u : G, u * r * u⁻¹ ≠ 1 := fun u h1 => hr1 (by
    calc r = u⁻¹ * (u * r * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group)
  have hyC' : y⁻¹ ∉ centralizer (R : Set G) := fun hc => hyC (by simpa using inv_mem hc)
  have hyyC : y * y ∉ centralizer (R : Set G) := fun hc =>
    hyC (mem_centralizer_of_sq_mem h.sylowR hRc hyK hyN hc)
  have h1 : y * r * y⁻¹ ≠ r := h.conj_ne_of_not_mem hyK hyN hyC hr hr1
  have h2 : y⁻¹ * r * y⁻¹⁻¹ ≠ r := h.conj_ne_of_not_mem (inv_mem hyK) (inv_mem hyN) hyC' hr hr1
  have h3 : y * r * y⁻¹ ≠ y⁻¹ * r * y⁻¹⁻¹ := by
    intro he
    apply h.conj_ne_of_not_mem (mul_mem hyK hyK) (mul_mem hyN hyN) hyyC hr hr1
    calc y * y * r * (y * y)⁻¹ = y * (y * r * y⁻¹) * y⁻¹ := by group
      _ = y * (y⁻¹ * r * y⁻¹⁻¹) * y⁻¹ := by rw [he]
      _ = r := by group
  have hthird : y⁻¹ * r * y⁻¹⁻¹ = r * (y * r * y⁻¹) := by
    rcases mem_four h.cardR hR2 hr (hconjR y hyN) hr1 (hne1 y) h1.symm
      (hconjR y⁻¹ (inv_mem hyN)) with h4 | h4 | h4 | h4
    · exact absurd h4 (hne1 _)
    · exact absurd h4 h2
    · exact absurd h4.symm h3
    · exact h4
  rcases mem_four h.cardR hR2 hr (hconjR y hyN) hr1 (hne1 y) h1.symm hr' with h4 | h4 | h4 | h4
  · exact absurd h4 hr'1
  · rw [h4]
  · exact isConj_iff.mpr ⟨y, h4.symm⟩
  · exact isConj_iff.mpr ⟨y⁻¹, by rw [hthird, h4]⟩

theorem isConj_of_mem_V {r v : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hv : v ∈ R ⊔ T) (hv0 : v ∉ V₀) :
    IsConj r v := by
  obtain ⟨c, -, hvc⟩ := h.loc.cover v hv hv0
  rw [mem_rightConjugate_iff] at hvc
  have hv1 : c * v * c⁻¹ ≠ 1 := fun h1 => hv0 (by
    have : v = c⁻¹ * (c * v * c⁻¹) * c := by group
    rw [this, h1]
    simp)
  exact (h.isConj_of_mem_R hIIa hr hr1 hvc hv1).trans
    (isConj_iff.mpr ⟨c⁻¹, by group⟩)

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem exists_conj_mem_P (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G)
    (hPS : P ≤ S) {u : G} (huS : u ∈ (S : Subgroup G)) (huP : u ∉ P) (hu2 : u * u = 1) :
    ∃ c : G, c⁻¹ * u * c ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS128, -, -, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hrel : P.relIndex S = 2 := by
    have h1 := Subgroup.relIndex_mul_card P S
    rw [inf_eq_left.mpr hPS, hS128, hP64] at h1
    omega
  have hu1 : u ≠ 1 := fun he => huP (he ▸ one_mem P)
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  by_contra hno
  push Not at hno
  refine not_normal_index_two hGs h.two_lt_card ?_
  refine CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson S.isPGroup'
    S.not_dvd_index hPS hrel huS huP (fun w _ hwP => ?_) hno
  have hw1 : w ≠ 1 := fun he => hwP (he ▸ one_mem P)
  have hpos := orderOf_pos w
  have hw1' : orderOf w ≠ 1 := fun he => hw1 (orderOf_eq_one_iff.mp he)
  omega

theorem isConj_or_isConj (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') {z₀ r₀ : G} (hz₀ : z₀ ∈ V₀)
    (hz₀1 : z₀ ≠ 1) (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1) {x : G} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    IsConj z₀ x ∨ IsConj r₀ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := hP.isPGroup.exists_le_sylow
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hPS' : P < S := lt_of_le_of_ne hPS (h.P_not_sylow hP hPC hGold hGs hIIa hP64 hVP S).symm
  obtain ⟨s₀, hs₀, hs₀P⟩ := IsConcreteLE.exists_of_lt hPS'
  obtain ⟨hVs, hV's⟩ := hswap s₀ hs₀ hs₀P
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  have hPinv : ∀ u ∈ P, u * u = 1 → u ≠ 1 → IsConj z₀ u ∨ IsConj r₀ u := by
    intro u hu hu2 hu1
    by_cases huV : u ∈ R ⊔ T
    · by_cases hu0 : u ∈ V₀
      · exact Or.inl (h.isConj_of_mem_V₀ hz₀ hz₀1 hu0 hu1)
      · exact Or.inr (h.isConj_of_mem_V hIIa hr₀ hr₀1 huV hu0)
    ·
      have huV' := hV'inv u hu hu2 huV
      have h1 : s₀ * u * s₀⁻¹ ∈ R ⊔ T := by
        rw [← hVs] at huV'
        exact (mem_rightConjugate_iff _ _ _).mp huV'
      have h2 : s₀ * u * s₀⁻¹ ∉ V₀ := by
        intro h0
        apply huV
        rw [← hV's, mem_rightConjugate_iff]
        exact hV₀V' h0
      exact Or.inr ((h.isConj_of_mem_V hIIa hr₀ hr₀1 h1 h2).trans
        (isConj_iff.mpr ⟨s₀⁻¹, by group⟩))
  have hSinv : ∀ u ∈ (S : Subgroup G), u * u = 1 → u ≠ 1 → IsConj z₀ u ∨ IsConj r₀ u := by
    intro u hu hu2 hu1
    by_cases huP : u ∈ P
    · exact hPinv u huP hu2 hu1
    obtain ⟨c, hc⟩ := h.exists_conj_mem_P hIIa hP hPC hGold hGs hP64 hVP hε hV'P hV'e hV'16
      hinf hsup hV'inv S hPS hu huP hu2
    have hc2 : c⁻¹ * u * c * (c⁻¹ * u * c) = 1 := by
      calc c⁻¹ * u * c * (c⁻¹ * u * c) = c⁻¹ * (u * u) * c := by group
        _ = 1 := by rw [hu2]; group
    have hc1 : c⁻¹ * u * c ≠ 1 := fun he => hu1 (by
      calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
        _ = 1 := by rw [he]; group)
    have hcu : IsConj (c⁻¹ * u * c) u := isConj_iff.mpr ⟨c, by group⟩
    rcases hPinv _ hc hc2 hc1 with h1 | h1
    · exact Or.inl (h1.trans hcu)
    · exact Or.inr (h1.trans hcu)
  have hxp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx2 hx1]; norm_num)
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow S hxp
  have hc2 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [← sq, hx2]; group
  have hc1 : c * x * c⁻¹ ≠ 1 := fun he => hx1 (by
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [he]; group)
  have hcx : IsConj (c * x * c⁻¹) x := isConj_iff.mpr ⟨c⁻¹, by group⟩
  rcases hSinv _ hc hc2 hc1 with h1 | h1
  · exact Or.inl (h1.trans hcx)
  · exact Or.inr (h1.trans hcx)

end PStructure

end IIa

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive

