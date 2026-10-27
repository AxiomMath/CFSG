module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveZ

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {fr : JankoFrame G z}

theorem exists_mem_normalizer_N_not_mem (h : Hyp fr) :
    ∃ g ∈ normalizer (fr.N : Set G), g ∉ normalizer (fr.P₁ : Set G) := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hNR⟩ := h.isPGroup_N.exists_le_sylow
  have hNR' : fr.N = (R : Subgroup G) := by
    by_contra hne
    have hlt := lt_inf_normalizer_of_lt R.isPGroup' (lt_of_le_of_ne hNR hne)
    have hle : (R : Subgroup G) ⊓ normalizer (fr.N : Set G) ≤ normalizer (fr.P₁ : Set G) :=
      fun x hx => hcon x (Subgroup.mem_inf.mp hx).2
    have hcard := card_le_of_isSylowOf h.p11.isSylowOf_N (R.isPGroup'.to_le inf_le_left) hle
    exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr hcard)
  obtain ⟨x, -, hx⟩ := fr.exists_orderOf_nine
  have hxp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨R', hR'⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R R'
  have hxR' : x ∈ (R' : Subgroup G) := hR' (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxR'
  have hmem : g⁻¹ * x * g ∈ fr.N := by
    rw [hNR']
    convert hxR' using 1
    simp [MulAut.smul_def]
  have h3 := h.p11.N_pow_three _ hmem
  have hx3 : x ^ 3 = 1 := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow] at h3
    calc x ^ 3 = g * (g⁻¹ * x ^ 3 * g⁻¹⁻¹) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  have := orderOf_dvd_of_pow_eq_one hx3
  rw [hx] at this
  exact absurd this (by norm_num)

theorem conj_s₁_mem_ZN (h : Hyp fr) {g : G} (hg : g ∈ normalizer (fr.N : Set G)) :
    g * fr.s₁ * g⁻¹ ∈ fr.ZN :=
  (Subgroup.mem_normalizer_iff.mp (h.mem_normalizer_ZN hg) _).mp h.s₁_mem_ZN

theorem conj_s₁_not_mem_S (h : Hyp fr) (g : G) : g * fr.s₁ * g⁻¹ ∉ fr.S := by
  intro hS
  have hne : g * fr.s₁ * g⁻¹ ≠ 1 := by
    intro h1
    apply h.s₁_ne_one
    calc fr.s₁ = g⁻¹ * (g * fr.s₁ * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  exact h.p7.not_isConj_s₁_s₃ ((isConj_iff.mpr ⟨g, rfl⟩).trans (h.isConj_s₃_of_mem_S hS hne))

theorem mem_orbit_s₁ (h : Hyp fr) {x : G} (hx : x ∈ fr.ZN) (hxS : x ∉ fr.S) :
    ∃ g ∈ normalizer (fr.N : Set G), g * fr.s₁ * g⁻¹ = x := by
  by_cases hxP : x ∈ fr.P₁
  · have hx1 : x ≠ 1 := fun h1 => hxS (h1 ▸ one_mem _)
    rw [fr.P₁_eq] at hxP
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers fr.orderOf_s₁ hxP with h1 | h1 | h1
    · exact absurd h1 hx1
    · exact ⟨1, one_mem _, by rw [h1]; group⟩
    · exact ⟨fr.t, h.L_le_normalizer_N h.t_mem_L, by rw [h1, h.t_conj_s₁]⟩
  · obtain ⟨g₀, hg₀, hg₀P⟩ := h.exists_mem_normalizer_N_not_mem
    have hyZ := h.conj_s₁_mem_ZN hg₀
    have hyS := h.conj_s₁_not_mem_S g₀
    have hyP : g₀ * fr.s₁ * g₀⁻¹ ∉ fr.P₁ := by
      intro hyP
      apply hg₀P
      refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun w hw => ?_
      rw [fr.P₁_eq] at hw hyP ⊢
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow]
      exact zpow_mem hyP k
    obtain ⟨l, hl, hlx⟩ := h.p11.exists_conj_ZN _ hyZ x hx hyP hyS hxP hxS
    exact ⟨l * g₀, mul_mem (h.L_le_normalizer_N hl) hg₀, by rw [← hlx]; group⟩

theorem orbit_s₁_eq (h : Hyp fr) :
    {y | ∃ g ∈ normalizer (fr.N : Set G), g * fr.s₁ * g⁻¹ = y} = (fr.ZN : Set G) \ fr.S := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨h.conj_s₁_mem_ZN hg, h.conj_s₁_not_mem_S g⟩
  · rintro ⟨hx, hxS⟩
    exact h.mem_orbit_s₁ hx hxS

theorem ncard_orbit_s₁ (h : Hyp fr) :
    {y | ∃ g ∈ normalizer (fr.N : Set G), g * fr.s₁ * g⁻¹ = y}.ncard = 18 := by
  rw [h.orbit_s₁_eq, Set.ncard_sdiff (fun x hx => h.S_le_ZN hx) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe,
    h.p11.card_ZN, h.card_S]

theorem L₁_le_normalizer_N (h : Hyp fr) : fr.L₁ ≤ normalizer (fr.N : Set G) := by
  rw [fr.L₁_eq, Subgroup.zpowers_le]
  exact h.L_le_normalizer_N h.ℓ_mem_L

theorem L₁_le_centralizer_s₁ (h : Hyp fr) : fr.L₁ ≤ centralizer ({fr.s₁} : Set G) := by
  rw [fr.L₁_eq, Subgroup.zpowers_le, ← h.centralizer_P₁_eq]
  exact fr.F_le_centralizer fr.ℓ_mem_F

theorem card_L₁ (_h : Hyp fr) : Nat.card fr.L₁ = 8 := by
  rw [fr.L₁_eq, Nat.card_zpowers, fr.orderOf_ℓ]

theorem card_N_sup_L (h : Hyp fr) : Nat.card (fr.N ⊔ fr.L : Subgroup G) = 3 ^ 7 * 16 := by
  have hb : fr.L ⊓ fr.N = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [fr.card_L, h.p11.card_N]; norm_num))
  rw [sup_comm, card_sup_of_inf_eq_bot h.L_le_normalizer_N hb, fr.card_L, h.p11.card_N]
  ring

theorem card_normalizer_N_inf_centralizer_s₁ (h : Hyp fr) :
    Nat.card (normalizer (fr.N : Set G) ⊓ centralizer ({fr.s₁} : Set G) : Subgroup G) =
      3 ^ 7 * 8 := by
  set A := normalizer (fr.N : Set G) ⊓ centralizer ({fr.s₁} : Set G)
  have hb : fr.L₁ ⊓ fr.N = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [h.card_L₁, h.p11.card_N]; norm_num))
  have hc1 : Nat.card (fr.L₁ ⊔ fr.N : Subgroup G) = 3 ^ 7 * 8 := by
    rw [card_sup_of_inf_eq_bot h.L₁_le_normalizer_N hb, h.card_L₁, h.p11.card_N]
    ring
  have hle1 : fr.L₁ ⊔ fr.N ≤ A :=
    sup_le (le_inf h.L₁_le_normalizer_N h.L₁_le_centralizer_s₁)
      (le_inf Subgroup.le_normalizer h.N_le_centralizer_s₁)
  have hle2 : A ≤ fr.N ⊔ fr.L := by
    rw [← h.p11.normalizer_N_inf]
    refine inf_le_inf_left _ ?_
    rw [← h.centralizer_P₁_eq]
    exact Subgroup.centralizer_le_normalizer _
  have htA : fr.t ∉ A := by
    intro htA
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp htA).2
    have h2 := h.t_conj_s₁
    rw [h1, mul_inv_cancel_right] at h2
    have h3 : fr.s₁ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h2]
      exact mul_inv_cancel _
    have := orderOf_dvd_of_pow_eq_one h3
    rw [fr.orderOf_s₁] at this
    exact absurd this (by norm_num)
  have htNL : fr.t ∈ fr.N ⊔ fr.L := (le_sup_right : fr.L ≤ fr.N ⊔ fr.L) h.t_mem_L
  have hlt : Nat.card A < 3 ^ 7 * 16 := by
    rw [← h.card_N_sup_L]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle2 fun he => htA (he ▸ htNL))
  obtain ⟨k, hk⟩ : 3 ^ 7 * 8 ∣ Nat.card A := hc1 ▸ Subgroup.card_dvd_of_le hle1
  have hd : Nat.card A ∣ 3 ^ 7 * 16 := h.card_N_sup_L ▸ Subgroup.card_dvd_of_le hle2
  rw [hk] at hlt hd ⊢
  have hk2 : k ∣ 2 := by
    rw [show 3 ^ 7 * 16 = 3 ^ 7 * 8 * 2 by norm_num] at hd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
  · ring
  · exact absurd hlt (by norm_num)

theorem card_normalizer_N (h : Hyp fr) :
    Nat.card (normalizer (fr.N : Set G)) = 3 ^ 9 * 2 ^ 4 := by
  have := card_conj_orbit_mul (normalizer (fr.N : Set G)) fr.s₁
  rw [h.ncard_orbit_s₁, h.card_normalizer_N_inf_centralizer_s₁] at this
  rw [← this]
  norm_num

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
