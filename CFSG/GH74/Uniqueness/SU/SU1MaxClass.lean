module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup
open scoped commutatorElement

@[expose] def CentralizerQuotientLe : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal] (x : X),
    Nat.card (centralizer ({(x : X ⧸ N)} : Set (X ⧸ N))) ≤ Nat.card (centralizer ({x} : Set X))

theorem maximalClass_aux (h916 : CentralizerQuotientLe) (p : ℕ) (hp : p.Prime) :
    ∀ n : ℕ, ∀ (P : Type) [Group P] [Finite P], Nat.card P = n → IsPGroup p P → p ^ 3 ≤ n →
      ∀ x : P, Nat.card (centralizer ({x} : Set P)) ≤ p ^ 2 →
        ∃ m : ℕ, Nat.card P = p ^ m ∧ (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hn hP hcard x hx
  have := Fact.mk hp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hm3 : 3 ≤ m := by
    rw [← hn, hm] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  have hnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hm]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  set Z := center P with hZdef
  have hxZ : x ∉ Z := by
    intro hxZ
    have htop : centralizer ({x} : Set P) = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hxZ g)
    rw [htop, Subgroup.card_top, hm] at hx
    have h1 : m ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hx
    omega
  have hZC : Z ≤ centralizer ({x} : Set P) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hz x).symm
  have hZlt : Z < centralizer ({x} : Set P) := by
    refine lt_of_le_of_ne hZC (fun h => hxZ ?_)
    rw [h, Subgroup.mem_centralizer_singleton_iff]
  have hZcard : Nat.card Z = p := by
    have hlt := Subgroup.card_lt_of_lt hZlt
    have hdvd : Nat.card Z ∣ p ^ m := hm ▸ Subgroup.card_subgroup_dvd_card Z
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hZnt : Nontrivial Z := hP.center_nontrivial
    have hZ1 : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    rw [hs] at hZ1 hlt ⊢
    have hs1 : 1 ≤ s := by
      by_contra hcon
      have : s = 0 := by omega
      rw [this, pow_zero] at hZ1
      exact lt_irrefl _ hZ1
    have hs2 : s < 2 := by
      have := hlt.trans_le hx
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp this
    have : s = 1 := by omega
    rw [this, pow_one]
  by_cases hm3' : m = 3
  · refine ⟨3, by rw [hm, hm3'], ?_⟩
    rw [show 3 - 2 = 1 by norm_num, Subgroup.top_lowerCentralSeries_one]
    intro hab
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    have hcomm : ⁅g, x⁆ ∈ commutator P :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
    rw [hab, Subgroup.mem_bot, commutatorElement_def] at hcomm
    calc g * x = (g * x * g⁻¹ * x⁻¹) * (x * g) := by group
      _ = x * g := by rw [hcomm, one_mul]
  have hm4 : 4 ≤ m := by omega
  set Q := P ⧸ Z with hQdef
  have hQcard : Nat.card Q = p ^ (m - 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hZcard, hm] at h1
    have h2 : p ^ m = p ^ (m - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h1).symm
  have hQp : IsPGroup p Q := hP.to_quotient Z
  have hxbar : Nat.card (centralizer ({(x : Q)} : Set Q)) ≤ p ^ 2 := (h916 P Z x).trans hx
  have hlt : Nat.card Q < n := by
    rw [← hn, hm, hQcard]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hQ3 : p ^ 3 ≤ Nat.card Q := by
    rw [hQcard]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨m', hm', hγ⟩ := ih _ hlt Q rfl hQp hQ3 (x : Q) hxbar
  have hm'eq : m' = m - 1 := by
    rw [hQcard] at hm'
    exact (Nat.pow_right_injective hp.two_le hm').symm
  refine ⟨m, hm, fun hbot => hγ ?_⟩
  have hcen : (⊤ : Subgroup P).lowerCentralSeries (m - 3) ≤ Z := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro y
    have hmem : ⁅g, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (m - 3 + 1) := by
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator hg (Subgroup.mem_top y)
    rw [show m - 3 + 1 = m - 2 by omega, hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
    calc y * g = (g * y * g⁻¹ * y⁻¹)⁻¹ * (g * y) := by group
      _ = g * y := by rw [hmem, inv_one, one_mul]
  have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup P) (QuotientGroup.mk' Z) (m - 3)
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)] at hmap
  rw [hm'eq, show m - 1 - 2 = m - 3 by omega, ← hmap, eq_bot_iff]
  intro q hq
  obtain ⟨g, hg, rfl⟩ := hq
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hcen hg

end CFSG.GH74.Uniqueness.SU.SU1
