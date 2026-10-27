module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

theorem sylow_le_iff_card {U : Type*} [CommGroup U] [Finite U] [IsCyclic U] {r : ℕ}
    [hr : Fact r.Prime] {a m : ℕ} (hm : 0 < m) (μ Zu Du : Subgroup U) (hμ : Nat.card μ = r ^ a)
    (hUa : padicValNat r (Nat.card U) = a) (hZD : Zu ≤ Du) (hDm : ∀ u ∈ Du, u ^ m = 1)
    (hDu : ∀ u ∈ μ, u ^ m = 1 → u ∈ Du) :
    μ ≤ Zu ↔ (¬ r ∣ Nat.card Du / Nat.card Zu ∧ a ≤ padicValNat r m) := by
  have hZDcard : Nat.card Zu ∣ Nat.card Du := Subgroup.card_dvd_of_le hZD
  obtain ⟨n, hn⟩ := hZDcard
  have hZpos : 0 < Nat.card Zu := Nat.card_pos
  have hnn : Nat.card Du / Nat.card Zu = n := by
    rw [hn]
    exact Nat.mul_div_cancel_left _ hZpos
  rw [hnn]
  constructor
  · intro hμZ
    have hμD : μ ≤ Du := hμZ.trans hZD
    refine ⟨?_, ?_⟩
    · intro hrn
      have h1 : r ^ a ∣ Nat.card Zu := by
        rw [← hμ]
        exact Subgroup.card_dvd_of_le hμZ
      have h2 : r ^ (a + 1) ∣ Nat.card Du := by
        rw [hn, pow_succ]
        exact mul_dvd_mul h1 hrn
      have h3 : r ^ (a + 1) ∣ Nat.card U := h2.trans (Subgroup.card_subgroup_dvd_card Du)
      have h4 := (padicValNat_dvd_iff_le (p := r) (Nat.card_pos (α := U)).ne').1 h3
      omega
    ·
      haveI : IsCyclic μ := Subgroup.isCyclic μ
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := μ)
      have hord : orderOf g = r ^ a := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, hμ]
      have hgm : (g : U) ^ m = 1 := hDm _ (hμD g.2)
      have hgm' : g ^ m = 1 := Subtype.ext hgm
      have h1 : r ^ a ∣ m := hord ▸ orderOf_dvd_of_pow_eq_one hgm'
      exact (padicValNat_dvd_iff_le (p := r) hm.ne').1 h1
  · rintro ⟨hrn, hav⟩
    have h1 : r ^ a ∣ m := (padicValNat_dvd_iff_le (p := r) hm.ne').2 hav
    have hμD : μ ≤ Du := by
      intro u hu
      apply hDu u hu
      have h2 : (⟨u, hu⟩ : μ) ^ (r ^ a) = 1 := by
        rw [← hμ]
        exact pow_card_eq_one'
      have h3 : u ^ (r ^ a) = 1 := congrArg Subtype.val h2
      obtain ⟨c, hc⟩ := h1
      rw [hc, pow_mul, h3, one_pow]
    have h2 : r ^ a ∣ Nat.card Du := hμ ▸ Subgroup.card_dvd_of_le hμD
    have hcop : Nat.Coprime (r ^ a) n :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hrn)
    rw [hn] at h2
    have h3 : r ^ a ∣ Nat.card Zu := hcop.dvd_of_dvd_mul_right h2
    rw [IsCyclic.subgroup_le_iff_card_dvd, hμ]
    exact h3

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
