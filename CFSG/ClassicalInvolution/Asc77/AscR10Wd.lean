module

public import CFSG.ClassicalInvolution.Asc77.AscT3VConj
public import CFSG.ClassicalInvolution.AschTight.S1911F0a

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Pure

variable {G : Type} [Group G]

theorem r_zpow_pow_comm (g : G) (i : ℤ) (N : ℕ) : (g ^ i) ^ N = (g ^ N) ^ i := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem r_zpow_invol {g : G} (hg : g * g = 1) (i : ℤ) : g ^ i = 1 ∨ g ^ i = g := by
  obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' i
  · left
    rw [zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hg, one_zpow, one_mul]

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}




theorem Std20.r_W_exp (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) :
    ∀ w ∈ W, w ^ (2 ^ (k + 1)) = 1 := by
  obtain ⟨v₀, -, hv₀o, -, -, hWgen, huv, -⟩ := d.v_W_gen hu huo
  intro w hw
  rw [hWgen] at hw
  obtain ⟨i, j, rfl⟩ := T3V.mem_sup_zpowers_of_commute huv hw
  have hc : Commute (u ^ i) (v₀ ^ j) := (show Commute u v₀ from huv).zpow_zpow i j
  have hu1 : u ^ (2 ^ (k + 1)) = 1 := by rw [← huo]; exact pow_orderOf_eq_one u
  have hv1 : v₀ ^ (2 ^ (k + 1)) = 1 := by rw [← hv₀o]; exact pow_orderOf_eq_one v₀
  rw [hc.mul_pow, r_zpow_pow_comm, r_zpow_pow_comm, hu1, hv1, one_zpow, one_zpow, mul_one]

theorem Std20.r_W_pow_cases (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) :
    ∀ w ∈ W, w ^ (2 ^ k) = 1 ∨ w ^ (2 ^ k) = z ∨ w ^ (2 ^ k) = t ∨ w ^ (2 ^ k) = z * t := by
  obtain ⟨v₀, -, -, hv₀t, huz, hWgen, huv, -⟩ := d.v_W_gen hu huo
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  intro w hw
  rw [hWgen] at hw
  obtain ⟨i, j, rfl⟩ := T3V.mem_sup_zpowers_of_commute huv hw
  have hc : Commute (u ^ i) (v₀ ^ j) := (show Commute u v₀ from huv).zpow_zpow i j
  rw [hc.mul_pow, r_zpow_pow_comm, r_zpow_pow_comm, huz, hv₀t]
  rcases r_zpow_invol hz2 i with h1 | h1 <;> rcases r_zpow_invol ht2 j with h2 | h2 <;>
    simp [h1, h2]

theorem Std20.r_W_invol (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) :
    ∀ w ∈ W, w * w = 1 → w = 1 ∨ w = z ∨ w = t ∨ w = z * t := by
  obtain ⟨v₀, hv₀, -, -, -, hWgen, huv, hdis⟩ := d.v_W_gen hu huo
  intro w hw hw2
  rw [hWgen] at hw
  obtain ⟨i, j, rfl⟩ := T3V.mem_sup_zpowers_of_commute huv hw
  have hc : Commute (u ^ i) (v₀ ^ j) := (show Commute u v₀ from huv).zpow_zpow i j
  have huK : u ∈ K := (hu ▸ Subgroup.mem_zpowers u : u ∈ K ⊓ W).1
  have hvJ : v₀ ∈ J := (hv₀ ▸ Subgroup.mem_zpowers v₀ : v₀ ∈ J ⊓ W).1
  have haK : u ^ i ∈ K := K.zpow_mem huK i
  have hbJ : v₀ ^ j ∈ J := J.zpow_mem hvJ j
  have h1 : (u ^ i * u ^ i) * (v₀ ^ j * v₀ ^ j) = 1 := by
    rw [← hw2]
    calc (u ^ i * u ^ i) * (v₀ ^ j * v₀ ^ j) = u ^ i * (u ^ i * v₀ ^ j) * v₀ ^ j := by group
      _ = u ^ i * (v₀ ^ j * u ^ i) * v₀ ^ j := by rw [hc.eq]
      _ = (u ^ i * v₀ ^ j) * (u ^ i * v₀ ^ j) := by group
  have h2 : u ^ i * u ^ i = 1 := by
    have hmem : u ^ i * u ^ i ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v₀ := by
      refine ⟨(Subgroup.zpowers u).mul_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) i)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) i), ?_⟩
      have : u ^ i * u ^ i = ((v₀ ^ j * v₀ ^ j))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (Subgroup.zpowers v₀).inv_mem ((Subgroup.zpowers v₀).mul_mem
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v₀) j)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v₀) j))
    rw [hdis] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h3 : v₀ ^ j * v₀ ^ j = 1 := by rw [h2, one_mul] at h1; exact h1
  have hA := d.viol.hzK.unique _ haK h2
  have hB := d.viol.hzJ.unique _ hbJ h3
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
