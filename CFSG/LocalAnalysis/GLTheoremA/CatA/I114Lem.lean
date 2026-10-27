module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem zpow_eq_zpow_mod3 {G : Type} [Group G] {x : G} (hx : x ^ 3 = 1) (n : ℤ) :
    x ^ n = x ^ (n % 3) := by
  have h : n % 3 + 3 * (n / 3) = n := by omega
  calc x ^ n = x ^ (n % 3 + 3 * (n / 3)) := by rw [h]
    _ = x ^ (n % 3) * (x ^ (3 : ℤ)) ^ (n / 3) := by
      rw [zpow_add, zpow_mul]
    _ = x ^ (n % 3) := by
      have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx
      rw [h3, one_zpow, mul_one]

theorem three_dvd_of_pow_eq_conj {K : Type} [Group K] {α : MulAut K} (h3 : α ^ 3 = 1)
    (hout : ∀ k : K, α ≠ MulAut.conj k) {j : ℤ} {e : K} (hj : α ^ j = MulAut.conj e) :
    (3 : ℤ) ∣ j := by
  by_contra hdiv
  obtain ⟨j', hj'⟩ : ∃ j' : ℤ, j * j' % 3 = 1 := by
    have : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases this with h1 | h1
    · exact ⟨1, by rw [mul_one]; omega⟩
    · exact ⟨2, by omega⟩
  have hα : α = α ^ (j * j') := by
    rw [zpow_eq_zpow_mod3 h3 (j * j'), hj']
    simp
  have hαe : α = MulAut.conj (e ^ j') := by
    rw [hα, zpow_mul, hj, ← map_zpow]
  exact hout (e ^ j') hαe

theorem cj_eq_of_cent {L : Subgroup Y} {g : Y} (h : ∀ l ∈ L, l * g = g * l) : cj g L = L := by
  ext z
  rw [mem_cj]
  constructor
  · intro hz
    have hc := h _ hz
    have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [e]
    have hc' : g * (g⁻¹ * z * g) * g⁻¹ = g⁻¹ * z * g := by
      rw [← h _ hz]
      group
    rw [hc']
    exact hz
  · intro hz
    have hc : g⁻¹ * z * g = z := by
      calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
        _ = g⁻¹ * (g * z) := by rw [h z hz]
        _ = z := by group
    rw [hc]
    exact hz

end CFSG.LocalAnalysis.GLTheoremA.I114
