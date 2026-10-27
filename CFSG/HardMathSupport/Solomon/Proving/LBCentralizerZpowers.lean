module

public import CFSG.HardMathSupport.Timmesfeld.Proving.CentreComponentPGroup

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open

variable {Y : Type} [Group Y]

theorem mem_zpowers_of_mem_zpowers_ne_one {x y : Y} (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : x ∈ Subgroup.zpowers y := by
  have hx3z : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx3]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk3 : k % 3 ≠ 0 := by
    intro h0
    apply hy1
    rw [show k = 3 * (k / 3) by omega, zpow_mul, hx3z, one_zpow]
  obtain ⟨q, hq | hq⟩ : ∃ q : ℤ, k = 3 * q + 1 ∨ k = 3 * q + 2 := ⟨k / 3, by omega⟩
  · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hkk : k * k = 1 + 3 * (3 * q ^ 2 + 2 * q) := by rw [hq]; ring
    rw [← zpow_mul, hkk, zpow_add, zpow_mul, hx3z, one_zpow, mul_one, zpow_one]
  · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hkk : k * k = 1 + 3 * (3 * q ^ 2 + 4 * q + 1) := by rw [hq]; ring
    rw [← zpow_mul, hkk, zpow_add, zpow_mul, hx3z, one_zpow, mul_one, zpow_one]

theorem conj_mem_centralizer_singleton {x g n : Y} (hx3 : x ^ 3 = 1)
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Y) : Set Y))
    (hn : n ∈ Subgroup.centralizer ({x} : Set Y)) :
    g * n * g⁻¹ ∈ Subgroup.centralizer ({x} : Set Y) := by
  have hxn : x * n = n * x := Subgroup.mem_centralizer_iff.mp hn x (Set.mem_singleton x)
  have hy : g * x * g⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp hg x).mp (Subgroup.mem_zpowers x)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  by_cases hy1 : g * x * g⁻¹ = 1
  · have hx1 : x = 1 := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [hy1]; group
    rw [hx1]
    simp
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_mem_zpowers_ne_one hx3 hy hy1)
    have hcomm : (g * x * g⁻¹) * (g * n * g⁻¹) = (g * n * g⁻¹) * (g * x * g⁻¹) := by
      calc g * x * g⁻¹ * (g * n * g⁻¹) = g * (x * n) * g⁻¹ := by group
        _ = g * (n * x) * g⁻¹ := by rw [hxn]
        _ = g * n * g⁻¹ * (g * x * g⁻¹) := by group
    have hd : Commute (g * n * g⁻¹) (g * x * g⁻¹) := hcomm.symm
    have hdx : Commute (g * n * g⁻¹) x := by
      rw [← hk]
      exact hd.zpow_right k
    exact hdx.eq.symm

theorem centralizer_subgroupOf_normalizer_normal {x : Y} (hx3 : x ^ 3 = 1) :
    ((Subgroup.centralizer ({x} : Set Y)).subgroupOf
      (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Y) : Set Y))).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_centralizer_singleton hx3 g.2 hn⟩

theorem centralizer_le_normalizer_zpowers {x : Y} :
    Subgroup.centralizer ({x} : Set Y) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Y) : Set Y) := by
  intro c hc
  have hcx0 : Commute c x := (Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hcxk : Commute c (x ^ k) := hcx0.zpow_right k
    have e : c * x ^ k * c⁻¹ = x ^ k := by
      rw [hcxk.eq]
      group
    rw [e]
    exact hh
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hcxk : Commute c (x ^ k) := hcx0.zpow_right k
    have e : c⁻¹ * x ^ k * c = x ^ k := by
      rw [(hcxk.inv_left).eq]
      group
    have hh' : h = x ^ k := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
        _ = c⁻¹ * x ^ k * c := by rw [hk]
        _ = x ^ k := e
    rw [hh']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k

theorem glapPrimeCoreOf_centralizer_le_normalizer [Finite Y] {p : ℕ} (hp : p.Prime)
    {x : Y} (hx3 : x ^ 3 = 1) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set Y)) ≤
      GLAPPrimeCoreOf p (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Y) : Set Y)) :=
  CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le_of_normal_sub hp
    (centralizer_le_normalizer_zpowers (x := x)) (centralizer_subgroupOf_normalizer_normal hx3)

end CFSG.HardMathSupport.Solomon.Proving

end
