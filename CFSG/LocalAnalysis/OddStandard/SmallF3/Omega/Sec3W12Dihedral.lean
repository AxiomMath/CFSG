module

public import CFSG.GroupTheory.CentralizerMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem conj_pow_mul_eq_inv {a b : G} (ha : a * a = 1) (hb : b * b = 1) (j : ℕ) :
    a * (a * b) ^ j * a⁻¹ = ((a * b) ^ j)⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc a a b, ha, one_mul]
  rw [← conj_pow, h1, inv_pow]

theorem exists_pow_inv_conj_of_odd_orderOf_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) :
    ∃ n : ℕ, ((a * b) ^ n)⁻¹ * a * (((a * b) ^ n)⁻¹)⁻¹ = b := by
  obtain ⟨m, hm⟩ := hodd
  have hc : (a * b) ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one (a * b)
  have h1 : a * (a * b) ^ (m + 1) * a⁻¹ = ((a * b) ^ (m + 1))⁻¹ :=
    conj_pow_mul_eq_inv ha hb (m + 1)
  have h2 : a * (a * b) ^ (m + 1) = ((a * b) ^ (m + 1))⁻¹ * a := by
    calc a * (a * b) ^ (m + 1) = (a * (a * b) ^ (m + 1) * a⁻¹) * a := by group
      _ = ((a * b) ^ (m + 1))⁻¹ * a := by rw [h1]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  refine ⟨m + 1, ?_⟩
  calc ((a * b) ^ (m + 1))⁻¹ * a * (((a * b) ^ (m + 1))⁻¹)⁻¹
      = ((a * b) ^ (m + 1))⁻¹ * (a * (a * b) ^ (m + 1)) := by group
    _ = ((a * b) ^ (m + 1) * (a * b) ^ (m + 1))⁻¹ * a := by rw [h2, mul_inv_rev, mul_assoc]
    _ = (a * b)⁻¹ * a := by
        rw [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hc, one_mul]
    _ = b := by rw [mul_inv_rev, inv_mul_cancel_right, hbinv]

theorem exists_pow_involution_of_even_orderOf_mul [Finite G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hev : Even (orderOf (a * b))) :
    ∃ n : ℕ, orderOf ((a * b) ^ n) = 2 ∧ a * (a * b) ^ n = (a * b) ^ n * a ∧
      b * (a * b) ^ n = (a * b) ^ n * b := by
  have hpos : orderOf (a * b) ≠ 0 := (orderOf_pos (a * b)).ne'
  have hdvd : 2 ∣ orderOf (a * b) := even_iff_two_dvd.mp hev
  have hz : orderOf ((a * b) ^ (orderOf (a * b) / 2)) = 2 := orderOf_pow_orderOf_div hpos hdvd
  refine ⟨orderOf (a * b) / 2, hz, ?_⟩
  set n := orderOf (a * b) / 2 with hn
  have hz2 : (a * b) ^ n * (a * b) ^ n = 1 := by
    rw [← pow_two]
    exact hz ▸ pow_orderOf_eq_one _
  have hzinv : ((a * b) ^ n)⁻¹ = (a * b) ^ n := inv_eq_of_mul_eq_one_right hz2
  have hza : a * (a * b) ^ n = (a * b) ^ n * a := by
    have h1 := conj_pow_mul_eq_inv ha hb n
    rw [hzinv] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hca : Commute ((a * b) ^ n) a := hza.symm
  have hcc : Commute ((a * b) ^ n) (a * b) := (Commute.refl (a * b)).pow_left n
  have hbeq : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hcb : Commute ((a * b) ^ n) b := by
    have h := hca.mul_right hcc
    rwa [hbeq] at h
  exact ⟨hza, hcb.symm.eq⟩

theorem IsComponentIn.of_conj_centralizer {X : Subgroup G} {x₀ k : G}
    (h : IsComponentIn X (centralizer ({x₀} : Set G))) (hk : k ∈ centralizer (X : Set G)) :
    IsComponentIn X (centralizer ({k * x₀ * k⁻¹} : Set G)) := by
  have hmap := h.map_mulEquiv (MulAut.conj k)
  rw [CFSG.centralizer_singleton_map (MulAut.conj k) x₀, MulAut.conj_apply] at hmap
  have hX : X.map (MulAut.conj k).toMonoidHom = X := by
    have hfix : ∀ a ∈ X, k * a * k⁻¹ = a := by
      intro a ha
      have hak : a * k = k * a := Subgroup.mem_centralizer_iff.mp hk a ha
      rw [← hak, mul_inv_cancel_right]
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hfix a ha]
      exact ha
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  rwa [hX] at hmap

end CFSG.OddStandard.SmallF3.Omega
