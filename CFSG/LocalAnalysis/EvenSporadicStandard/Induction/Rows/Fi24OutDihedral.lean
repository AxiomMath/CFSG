module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

variable {G : Type*} [Group G]

theorem fi24out_odd_dihedral {a a' : G} (ha : a * a = 1) (ha' : a' * a' = 1) {n : ℕ}
    (hn : Odd n) (hx : (a * a') ^ n = 1) :
    ∃ c ∈ zpowers (a * a'), c * a * c⁻¹ = a' := by
  obtain ⟨s, rfl⟩ := hn
  set x := a * a' with hxdef
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hai' : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'
  have hinv : a * x * a⁻¹ = x⁻¹ := by
    rw [hxdef, mul_inv_rev, hai, hai']
    calc a * (a * a') * a = (a * a) * a' * a := by group
      _ = a' * a := by rw [ha, one_mul]
  have hpow : ∀ k : ℤ, a * x ^ k * a⁻¹ = x ^ (-k) := by
    intro k
    calc a * x ^ k * a⁻¹ = (a * x * a⁻¹) ^ k := (conj_zpow).symm
      _ = x ^ (-k) := by rw [hinv, inv_zpow']
  have hx2 : x ^ (2 * s) = x⁻¹ := by
    have h1 : x ^ (2 * s) * x = 1 := by rw [← pow_succ]; exact hx
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨x ^ s, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) s, ?_⟩
  have h1 : a * (x ^ s)⁻¹ * a⁻¹ = x ^ s := by
    have := hpow (-(s : ℤ))
    rw [zpow_neg, zpow_natCast, neg_neg, zpow_natCast] at this
    exact this
  calc x ^ s * a * (x ^ s)⁻¹ = x ^ s * (a * (x ^ s)⁻¹ * a⁻¹) * a := by group
    _ = x ^ s * x ^ s * a := by rw [h1]
    _ = x ^ (2 * s) * a := by rw [← pow_add, two_mul]
    _ = x⁻¹ * a := by rw [hx2]
    _ = a' := by
      rw [hxdef, mul_inv_rev, hai, hai']
      calc a' * a * a = a' * (a * a) := by group
        _ = a' := by rw [ha, mul_one]

theorem fi24out_odd_dihedral_commute {a b : G} (ha : a * a = 1) (hb : b * b = 1) {n : ℕ}
    (hn : Odd n) (hx : ((a * b) * (a * b)) ^ n = 1) :
    ∃ e ∈ zpowers ((a * b) * (a * b)), (e * a * e⁻¹) * b = b * (e * a * e⁻¹) := by
  set x := (a * b) * (a * b) with hxdef
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hbab : (b * a * b) * (b * a * b) = 1 := by
    calc (b * a * b) * (b * a * b) = b * (a * (b * b) * a) * b := by group
      _ = 1 := by rw [hb, mul_one, ha, mul_one, hb]
  have hprod : a * (b * a * b) = x := by
    rw [hxdef]; group
  obtain ⟨c, hc, hca⟩ := fi24out_odd_dihedral ha hbab hn (by rw [hprod]; exact hx)
  rw [hprod] at hc
  have hbx : b * x * b⁻¹ = x⁻¹ := by
    rw [hxdef, hbi]
    calc b * (a * b * (a * b)) * b = (b * a * b) * (a * (b * b)) := by group
      _ = b * a * b * a := by rw [hb, mul_one]
      _ = (a * b * (a * b))⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, hbi, inv_eq_of_mul_eq_one_right ha]; group
  have hbc : ∀ k : ℤ, b * x ^ k * b⁻¹ = x ^ (-k) := by
    intro k
    calc b * x ^ k * b⁻¹ = (b * x * b⁻¹) ^ k := (conj_zpow).symm
      _ = x ^ (-k) := by rw [hbx, inv_zpow']
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc
  obtain ⟨s, rfl⟩ := hn
  have hxn : x ^ (2 * s + 1) = 1 := hx
  refine ⟨x ^ (j * (s + 1 : ℕ)), ?_, ?_⟩
  · exact zpow_mem (mem_zpowers x) _
  · set e := x ^ (j * ((s + 1 : ℕ) : ℤ)) with he
    have hx' : x ^ ((2 * s + 1 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hxn
    have he2 : e * e = x ^ j := by
      rw [he, ← zpow_add]
      have : j * ((s + 1 : ℕ) : ℤ) + j * ((s + 1 : ℕ) : ℤ) = ((2 * s + 1 : ℕ) : ℤ) * j + j := by
        push_cast; ring
      rw [this, zpow_add, zpow_mul, hx', one_zpow, one_mul]
    have hbe : b * e * b = e⁻¹ := by
      have h0 : b * e * b⁻¹ = e⁻¹ := by rw [he, hbc, zpow_neg]
      rwa [hbi] at h0
    have hbe' : b * e⁻¹ * b = e := by
      calc b * e⁻¹ * b = (b * e * b)⁻¹ := by simp only [mul_inv_rev, hbi, mul_assoc]
        _ = e := by rw [hbe, inv_inv]
    have hcb : e * e * a * (e * e)⁻¹ = b * a * b := by
      have := hca
      rwa [← he2] at this
    have key : b * (e * a * e⁻¹) * b = e * a * e⁻¹ := by
      calc b * (e * a * e⁻¹) * b
          = (b * e * b) * (b * a * b) * (b * e⁻¹ * b) := by
            calc b * (e * a * e⁻¹) * b = b * e * (b * b) * a * (b * b) * e⁻¹ * b := by
                  rw [hb]; group
              _ = _ := by group
        _ = e⁻¹ * (e * e * a * (e * e)⁻¹) * e := by rw [hbe, hbe', hcb]
        _ = e * a * e⁻¹ := by group
    calc (e * a * e⁻¹) * b = b * (b * (e * a * e⁻¹) * b) := by
          calc (e * a * e⁻¹) * b = (b * b) * (e * a * e⁻¹) * b := by rw [hb, one_mul]
            _ = _ := by group
      _ = b * (e * a * e⁻¹) := by rw [key]

end CFSG.EvenSporadicStandard.Induction
