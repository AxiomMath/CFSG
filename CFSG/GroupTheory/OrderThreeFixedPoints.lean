module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.UCK

variable {G V : Type} [Group G] [AddCommGroup V] {q : ℕ} [Module (ZMod q) V]
  (ρ : Representation (ZMod q) G V)

private theorem mem_fixV_zpowers_iff {g : G} {v : V} :
    v ∈ fixV ρ (Subgroup.zpowers g) ↔ ρ g v = v := by
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h a ha
    exact (Representation.mem_stabilizer.mp
      (Subgroup.zpowers_le.mpr (Representation.mem_stabilizer.mpr h) ha))

private noncomputable def sumOp (g : G) : Module.End (ZMod q) V :=
  1 + ρ g + ρ g ^ 2

private theorem sumOp_fixed (g : G) (h3 : g ^ 3 = 1) (v : V) :
    ρ g (sumOp ρ g v) = sumOp ρ g v := by
  have h3' : (ρ g) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hsq : ρ g * ρ g ^ 2 = 1 := by
    rw [pow_two, ← pow_three, h3']
  have hop : ρ g * sumOp ρ g = sumOp ρ g := by
    simp only [sumOp]
    calc ρ g * (1 + ρ g + ρ g ^ 2)
        = ρ g + ρ g * ρ g + ρ g * ρ g ^ 2 := by noncomm_ring
      _ = ρ g + ρ g * ρ g + 1 := by rw [hsq]
      _ = 1 + ρ g + ρ g ^ 2 := by rw [pow_two]; abel
  rw [← Module.End.mul_apply, hop]

private theorem sumOp_eq_zero (g : G) (h3 : g ^ 3 = 1)
    (hfix : fixV ρ (Subgroup.zpowers g) = ⊥) (v : V) :
    sumOp ρ g v = 0 := by
  have hmem : sumOp ρ g v ∈ fixV ρ (Subgroup.zpowers g) :=
    (mem_fixV_zpowers_iff ρ).mpr (sumOp_fixed ρ g h3 v)
  rw [hfix, Submodule.mem_bot] at hmem
  exact hmem

private theorem sumOp_add_expansion (x y : G) (hy3 : y ^ 3 = 1)
    (hxy : Commute x y) :
    sumOp ρ x + sumOp ρ y + sumOp ρ (x * y) + sumOp ρ (x * y ^ 2) =
      (1 + 1 + 1 : Module.End (ZMod q) V) + sumOp ρ x * sumOp ρ y := by
  have hy3' : (ρ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hcomm : Commute (ρ x) (ρ y) := hxy.map ρ
  have hcomm2 : Commute (ρ x) ((ρ y) ^ 2) := hcomm.pow_right 2
  have hxy2 : (ρ x * ρ y) ^ 2 = (ρ x) ^ 2 * (ρ y) ^ 2 := hcomm.mul_pow 2
  have hy4 : (ρ y) ^ 4 = ρ y := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hy3', one_mul]
  have hy22 : ((ρ y) ^ 2) ^ 2 = ρ y := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, hy4]
  have hxy22 : (ρ x * (ρ y) ^ 2) ^ 2 = (ρ x) ^ 2 * ρ y := by
    rw [hcomm2.mul_pow 2, hy22]
  have hxy : sumOp ρ (x * y) = 1 + ρ x * ρ y + (ρ x) ^ 2 * (ρ y) ^ 2 := by
    simp only [sumOp, map_mul]
    rw [hxy2]
  have hxyi : sumOp ρ (x * y ^ 2) = 1 + ρ x * (ρ y) ^ 2 + (ρ x) ^ 2 * ρ y := by
    simp only [sumOp, map_mul, map_pow]
    rw [hxy22]
  have hprod : sumOp ρ x * sumOp ρ y =
      1 + ρ y + (ρ y) ^ 2 + ρ x + ρ x * ρ y + ρ x * (ρ y) ^ 2 + (ρ x) ^ 2 +
        (ρ x) ^ 2 * ρ y + (ρ x) ^ 2 * (ρ y) ^ 2 := by
    simp only [sumOp]
    noncomm_ring
  rw [hxy, hxyi, hprod]
  simp only [sumOp]
  abel

private theorem sumOp_expansion_apply (x y : G) (hy3 : y ^ 3 = 1)
    (hxy : Commute x y) (v : V) :
    sumOp ρ x v + sumOp ρ y v + sumOp ρ (x * y) v + sumOp ρ (x * y ^ 2) v =
      v + v + v + sumOp ρ x (sumOp ρ y v) := by
  have h := congrArg (fun f : Module.End (ZMod q) V => f v)
    (sumOp_add_expansion ρ x y hy3 hxy)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using h

theorem fixV_zpowers_eq_top_of_commute_of_pow_three
    (hq : q.Prime) (hq3 : q ≠ 3) {x y : G} (hxy : Commute x y)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hx : fixV ρ (Subgroup.zpowers x) = ⊥)
    (hxy_fix : fixV ρ (Subgroup.zpowers (x * y)) = ⊥)
    (hxyi_fix : fixV ρ (Subgroup.zpowers (x * y⁻¹)) = ⊥) :
    fixV ρ (Subgroup.zpowers y) = ⊤ := by
  have hyinv : y⁻¹ = y ^ 2 := by
    calc y⁻¹ = y⁻¹ * y ^ 3 := by rw [hy3, mul_one]
      _ = y ^ 2 := by group
  have hxy3 : (x * y) ^ 3 = 1 := by rw [hxy.mul_pow, hx3, hy3, mul_one]
  have hxyi3 : (x * y⁻¹) ^ 3 = 1 := by
    rw [hxy.inv_right.mul_pow, hx3, inv_pow, hy3, inv_one, mul_one]
  have h3unit : IsUnit (3 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 3 q).mpr
      ((Nat.coprime_primes Nat.prime_three hq).mpr (fun h => hq3 h.symm))
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq.ne_one
  have h3ne : (3 : ZMod q) ≠ 0 := h3unit.ne_zero
  haveI : Fact q.Prime := ⟨hq⟩
  have hmain : ∀ v : V, ρ y v = v := by
    intro v
    have hx0 : sumOp ρ x v = 0 := sumOp_eq_zero ρ x hx3 hx v
    have hxy0 : sumOp ρ (x * y) v = 0 := sumOp_eq_zero ρ (x * y) hxy3 hxy_fix v
    have hxyi0 : sumOp ρ (x * y⁻¹) v = 0 :=
      sumOp_eq_zero ρ (x * y⁻¹) hxyi3 hxyi_fix v
    rw [hyinv] at hxyi0
    have hSxSy : sumOp ρ x (sumOp ρ y v) = 0 := sumOp_eq_zero ρ x hx3 hx _
    have hexp := sumOp_expansion_apply ρ x y hy3 hxy v
    rw [hx0, hxy0, hxyi0, hSxSy] at hexp
    have hSy3 : sumOp ρ y v = v + v + v := by
      simpa only [zero_add, add_zero] using hexp
    have hSy : sumOp ρ y v = (3 : ZMod q) • v := by
      rw [hSy3, ← three'_nsmul]
      exact (Nat.cast_smul_eq_nsmul (R := ZMod q) 3 v).symm
    have hfix := sumOp_fixed ρ y hy3 v
    rw [hSy, map_smul] at hfix
    exact smul_right_injective (M := V) h3ne hfix
  have hy1 : ρ y = 1 := LinearMap.ext hmain
  rw [eq_top_iff]
  intro v _
  exact (mem_fixV_zpowers_iff ρ).mpr (by rw [hy1, Module.End.one_apply])

end CFSG.GroupTheory

end
