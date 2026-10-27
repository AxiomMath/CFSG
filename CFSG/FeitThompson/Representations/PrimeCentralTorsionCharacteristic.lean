module

public import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {R : Type*} [Group R]

def centerTorsionBy (R : Type*) [Group R] (n : ℕ) : Subgroup R where
  carrier := {z | z ∈ center R ∧ z ^ n = 1}
  one_mem' := ⟨one_mem _, one_pow n⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [Commute.mul_pow (mem_center_iff.mp ha b).symm, ha1, hb1, one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    exact ⟨inv_mem ha, by rw [inv_pow, ha1, inv_one]⟩

@[simp]
theorem mem_centerTorsionBy {n : ℕ} {z : R} :
    z ∈ centerTorsionBy R n ↔ z ∈ center R ∧ z ^ n = 1 := Iff.rfl

theorem centerTorsionBy_le_center (n : ℕ) : centerTorsionBy R n ≤ center R := fun _ hz => hz.1

theorem mem_center_of_mem_centerTorsionBy {n : ℕ} {z : R} (hz : z ∈ centerTorsionBy R n) :
    z ∈ center R := hz.1

theorem pow_eq_one_of_mem_centerTorsionBy {n : ℕ} {z : R} (hz : z ∈ centerTorsionBy R n) :
    z ^ n = 1 := hz.2

theorem mem_centerTorsionBy_of_mem_center {n : ℕ} {z : R} (hz : z ∈ center R) (hzn : z ^ n = 1) :
    z ∈ centerTorsionBy R n := ⟨hz, hzn⟩

instance centerTorsionBy_characteristic (n : ℕ) : (centerTorsionBy R n).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ z hz
  refine mem_centerTorsionBy.mpr ⟨?_, ?_⟩
  · exact Subgroup.characteristic_iff_le_comap.mp Subgroup.centerCharacteristic φ hz.1
  · rw [← map_pow, hz.2, map_one]

instance centerTorsionBy_isMulCommutative (n : ℕ) : IsMulCommutative (centerTorsionBy R n) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  exact (centerTorsionBy_le_center n).trans (Subgroup.center_le_centralizer _)

theorem exists_mem_centerTorsionBy_ne_one {r a : ℕ} (hr : r.Prime) (hR : Nat.card R = r ^ a)
    (ha : 1 ≤ a) : ∃ z : R, z ∈ centerTorsionBy R r ∧ z ≠ 1 := by
  obtain ⟨z, hzc, hz⟩ := exists_mem_center_orderOf_eq hr hR ha
  have hz1 : z ≠ 1 := fun h => hr.one_lt.ne (by rw [← hz, h, orderOf_one])
  exact ⟨z, mem_centerTorsionBy.mpr ⟨hzc, by rw [← hz]; exact pow_orderOf_eq_one z⟩, hz1⟩

theorem centerTorsionBy_ne_bot {r a : ℕ} (hr : r.Prime) (hR : Nat.card R = r ^ a) (ha : 1 ≤ a) :
    centerTorsionBy R r ≠ ⊥ := by
  obtain ⟨z, hz, hz1⟩ := exists_mem_centerTorsionBy_ne_one hr hR ha
  exact fun h => hz1 (by simpa [h, Subgroup.mem_bot] using hz)

theorem centerTorsionBy_nontrivial {r a : ℕ} (hr : r.Prime) (hR : Nat.card R = r ^ a)
    (ha : 1 ≤ a) : Nontrivial (centerTorsionBy R r) :=
  (Subgroup.nontrivial_iff_ne_bot _).mpr (centerTorsionBy_ne_bot hr hR ha)

theorem orderOf_eq_of_mem_centerTorsionBy {r : ℕ} (hr : r.Prime) {z : R}
    (hz : z ∈ centerTorsionBy R r) (hz1 : z ≠ 1) : orderOf z = r :=
  haveI := Fact.mk hr
  orderOf_eq_prime hz.2 hz1

theorem centerTorsionBy_spec {r a : ℕ} (hr : r.Prime) (hR : Nat.card R = r ^ a) (ha : 1 ≤ a) :
    centerTorsionBy R r ≠ ⊥ ∧ (centerTorsionBy R r).Characteristic ∧
      IsMulCommutative (centerTorsionBy R r) ∧
      ∀ z ∈ centerTorsionBy R r, z ≠ 1 → orderOf z = r :=
  ⟨centerTorsionBy_ne_bot hr hR ha, inferInstance, inferInstance,
    fun _ hz hz1 => orderOf_eq_of_mem_centerTorsionBy hr hz hz1⟩

end

end CFSG.FeitThompson
