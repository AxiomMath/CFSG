module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP6Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Tools

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X] {t z : G} {T : Subgroup G}
  {π : ↥(centralizer ({z} : Set G)) →* X}

private theorem sec5op5_odd_orderOf_mul {G : Type*} [Group G] {V : Subgroup G} {v y : G}
    (hV : Odd (Nat.card V)) (hv : v ∈ V)
    (hnorm : ∀ w ∈ V, y * w * y⁻¹ ∈ V) (hy : Odd (orderOf y)) :
    Odd (orderOf (v * y)) := by
  have hnorm_pow : ∀ i : ℕ, ∀ w ∈ V, y ^ i * w * (y ^ i)⁻¹ ∈ V := by
    intro i
    induction i with
    | zero => intro w hw; simpa using hw
    | succ i ih =>
        intro w hw
        have h1 : y ^ (i + 1) * w * (y ^ (i + 1))⁻¹ =
            y * (y ^ i * w * (y ^ i)⁻¹) * y⁻¹ := by
          rw [pow_succ']; group
        rw [h1]
        exact hnorm _ (ih w hw)
  have hpow : ∀ i : ℕ, ∃ w ∈ V, (v * y) ^ i = w * y ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, V.one_mem, by simp⟩
    | succ i ih =>
        obtain ⟨w, hw, hw_eq⟩ := ih
        refine ⟨w * (y ^ i * v * (y ^ i)⁻¹), V.mul_mem hw (hnorm_pow i v hv), ?_⟩
        rw [pow_succ, hw_eq]; group
  obtain ⟨w, hw, hw_eq⟩ := hpow (orderOf y)
  have hmem : (v * y) ^ orderOf y ∈ V := by
    rw [hw_eq, pow_orderOf_eq_one y, mul_one]
    exact hw
  have hpow2 : (v * y) ^ (orderOf y * Nat.card V) = 1 := by
    rw [pow_mul]
    have h := pow_card_eq_one' (x := (⟨(v * y) ^ orderOf y, hmem⟩ : ↥V))
    have h' : ((v * y) ^ orderOf y) ^ Nat.card V = 1 := by
      simpa only [Subgroup.coe_pow, Subtype.coe_mk, Subgroup.coe_one] using
        congrArg Subtype.val h
    exact h'
  exact (hy.mul hV).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow2)

theorem sec5op_lift_odd (hyp : Sec5OPHyp t z T π) (c : Sec5GBar (sec5op_Tb z T π))
    (hc : Odd (orderOf c))
    (hct : c * sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ =
      sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ * c) :
    ∃ (y : G) (hy : y ∈ sec5op_Y t z), y * t = t * y ∧ Odd (orderOf y) ∧
      sec5op_cls hyp ⟨y, hy⟩ = c := by
  have htY : t ∈ sec5op_Y t z := sec5op_t_mem_Y t z
  obtain ⟨y0, hy0⟩ := sec5op_cls_surjective hyp c
  obtain ⟨g, hgodd, hgimg⟩ := CFSG.ComponentClassification.GSThmB.exists_pow_odd_orderOf_map_eq
    (sec5op_cls hyp) y0 (by rwa [hy0])
  let y1 : G := (y0 ^ g : ↥(sec5op_Y t z))
  have hy1 : y1 ∈ sec5op_Y t z := (y0 ^ g).2
  have hy1odd : Odd (orderOf y1) := by
    rw [show y1 = ((y0 ^ g : ↥(sec5op_Y t z)) : G) from rfl, Subgroup.orderOf_coe]
    exact hgodd
  have hcls_y1 : sec5op_cls hyp ⟨y1, hy1⟩ = c := by
    have heq : (⟨y1, hy1⟩ : ↥(sec5op_Y t z)) = y0 ^ g := Subtype.ext rfl
    rw [heq, hgimg, hy0]
  let a : G := y1 * t * y1⁻¹ * t⁻¹
  have haY : a ∈ sec5op_Y t z :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy1 htY) (Subgroup.inv_mem _ hy1))
      (Subgroup.inv_mem _ htY)
  have hcls_a : sec5op_cls hyp ⟨a, haY⟩ = 1 := by
    have hEq : (⟨a, haY⟩ : ↥(sec5op_Y t z)) =
        ⟨y1, hy1⟩ * ⟨t, htY⟩ * ⟨y1, hy1⟩⁻¹ * ⟨t, htY⟩⁻¹ := Subtype.ext rfl
    rw [hEq]
    simp only [map_mul, map_inv, hcls_y1]
    rw [hct]; group
  have haW : a ∈ sec5op_W hyp := (sec5op_mem_W_iff hyp).mpr ⟨haY, hcls_a⟩
  obtain ⟨e, n, hn, haeq⟩ := sec5op_W_decomp hyp haW
  have hz2 : z * z = 1 := by rw [← pow_two, ← hyp.hz]; exact pow_orderOf_eq_one z
  have hy1H : y1 ∈ centralizer ({z} : Set G) := sec5op_Y_le hyp.tH hy1
  have hNz : ∀ n ∈ sec5op_N hyp, n * z = z * n := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mp (sec5op_N_le_H hyp hn)
  have hNy : ∀ n ∈ sec5op_N hyp, y1 * n * y1⁻¹ ∈ sec5op_N hyp := fun n hn =>
    sec5op_N_normal hyp hy1H hn
  have haN : a ∈ sec5op_N hyp :=
    sec5op_odd_comm_trick hz2 (Subgroup.mem_centralizer_singleton_iff.mp hy1H) hNz hNy
      (sec5op_N_odd hyp) hy1odd ⟨e, n, hn, haeq⟩
  have ht2 : t * t = 1 := by rw [← pow_two, ← hyp.ht]; exact pow_orderOf_eq_one t
  obtain ⟨m, hm, hfix⟩ := sec5op6_exists_fix ht2 (sec5op_N_odd hyp) haN
  have hmW : m ∈ sec5op_W hyp := (Subgroup.mem_inf.mp hm).2
  have hmY : m ∈ sec5op_Y t z := sec5op_W_le_Y hyp hmW
  have hy : m * y1 ∈ sec5op_Y t z := Subgroup.mul_mem _ hmY hy1
  have hcomm : (m * y1) * t = t * (m * y1) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hodd : Odd (orderOf (m * y1)) :=
    sec5op5_odd_orderOf_mul (sec5op_N_odd hyp) hm hNy hy1odd
  refine ⟨m * y1, hy, hcomm, hodd, ?_⟩
  have hcls_m : sec5op_cls hyp ⟨m, hmY⟩ = 1 := by
    obtain ⟨hx, hx1⟩ := (sec5op_mem_W_iff hyp).mp hmW
    have heq : (⟨m, hmY⟩ : ↥(sec5op_Y t z)) = ⟨m, hx⟩ := Subtype.ext rfl
    rw [heq]; exact hx1
  have heq : (⟨m * y1, hy⟩ : ↥(sec5op_Y t z)) = ⟨m, hmY⟩ * ⟨y1, hy1⟩ := Subtype.ext rfl
  rw [heq, map_mul, hcls_m, one_mul]
  exact hcls_y1

end CFSG.OddStandard.SmallF3.Omega
