module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma t3_z2z4_sq_eq_one_iff (z : Z 2 × Z 4) :
    z ^ 2 = 1 ↔
      z = 1 ∨ z = (Multiplicative.ofAdd (1 : ZMod 2), 1) ∨
        z = (1, Multiplicative.ofAdd (2 : ZMod 4)) ∨
        z = (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (2 : ZMod 4)) := by
  revert z
  decide

theorem tableIII_Z2Z4_eq_of_sq_eq_one {x y w : Z 2 × Z 4} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hw : w ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  rcases (t3_z2z4_sq_eq_one_iff x).mp hx with rfl | rfl | rfl | rfl <;>
    rcases (t3_z2z4_sq_eq_one_iff y).mp hy with rfl | rfl | rfl | rfl <;>
    rcases (t3_z2z4_sq_eq_one_iff w).mp hw with rfl | rfl | rfl | rfl <;>
    first | decide | simp_all

theorem tableIII_eq_of_mulEquiv_Z2Z4 {G : Type*} [Group G] {C : Subgroup G}
    (e : ↥C ≃* Z 2 × Z 4) {x y w : G} (hxC : x ∈ C) (hyC : y ∈ C) (hwC : w ∈ C)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hw : w ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x ≠ y) : w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  have hx' : (⟨x, hxC⟩ : ↥C) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hx
  have hy' : (⟨y, hyC⟩ : ↥C) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hy
  have hw' : (⟨w, hwC⟩ : ↥C) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hw
  have hx1' : (⟨x, hxC⟩ : ↥C) ≠ 1 := by
    intro h
    exact hx1 (by simpa using congrArg Subtype.val h)
  have hy1' : (⟨y, hyC⟩ : ↥C) ≠ 1 := by
    intro h
    exact hy1 (by simpa using congrArg Subtype.val h)
  have hxy' : (⟨x, hxC⟩ : ↥C) ≠ (⟨y, hyC⟩ : ↥C) := by
    intro h
    exact hxy (by simpa using congrArg Subtype.val h)
  have h2x : (e ⟨x, hxC⟩) ^ 2 = 1 := by rw [← map_pow, hx', map_one]
  have h2y : (e ⟨y, hyC⟩) ^ 2 = 1 := by rw [← map_pow, hy', map_one]
  have h2w : (e ⟨w, hwC⟩) ^ 2 = 1 := by rw [← map_pow, hw', map_one]
  have h1x : e ⟨x, hxC⟩ ≠ 1 := by
    intro h
    exact hx1' (e.injective (h.trans (map_one e).symm))
  have h1y : e ⟨y, hyC⟩ ≠ 1 := by
    intro h
    exact hy1' (e.injective (h.trans (map_one e).symm))
  have hxy2 : e ⟨x, hxC⟩ ≠ e ⟨y, hyC⟩ := by
    intro h
    exact hxy' (e.injective h)
  have h := tableIII_Z2Z4_eq_of_sq_eq_one h2x h2y h2w h1x h1y hxy2
  rcases h with h | h | h | h
  · left
    have hw1'' : (⟨w, hwC⟩ : ↥C) = 1 := e.injective (h.trans (map_one e).symm)
    simpa using congrArg Subtype.val hw1''
  · right; left
    have hwx'' : (⟨w, hwC⟩ : ↥C) = ⟨x, hxC⟩ := e.injective h
    simpa using congrArg Subtype.val hwx''
  · right; right; left
    have hwy'' : (⟨w, hwC⟩ : ↥C) = ⟨y, hyC⟩ := e.injective h
    simpa using congrArg Subtype.val hwy''
  · right; right; right
    have hwxy'' : (⟨w, hwC⟩ : ↥C) = ⟨x, hxC⟩ * ⟨y, hyC⟩ :=
      e.injective (h.trans (map_mul e ⟨x, hxC⟩ ⟨y, hyC⟩).symm)
    simpa using congrArg Subtype.val hwxy''

private lemma t3_zmod5_cube_eq_one {a : ZMod 5} (h : a ^ 3 = 1) : a = 1 := by
  revert a
  decide

private lemma t3_conj_zpow_iter {H : Type*} [Group H] (x r : H) (k : ℤ)
    (h : x * r * x⁻¹ = r ^ k) (n : ℕ) :
    x ^ n * r * (x ^ n)⁻¹ = r ^ (k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : x ^ (n + 1) * r * (x ^ (n + 1))⁻¹
        = x * (x ^ n * r * (x ^ n)⁻¹) * x⁻¹ := by
      rw [pow_succ]
      group
    rw [hstep, ih]
    have hconj : x * r ^ (k ^ n) * x⁻¹ = (x * r * x⁻¹) ^ (k ^ n) := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [hconj, h, ← zpow_mul r k (k ^ n), pow_succ']

theorem tableIII_mul_comm_of_card_eq_fifteen {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 15) {r : H} (hr : orderOf r = 5) (x : H) : x * r = r * x := by
  let P : Subgroup H := Subgroup.zpowers r
  have hPcard : Nat.card ↥P = 5 := by
    change Nat.card ↥(Subgroup.zpowers r) = 5
    rw [Nat.card_zpowers, hr]
  have hPindex : P.index = 3 := by
    have h := Subgroup.card_mul_index P
    rw [hH, hPcard] at h
    omega
  have hPnorm : P.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (H := P) (by rw [hPindex, hH]; norm_num)
  haveI : P.Normal := hPnorm
  have hrP : r ∈ P := Subgroup.mem_zpowers r
  have hmem : x * r * x⁻¹ ∈ P := hPnorm.conj_mem r hrP x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hx3P : x ^ 3 ∈ P := by
    have := Subgroup.pow_index_mem P x
    rwa [hPindex] at this
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hx3P
  have hleft : x ^ 3 * r * (x ^ 3)⁻¹ = r := by
    rw [← ha]
    have hcomm : r ^ a * r = r * r ^ a := by
      rw [← zpow_add_one, ← zpow_one_add]
      congr 1
      ring
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hiter := t3_conj_zpow_iter x r k hk.symm 3
  rw [hleft] at hiter
  have hmod : k ^ 3 ≡ 1 [ZMOD (5 : ℤ)] := by
    have h1 : k ^ 3 ≡ 1 [ZMOD (orderOf r : ℤ)] :=
      (zpow_eq_zpow_iff_modEq (x := r) (m := k ^ 3) (n := 1)).mp
        (by rw [zpow_one]; exact hiter.symm)
    simpa [hr] using h1
  have hk5 : (k : ZMod 5) ^ 3 = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (k ^ 3) 1 5).mpr hmod
    push_cast at h
    exact h
  have hk1 : (k : ZMod 5) = 1 := t3_zmod5_cube_eq_one hk5
  have hmod1 : k ≡ 1 [ZMOD (5 : ℤ)] := (ZMod.intCast_eq_intCast_iff k 1 5).mp hk1
  have hrk : r ^ k = r := by
    have h2 : k ≡ 1 [ZMOD (orderOf r : ℤ)] := by simpa [hr] using hmod1
    have := (zpow_eq_zpow_iff_modEq (x := r) (m := k) (n := 1)).mpr h2
    simpa [zpow_one] using this
  have hconj : x * r * x⁻¹ = r := by rw [← hk, hrk]
  calc x * r = (x * r * x⁻¹) * x := by group
    _ = r * x := by rw [hconj]

theorem tableIII_isElemAbelian_closure_three {G : Type} [Group G] {x y w : G}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hw : w ^ 2 = 1) (hxy : x * y = y * x)
    (hxw : x * w = w * x) (hyw : y * w = w * y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y)
    (hw1 : w ≠ 1) (hwx : w ≠ x) (hwy : w ≠ y) (hwxy : w ≠ x * y) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({x, y, w} : Set G)) ∧
      Nat.card ↥(Subgroup.closure ({x, y, w} : Set G)) = 2 ^ 3 := by
  let E : Subgroup G := Subgroup.closure ({x, y, w} : Set G)
  let D : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hDcard : Nat.card ↥D = 4 := by
    show Nat.card ↥(Subgroup.closure ({x, y} : Set G)) = 4
    exact card_closure_pair hx hy hxy hx1 hy1 hne
  have hcomm : ({x, y, w} : Set G).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with h | h | h <;> rcases hb with h' | h' | h'
    · rw [h, h']
    · rw [h, h']; exact hxy
    · rw [h, h']; exact hxw
    · rw [h, h']; exact hxy.symm
    · rw [h, h']
    · rw [h, h']; exact hyw
    · rw [h, h']; exact hxw.symm
    · rw [h, h']; exact hyw.symm
    · rw [h, h']
  have hD_le : D ≤ E := by
    apply Subgroup.closure_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hw_notD : w ∉ D := by
    intro hwD
    rcases eq_of_mem_closure_two hx hy hxy hwD with h | h | h | h
    · exact hw1 h
    · exact hwx h
    · exact hwy h
    · exact hwxy h
  have hD_lt : D < E := by
    refine lt_of_le_of_ne hD_le ?_
    intro hDE
    apply hw_notD
    rw [hDE]
    exact Subgroup.subset_closure (by simp)
  let f : Fin 8 → G := ![1, x, y, x * y, w, x * w, y * w, x * y * w]
  have hT8 : (Set.range f).ncard ≤ 8 := by
    have h := Set.ncard_image_le (f := f) (s := (Set.univ : Set (Fin 8)))
    simpa [Set.image_univ] using h
  have hET : (E : Set G) ⊆ Set.range f := by
    intro z hz
    rcases eq_of_mem_closure_three hx hy hw hxy hxw hyw hz with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩
    · exact ⟨2, by simp [f]⟩
    · exact ⟨3, by simp [f]⟩
    · exact ⟨4, by simp [f]⟩
    · exact ⟨5, by simp [f]⟩
    · exact ⟨6, by simp [f]⟩
    · exact ⟨7, by simp [f]⟩
  have hEfin : (E : Set G).Finite := (Set.finite_range f).subset hET
  haveI : Finite ↥E := hEfin.to_subtype
  have hEcard_le : Nat.card ↥E ≤ 8 := by
    change Nat.card ↥(E : Set G) ≤ 8
    rw [Nat.card_coe_set_eq]
    exact le_trans (Set.ncard_le_ncard hET (Set.finite_range f)) hT8
  have h4dvd : 4 ∣ Nat.card ↥E := by
    have h := Subgroup.card_dvd_of_le hD_le
    rwa [hDcard] at h
  have h4lt : 4 < Nat.card ↥E := by
    have h := Subgroup.card_lt_of_lt hD_lt
    rwa [hDcard] at h
  have hsq : ∀ z ∈ E, z ^ 2 = 1 := by
    intro z hz
    rcases eq_of_mem_closure_three hx hy hw hxy hxw hyw hz with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simpa using hx
    · simpa using hy
    · rw [Commute.mul_pow hxy 2, hx, hy]; simp
    · simpa using hw
    · rw [Commute.mul_pow hxw 2, hx, hw]; simp
    · rw [Commute.mul_pow hyw 2, hy, hw]; simp
    · rw [Commute.mul_pow (Commute.mul_left hxw hyw) 2, Commute.mul_pow hxy 2,
        hx, hy, hw]
      simp
  refine ⟨⟨Subgroup.isMulCommutative_closure hcomm, hsq⟩, ?_⟩
  change Nat.card ↥E = 2 ^ 3
  obtain ⟨m, hm⟩ := h4dvd
  rw [hm] at h4lt hEcard_le ⊢
  norm_num at h4lt hEcard_le ⊢
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
