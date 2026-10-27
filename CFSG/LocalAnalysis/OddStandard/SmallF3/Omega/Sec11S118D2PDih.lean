module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PCyc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118W

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11d2_setup [Finite G] {C D Y : Subgroup G} {z : G} (hD2 : IsPGroup 2 D)
    (hCD : C ≤ D) (hYD : Y ≤ D) (hY : IsCyclic Y) (hYi : Y.relIndex D = 2) (hC : IsD8 C)
    (hzC : z ∈ C) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzcC : ∀ x ∈ C, x * z = z * x) :
    ∃ c ∈ C, c ∈ Y ∧ orderOf c = 4 ∧ c * c = z ∧ ∃ t0 ∈ C, t0 ∉ Y ∧ t0 * c * t0⁻¹ = c⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC8 : Nat.card C = 8 := sec11_isD8_card hC
  have hrel : Y.relIndex C ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := Y) hCD (by rw [hYi]; norm_num)
    rwa [hYi] at h
  have hmul := Subgroup.relIndex_mul_card (H := Y) (K := C)
  have hKcard : 2 < Nat.card ↥(Y ⊓ C) := by
    rw [hC8] at hmul
    generalize Y.relIndex C = r at hmul hrel
    generalize Nat.card ↥(Y ⊓ C) = n at hmul ⊢
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hmul
    obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
    · omega
    · omega
  have hKcyc : IsCyclic ↥(Y ⊓ C) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_left : Y ⊓ C ≤ Y))
      (Subgroup.inclusion_injective _)
  have hK2 : IsPGroup 2 ↥(Y ⊓ C) := hD2.to_le (inf_le_right.trans hCD)
  obtain ⟨c, hcK, hc4⟩ := sec11d2_exists_orderOf_eq_four hKcyc hK2 hKcard
  have hcY : c ∈ Y := hcK.1
  have hcC : c ∈ C := hcK.2
  have hc4' : c ^ 4 = 1 := by rw [← hc4]; exact pow_orderOf_eq_one c
  have hcc1 : c * c ≠ 1 := by
    intro h
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h])
    rw [hc4] at h2
    exact absurd h2 (by decide)
  obtain ⟨e⟩ := hC
  let cC : ↥C := ⟨c, hcC⟩
  let zC : ↥C := ⟨z, hzC⟩
  have hcC4 : cC ^ 4 = 1 := Subtype.ext hc4'
  have hcCsq : cC * cC ≠ 1 := fun h => hcc1 (congrArg Subtype.val h)
  have hzCsq : zC * zC = 1 := Subtype.ext hz2
  have hzC1 : zC ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzCc : ∀ y : ↥C, zC * y = y * zC := fun y => Subtype.ext (hzcC y y.2).symm
  have hecC4 : (e cC) ^ 4 = 1 := by rw [← map_pow, hcC4, map_one]
  have hecCsq : e cC * e cC ≠ 1 := by
    intro h
    apply hcCsq
    apply e.injective
    rw [map_mul, h, map_one]
  have hsqz : e cC * e cC = e zC := by
    refine (by decide +kernel : ∀ x z : DihedralGroup 4, x ^ 4 = 1 → x * x ≠ 1 → z * z = 1 →
      z ≠ 1 → (∀ y : DihedralGroup 4, z * y = y * z) → x * x = z) (e cC) (e zC) hecC4 hecCsq
      ?_ ?_ ?_
    · rw [← map_mul, hzCsq, map_one]
    · intro h
      apply hzC1
      apply e.injective
      rw [h, map_one]
    · intro y
      have h := congrArg e (hzCc (e.symm y))
      simpa [map_mul] using h
  have hcz : c * c = z := by
    have h : cC * cC = zC := e.injective (by rw [map_mul]; exact hsqz)
    exact congrArg Subtype.val h
  obtain ⟨y, hy⟩ := (by decide +kernel : ∀ x : DihedralGroup 4, x ^ 4 = 1 → x * x ≠ 1 →
    ∃ y : DihedralGroup 4, y * x * y⁻¹ = x⁻¹) (e cC) hecC4 hecCsq
  have hconj : (e.symm y : G) * c * (e.symm y : G)⁻¹ = c⁻¹ := by
    have h : e.symm y * cC * (e.symm y)⁻¹ = cC⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply]
      exact hy
    exact congrArg Subtype.val h
  refine ⟨c, hcC, hcY, hc4, hcz, (e.symm y : G), (e.symm y).2, ?_, hconj⟩
  intro ht0Y
  have hcomm := sec11d2_mul_comm_of_isCyclic hY ht0Y hcY
  have h1 : (e.symm y : G) * c * (e.symm y : G)⁻¹ = c := by rw [hcomm]; group
  rw [h1] at hconj
  apply hcc1
  calc c * c = c * c⁻¹ := by rw [← hconj]
    _ = 1 := mul_inv_cancel c

theorem sec11d2_comm_mod_z [Finite G] {D Y : Subgroup G} {z c t0 a : G} (hD2 : IsPGroup 2 D)
    (hYD : Y ≤ D) (hY : IsCyclic Y) (hYi : Y.relIndex D = 2) (hcY : c ∈ Y)
    (hc4 : orderOf c = 4) (hcc : c * c = z) (ht0D : t0 ∈ D) (ht0Y : t0 ∉ Y)
    (ht0c : t0 * c * t0⁻¹ = c⁻¹) (haD : ∀ x ∈ D, a * x * a⁻¹ ∈ D) (haa : a * a = 1)
    (hac : a * c = c * a) (hat0 : a * t0 = t0 * a) (hzD : ∀ x ∈ D, x * z = z * x) :
    ∀ x ∈ D, a * x * a⁻¹ * x⁻¹ ∈ zpowers z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 Y := hD2.to_le hYD
  have hYcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x :=
    fun x hx y hy => sec11d2_mul_comm_of_isCyclic hY hx hy
  have hcc1 : c * c ≠ 1 := by
    intro h
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h])
    rw [hc4] at h2
    exact absurd h2 (by decide)
  have hcoset : ∀ x ∈ D, x ∉ Y → t0⁻¹ * x ∈ Y := fun x hx hxY =>
    sec11d2_mul_mem_of_nmem hYi (D.inv_mem ht0D) hx
      (fun h => ht0Y (by simpa using Y.inv_mem h)) hxY
  have hac' : a⁻¹ * c = c * a⁻¹ := (Commute.inv_left (show Commute a c from hac)).eq
  have haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
    intro y hy
    by_contra hnot
    have hyD : a * y * a⁻¹ ∈ D := haD y (hYD hy)
    have h1 := hcoset _ hyD hnot
    have hxc : (a * y * a⁻¹) * c = c * (a * y * a⁻¹) := by
      calc (a * y * a⁻¹) * c = a * y * (a⁻¹ * c) := by group
        _ = a * y * (c * a⁻¹) := by rw [hac']
        _ = a * (y * c) * a⁻¹ := by group
        _ = a * (c * y) * a⁻¹ := by rw [hYcomm y hy c hcY]
        _ = (a * c) * y * a⁻¹ := by group
        _ = (c * a) * y * a⁻¹ := by rw [hac]
        _ = c * (a * y * a⁻¹) := by group
    have hy1c : (t0⁻¹ * (a * y * a⁻¹)) * c = c * (t0⁻¹ * (a * y * a⁻¹)) :=
      hYcomm _ h1 c hcY
    apply hcc1
    have hfix : t0 * c * t0⁻¹ = c := by
      calc t0 * c * t0⁻¹
          = (t0 * (t0⁻¹ * (a * y * a⁻¹))) * c * (t0 * (t0⁻¹ * (a * y * a⁻¹)))⁻¹ := by
            calc t0 * c * t0⁻¹ = t0 * ((t0⁻¹ * (a * y * a⁻¹)) * c * (t0⁻¹ * (a * y * a⁻¹))⁻¹) *
                  t0⁻¹ := by rw [hy1c]; group
              _ = _ := by group
        _ = (a * y * a⁻¹) * c * (a * y * a⁻¹)⁻¹ := by group
        _ = c := by rw [hxc]; group
    rw [hfix] at ht0c
    calc c * c = c * c⁻¹ := congrArg (fun w => c * w) ht0c
      _ = 1 := mul_inv_cancel c
  have hzmem : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ ∈ zpowers z := by
    intro y hy
    rcases sec11d2_cyc_conj hY hY2 haa haY hcY hc4 hac hy with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h, hcc]
      exact Subgroup.mem_zpowers z
  have hz0 : ∀ n ∈ zpowers z, t0 * n * t0⁻¹ ∈ zpowers z := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    have hc : t0 * z * t0⁻¹ = z := by
      rw [hzD t0 ht0D]
      group
    rw [hc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  intro x hx
  by_cases hxY : x ∈ Y
  · exact hzmem x hxY
  · have h1 := hcoset x hx hxY
    have hxeq : x = t0 * (t0⁻¹ * x) := by group
    have hcalc : a * x * a⁻¹ * x⁻¹ = t0 * (a * (t0⁻¹ * x) * a⁻¹ * (t0⁻¹ * x)⁻¹) * t0⁻¹ := by
      have e1 : a * x * a⁻¹ * x⁻¹ =
          a * (t0 * (t0⁻¹ * x)) * a⁻¹ * (t0 * (t0⁻¹ * x))⁻¹ := by rw [← hxeq]
      rw [e1]
      calc a * (t0 * (t0⁻¹ * x)) * a⁻¹ * (t0 * (t0⁻¹ * x))⁻¹
          = (a * t0) * (t0⁻¹ * x) * a⁻¹ * (t0⁻¹ * x)⁻¹ * t0⁻¹ := by group
        _ = (t0 * a) * (t0⁻¹ * x) * a⁻¹ * (t0⁻¹ * x)⁻¹ * t0⁻¹ := by rw [hat0]
        _ = _ := by group
    rw [hcalc]
    exact hz0 _ (hzmem _ h1)

theorem sec11d2_exists_X [Finite G] {D Y : Subgroup G} {z c d : G} (hYD : Y ≤ D)
    (hY : IsCyclic Y) (hYi : Y.relIndex D = 2) (hz2 : z * z = 1) (hcY : c ∈ Y)
    (hc4 : orderOf c = 4) (hcc : c * c = z) (hdD : d ∈ D) (hd2 : d * d = z)
    (hzD : ∀ x ∈ D, x * z = z * x) (hdc : d ∉ zpowers c) :
    ∃ X : Subgroup G, X ≤ D ∧ d ∈ X ∧ z ∈ X ∧ IsElemAbelianMod z X ∧ 8 ≤ Nat.card X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcD : c ∈ D := hYD hcY
  have hdedY : d * c * d⁻¹ ∈ Y := sec11d2_conj_mem hYD hYi hdD hcY
  have hded4 : orderOf (d * c * d⁻¹) = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj d) c
    rw [MulAut.conj_apply] at h
    rw [h, hc4]
  have hcase : d * c * d⁻¹ = c ∨ d * c * d⁻¹ = c⁻¹ :=
    sec11d2_eq_or_eq_inv_of_orderOf_eq_four hY hcY hdedY hc4 hded4
  have hzz : c⁻¹ * c⁻¹ = z := by
    rw [← mul_inv_rev, hcc, inv_eq_of_mul_eq_one_left hz2]
  have hcomm1 : d * c * d⁻¹ * c⁻¹ ∈ zpowers z := by
    rcases hcase with h | h
    · rw [h, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h, hzz]
      exact Subgroup.mem_zpowers z
  have hcomm2 : c * d * c⁻¹ * d⁻¹ ∈ zpowers z := by
    have h := Subgroup.inv_mem _ hcomm1
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  let X : Subgroup G := Subgroup.closure ({d, c} : Set G)
  have hdX : d ∈ X := Subgroup.subset_closure (by simp)
  have hcX : c ∈ X := Subgroup.subset_closure (by simp)
  have hzX : z ∈ X := by
    have h : c * c ∈ X := X.mul_mem hcX hcX
    rwa [hcc] at h
  have hXD : X ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdD
    · exact hcD
  have hmod : IsElemAbelianMod z X := by
    refine sec11_isElemAbelianMod_closure ?_ ?_ ?_
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]
        exact hzD d hdD
      · rw [ha]
        exact hzD c hcD
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha, hd2]
        exact Subgroup.mem_zpowers z
      · rw [ha, hcc]
        exact Subgroup.mem_zpowers z
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb, show d * d * d⁻¹ * d⁻¹ = 1 by group]
        exact Subgroup.one_mem _
      · rw [ha, hb]
        exact hcomm1
      · rw [ha, hb]
        exact hcomm2
      · rw [ha, hb, show c * c * c⁻¹ * c⁻¹ = 1 by group]
        exact Subgroup.one_mem _
  refine ⟨X, hXD, hdX, hzX, hmod, ?_⟩
  have hzpc : Nat.card (zpowers c) = 4 := by rw [Nat.card_zpowers, hc4]
  have hle : zpowers c ≤ X := zpowers_le.mpr hcX
  have hdvd : 4 ∣ Nat.card X := by
    rw [← hzpc]
    exact Subgroup.card_dvd_of_le hle
  have hne : Nat.card X ≠ 4 := by
    intro h4
    have heq : zpowers c = X := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [h4, hzpc]
    exact hdc (heq ▸ hdX)
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · omega
      · omega
    · exact h
  omega

end CFSG.OddStandard.SmallF3.Omega
