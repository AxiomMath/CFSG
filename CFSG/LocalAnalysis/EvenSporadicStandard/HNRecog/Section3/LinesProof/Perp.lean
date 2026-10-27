module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Cube
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Graph

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

private theorem lines_sq_eq_one (h : IsF5Type a z) {x : G} (hx : IsConj a x) : x ^ 2 = 1 := by
  have h2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx
  simpa [h2] using pow_orderOf_eq_one x

private theorem lines_ne_one_of_isConj_a (h : IsF5Type a z) {x : G} (hx : IsConj a x) :
    x ≠ 1 := by
  intro hx1
  have h2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx
  rw [hx1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem lines_not_isConj_one (h : IsF5Type a z) : ¬ IsConj a 1 := by
  intro hc
  have ha : a = 1 := isConj_one_left.mp hc
  have h2 : orderOf a = 2 := h.orderOf_a
  rw [ha, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem lines_ne_of_isConj_mul (h : IsF5Type a z) {u v : G} (hu : IsConj a u)
    (huv : IsConj a (u * v)) : u ≠ v := by
  intro hEq
  have h1 : u * v = 1 := by
    rw [← hEq]
    simpa [pow_two] using lines_sq_eq_one h hu
  exact lines_not_isConj_one h (h1 ▸ huv)

private theorem lines_mul_ne_left_of_ne_one {x y : G} (hy : y ≠ 1) : x * y ≠ x := by
  intro hEq
  exact hy (mul_left_cancel (hEq.trans (mul_one x).symm))

private theorem lines_mul_ne_right_of_ne_one {x y : G} (hx : x ≠ 1) : x * y ≠ y := by
  intro hEq
  exact hx (mul_right_cancel (hEq.trans (one_mul y).symm))

theorem lines_perp_xy (h : IsF5Type a z) (hCube : CubeFacts a z) {x y : G} (hx : IsConj a x)
    (hy : IsConj a y) (hxy : IsConj a (x * y)) :
    gammaPerp a {x, y, x * y} = {x, y, x * y} := by
  have hx2 : x ^ 2 = 1 := lines_sq_eq_one h hx
  have hy2 : y ^ 2 = 1 := lines_sq_eq_one h hy
  have hxy2 : (x * y) ^ 2 = 1 := lines_sq_eq_one h hxy
  have hx1 : x ≠ 1 := lines_ne_one_of_isConj_a h hx
  have hy1 : y ≠ 1 := lines_ne_one_of_isConj_a h hy
  have hne : x ≠ y := lines_ne_of_isConj_mul h hx hxy
  have hxy_ne_x : x * y ≠ x := lines_mul_ne_left_of_ne_one hy1
  have hxy_ne_y : x * y ≠ y := lines_mul_ne_right_of_ne_one hx1
  have hcomm : x * y = y * x := comm_of_sq_mul hx2 hy2 hxy2
  have hxx : x * x = 1 := by simpa [pow_two] using hx2
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  have hx_xy : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have hy_xy : y * (x * y) = x := by rw [hcomm, ← mul_assoc, hyy, one_mul]
  have hxy_x : (x * y) * x = y := by rw [hcomm, mul_assoc, hxx, mul_one]
  have hxy_y : (x * y) * y = x := by rw [mul_assoc, hyy, mul_one]
  have hyx : y * x = x * y := hcomm.symm
  have hx_mem : x ∈ gammaPerp a {x, y, x * y} := by
    refine ⟨hx, ?_⟩
    intro w hw
    have hw' : w = x ∨ w = y ∨ w = x * y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
    rcases hw' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨hne.symm, by rw [hyx]; exact hxy⟩
    · exact Or.inr ⟨hxy_ne_x, by rw [hxy_x]; exact hy⟩
  have hy_mem : y ∈ gammaPerp a {x, y, x * y} := by
    refine ⟨hy, ?_⟩
    intro w hw
    have hw' : w = x ∨ w = y ∨ w = x * y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
    rcases hw' with rfl | rfl | rfl
    · exact Or.inr ⟨hne, hxy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hxy_ne_y, by rw [hxy_y]; exact hx⟩
  have hxy_mem : x * y ∈ gammaPerp a {x, y, x * y} := by
    refine ⟨hxy, ?_⟩
    intro w hw
    have hw' : w = x ∨ w = y ∨ w = x * y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
    rcases hw' with rfl | rfl | rfl
    · exact Or.inr ⟨hxy_ne_x.symm, by rw [hx_xy]; exact hy⟩
    · exact Or.inr ⟨hxy_ne_y.symm, by rw [hy_xy]; exact hx⟩
    · exact Or.inl rfl
  apply Set.Subset.antisymm
  · intro w hw
    by_contra hwnot
    have hwne : w ≠ x ∧ w ≠ y ∧ w ≠ x * y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hwnot
    obtain ⟨hwx, hwy, hwxy⟩ := hwne
    have hxw : IsConj a (x * w) := by
      rcases hw.2 x (by simp) with h1 | h1
      · exact absurd h1 hwx
      · exact h1.2
    have hyw : IsConj a (y * w) := by
      rcases hw.2 y (by simp) with h1 | h1
      · exact absurd h1 hwy
      · exact h1.2
    have hxyw : IsConj a ((x * y) * w) := by
      rcases hw.2 (x * y) (by simp) with h1 | h1
      · exact absurd h1 hwxy
      · exact h1.2
    have hw2 : w ^ 2 = 1 := lines_sq_eq_one h hw.1
    have hw1 : w ≠ 1 := lines_ne_one_of_isConj_a h hw.1
    have hxw_comm : x * w = w * x := comm_of_sq_mul hx2 hw2 (lines_sq_eq_one h hxw)
    have hyw_comm : y * w = w * y := comm_of_sq_mul hy2 hw2 (lines_sq_eq_one h hyw)
    have hw_notin : w ∉ Subgroup.closure ({x, y} : Set G) := by
      intro hmem
      rcases eq_of_mem_closure_two hx2 hy2 hcomm hmem with h1 | h1 | h1 | h1
      · exact hw1 h1
      · exact hwx h1
      · exact hwy h1
      · exact hwxy h1
    apply hCube.no_cube
    refine ⟨Subgroup.closure ({x, y, w} : Set G), ?_, ?_⟩
    · exact lines_isElemTwo_closure_three hx2 hy2 hw2 hcomm hxw_comm hyw_comm hx1 hy1 hne
        hw_notin
    · intro t ht _ ht1
      rcases eq_of_mem_closure_three hx2 hy2 hw2 hcomm hxw_comm hyw_comm ht with
        h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
      · exact absurd h1 ht1
      · rw [h1]; exact hx
      · rw [h1]; exact hy
      · rw [h1]; exact hxy
      · rw [h1]; exact hw.1
      · rw [h1]; exact hxw
      · rw [h1]; exact hyw
      · rw [h1]; exact hxyw
  · intro v hv
    have hv' : v = x ∨ v = y ∨ v = x * y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv
    rcases hv' with h1 | h1 | h1
    · rw [h1]; exact hx_mem
    · rw [h1]; exact hy_mem
    · rw [h1]; exact hxy_mem

theorem lines_unique_third (h : IsF5Type a z) (hCube : CubeFacts a z)
    (hcom : ∀ x y t : G, IsConj a x → IsConj a y → IsConj a (x * y) → t ≠ x * y →
      t ∈ orb2A a x ∩ orb2A a y → (orb2A a x ∩ orb2A a y ∩ orb2A a t).Nonempty)
    {x y : G} (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y)) :
    {t | IsConj a t ∧ t ≠ x ∧ t ≠ y ∧ gammaPerp a {x, y, t} = {x, y, t}} = {x * y} := by
  have hx2 : x ^ 2 = 1 := lines_sq_eq_one h hx
  have hy2 : y ^ 2 = 1 := lines_sq_eq_one h hy
  have hx1 : x ≠ 1 := lines_ne_one_of_isConj_a h hx
  have hy1 : y ≠ 1 := lines_ne_one_of_isConj_a h hy
  have hxy_ne_x : x * y ≠ x := lines_mul_ne_left_of_ne_one hy1
  have hxy_ne_y : x * y ≠ y := lines_mul_ne_right_of_ne_one hx1
  have hxx : x * x = 1 := by simpa [pow_two] using hx2
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨htA, htne_x, htne_y, hperp⟩ := ht
    simp only [Set.mem_singleton_iff]
    by_contra htxy
    have ht_perp : t ∈ gammaPerp a {x, y, t} := by
      rw [hperp]
      simp
    have hxt : IsConj a (x * t) := by
      rcases ht_perp.2 x (by simp) with h1 | h1
      · exact absurd h1 htne_x
      · exact h1.2
    have hyt : IsConj a (y * t) := by
      rcases ht_perp.2 y (by simp) with h1 | h1
      · exact absurd h1 htne_y
      · exact h1.2
    have ht_mem : t ∈ orb2A a x ∩ orb2A a y := ⟨⟨htA, hxt⟩, ⟨htA, hyt⟩⟩
    obtain ⟨t₁, ht₁⟩ := hcom x y t hx hy hxy htxy ht_mem
    obtain ⟨⟨⟨ht1A, hxt1⟩, ⟨_, hyt1⟩⟩, ⟨_, htt1⟩⟩ := ht₁
    have ht1_perp : t₁ ∈ gammaPerp a {x, y, t} := by
      refine ⟨ht1A, ?_⟩
      intro v hv
      have hv' : v = x ∨ v = y ∨ v = t := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv
      rcases hv' with h1 | h1 | h1
      · rw [h1]
        by_cases hh : t₁ = x
        · exact Or.inl hh
        · exact Or.inr ⟨fun h' => hh h'.symm, hxt1⟩
      · rw [h1]
        by_cases hh : t₁ = y
        · exact Or.inl hh
        · exact Or.inr ⟨fun h' => hh h'.symm, hyt1⟩
      · rw [h1]
        by_cases hh : t₁ = t
        · exact Or.inl hh
        · exact Or.inr ⟨fun h' => hh h'.symm, htt1⟩
    have ht1_in : t₁ ∈ ({x, y, t} : Set G) := by
      rw [← hperp]
      exact ht1_perp
    have ht1' : t₁ = x ∨ t₁ = y ∨ t₁ = t := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht1_in
    rcases ht1' with h1 | h1 | h1
    · rw [h1] at hxt1
      rw [hxx] at hxt1
      exact lines_not_isConj_one h hxt1
    · rw [h1] at hyt1
      rw [hyy] at hyt1
      exact lines_not_isConj_one h hyt1
    · rw [h1] at htt1
      have htt : t * t = 1 := by simpa [pow_two] using lines_sq_eq_one h htA
      rw [htt] at htt1
      exact lines_not_isConj_one h htt1
  · intro t ht
    have ht' : t = x * y := by simpa only [Set.mem_singleton_iff] using ht
    show IsConj a t ∧ t ≠ x ∧ t ≠ y ∧ gammaPerp a {x, y, t} = {x, y, t}
    rw [ht']
    exact ⟨hxy, hxy_ne_x, hxy_ne_y, lines_perp_xy h hCube hx hy hxy⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
