module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem eq_of_mem_closure_two {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : x * y = y * x)
    {e : G} (he : e ∈ Subgroup.closure ({x, y} : Set G)) : e = 1 ∨ e = x ∨ e = y ∨ e = x * y := by
  have hxx : x * x = 1 := by simpa [pow_two] using hx
  have hyy : y * y = 1 := by simpa [pow_two] using hy
  have hx1 : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hxx, one_mul]
  have hy1 : ∀ z, y * (y * z) = z := fun z => by rw [← mul_assoc, hyy, one_mul]
  have hyxy : y * (x * y) = x := by rw [hxy, hy1]
  have hxyx : x * y * x = y := by rw [mul_assoc, ← hxy, hx1]
  have hxyy : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
  have hxyxy : x * y * (x * y) = 1 := by rw [mul_assoc, hyxy, hxx]
  induction he using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [hx1, hyxy, hxyx, hxyy, hxyxy, hxx, hyy, hxy.symm]
  | inv a _ ha =>
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hxx))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hyy)))
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hyy, hxy]

theorem eq_of_mem_closure_three {x y t : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (ht : t ^ 2 = 1)
    (hxy : x * y = y * x) (hxt : x * t = t * x) (hyt : y * t = t * y) {e : G}
    (he : e ∈ Subgroup.closure ({x, y, t} : Set G)) :
    e = 1 ∨ e = x ∨ e = y ∨ e = x * y ∨ e = t ∨ e = x * t ∨ e = y * t ∨ e = x * y * t := by
  have htt : t * t = 1 := by simpa [pow_two] using ht
  let H := Subgroup.closure ({x, y} : Set G)
  have hcomm : ∀ d ∈ H, d * t = t * d := by
    intro d hd
    induction hd using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact hxt
      · exact hyt
    | one => simp
    | mul a b _ _ ha hb =>
      calc (a * b) * t = a * (b * t) := mul_assoc a b t
        _ = a * (t * b) := by rw [hb]
        _ = (a * t) * b := (mul_assoc a t b).symm
        _ = (t * a) * b := by rw [ha]
        _ = t * (a * b) := mul_assoc t a b
    | inv a _ ha =>
      have h := congrArg (·⁻¹) ha
      simpa [mul_inv_rev, inv_eq_of_mul_eq_one_right htt] using h.symm
  have hmem : e ∈ H ∨ ∃ d ∈ H, e = d * t := by
    induction he using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl (Subgroup.subset_closure (by simp))
      · exact Or.inl (Subgroup.subset_closure (by simp))
      · exact Or.inr ⟨1, H.one_mem, by simp⟩
    | one => exact Or.inl H.one_mem
    | mul a b _ _ ha hb =>
      rcases ha with haH | ⟨d1, hd1, rfl⟩ <;> rcases hb with hbH | ⟨d2, hd2, rfl⟩
      · exact Or.inl (H.mul_mem haH hbH)
      · exact Or.inr ⟨a * d2, H.mul_mem haH hd2, (mul_assoc a d2 t).symm⟩
      · refine Or.inr ⟨d1 * b, H.mul_mem hd1 hbH, ?_⟩
        calc (d1 * t) * b = d1 * (t * b) := mul_assoc d1 t b
          _ = d1 * (b * t) := by rw [hcomm b hbH]
          _ = (d1 * b) * t := (mul_assoc d1 b t).symm
      · refine Or.inl ?_
        have hcancel : (d1 * t) * (d2 * t) = d1 * d2 := by
          calc (d1 * t) * (d2 * t) = (d1 * t) * (t * d2) := by rw [hcomm d2 hd2]
            _ = d1 * (t * (t * d2)) := mul_assoc d1 t (t * d2)
            _ = d1 * ((t * t) * d2) := by rw [← mul_assoc t t d2]
            _ = d1 * d2 := by rw [htt, one_mul]
        rw [hcancel]
        exact H.mul_mem hd1 hd2
    | inv a _ ha =>
      rcases ha with haH | ⟨d, hd, rfl⟩
      · exact Or.inl (H.inv_mem haH)
      · refine Or.inr ⟨d⁻¹, H.inv_mem hd, ?_⟩
        calc (d * t)⁻¹ = t⁻¹ * d⁻¹ := mul_inv_rev d t
          _ = t * d⁻¹ := by rw [inv_eq_of_mul_eq_one_right htt]
          _ = d⁻¹ * t := (hcomm d⁻¹ (H.inv_mem hd)).symm
  rcases hmem with heH | ⟨d, hd, rfl⟩
  · rcases eq_of_mem_closure_two hx hy hxy heH with rfl | rfl | rfl | rfl <;> simp
  · rcases eq_of_mem_closure_two hx hy hxy hd with rfl | rfl | rfl | rfl <;> simp

theorem card_closure_pair {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card ↥(Subgroup.closure ({x, y} : Set G)) = 4 := by
  have hxx : x * x = 1 := by simpa [pow_two] using hx
  have hyy : y * y = 1 := by simpa [pow_two] using hy
  have hxy_ne_one : x * y ≠ 1 := by
    intro h
    exact hne (mul_left_cancel (show x * y = x * x by rw [hxx]; exact h)).symm
  have hx_ne_xy : x ≠ x * y := by
    intro h
    exact hy1 (mul_left_cancel (show x * y = x * 1 by rw [mul_one]; exact h.symm))
  have hy_ne_xy : y ≠ x * y := by
    intro h
    exact hx1 (mul_right_cancel (show x * y = 1 * y by rw [one_mul]; exact h.symm))
  let H := Subgroup.closure ({x, y} : Set G)
  have hset : (H : Set G) = ({1, x, y, x * y} : Set G) := by
    ext z
    constructor
    · intro hz
      rcases eq_of_mem_closure_two hx hy hxy hz with rfl | rfl | rfl | rfl <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact H.one_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact H.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have h1 : 1 ∉ ({x, y, x * y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hy1.symm, hxy_ne_one.symm⟩
  have h2 : x ∉ ({y, x * y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hx_ne_xy⟩
  have h3 : y ∉ ({x * y} : Set G) := by
    simpa using hy_ne_xy
  change (H : Set G).ncard = 4
  rw [hset]
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

theorem exists_mem_not_mem_closure_pair {E : Subgroup G} (hE : IsElemTwo 3 E) {x y : G}
    (hxE : x ∈ E) (hyE : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    ∃ t ∈ E, t ∉ Subgroup.closure ({x, y} : Set G) := by
  by_contra h
  push Not at h
  haveI : IsMulCommutative E := hE.1.1
  have hx2 : x ^ 2 = 1 := hE.1.2 x hxE
  have hy2 : y ^ 2 = 1 := hE.1.2 y hyE
  have hxy : x * y = y * x := setLike_mul_comm hxE hyE
  have hle : E ≤ Subgroup.closure ({x, y} : Set G) := fun z hz => h z hz
  have hcle : Subgroup.closure ({x, y} : Set G) ≤ E := by
    apply (Subgroup.closure_le E).2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxE
    · exact hyE
  have hEq : E = Subgroup.closure ({x, y} : Set G) := le_antisymm hle hcle
  have hEcard : Nat.card E = 8 := by rw [hE.2]; norm_num
  have hcardcl : Nat.card (Subgroup.closure ({x, y} : Set G)) = 4 :=
    card_closure_pair hx2 hy2 hxy hx1 hy1 hne
  rw [hEq, hcardcl] at hEcard
  exact absurd hEcard (by norm_num)

theorem closure_three_eq_of_isElemTwo {E : Subgroup G} (hE : IsElemTwo 3 E) {x y t : G}
    (hxE : x ∈ E) (hyE : y ∈ E) (htE : t ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y)
    (ht : t ∉ Subgroup.closure ({x, y} : Set G)) :
    Subgroup.closure ({x, y, t} : Set G) = E := by
  haveI : IsMulCommutative E := hE.1.1
  have hx2 : x ^ 2 = 1 := hE.1.2 x hxE
  have hy2 : y ^ 2 = 1 := hE.1.2 y hyE
  have hxy : x * y = y * x := setLike_mul_comm hxE hyE
  have hEcard : Nat.card E = 8 := by rw [hE.2]; norm_num
  haveI hEfin : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hC_le : Subgroup.closure ({x, y, t} : Set G) ≤ E := by
    apply (Subgroup.closure_le E).2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hxE
    · exact hyE
    · exact htE
  have hD_le_C : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.closure ({x, y, t} : Set G) := by
    apply Subgroup.closure_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hcardD : Nat.card ↥(Subgroup.closure ({x, y} : Set G)) = 4 :=
    card_closure_pair hx2 hy2 hxy hx1 hy1 hne
  have hD_lt_C : Subgroup.closure ({x, y} : Set G) < Subgroup.closure ({x, y, t} : Set G) := by
    refine lt_of_le_of_ne hD_le_C ?_
    intro hDC
    have htC : t ∈ Subgroup.closure ({x, y, t} : Set G) := Subgroup.subset_closure (by simp)
    rw [← hDC] at htC
    exact ht htC
  haveI hCfin : Finite ↥(Subgroup.closure ({x, y, t} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hC_le) (Subgroup.inclusion_injective hC_le)
  have hcard_lt :
      Nat.card ↥(Subgroup.closure ({x, y} : Set G)) <
        Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) :=
    Subgroup.card_lt_of_lt hD_lt_C
  have hcardD_dvd :
      Nat.card ↥(Subgroup.closure ({x, y} : Set G)) ∣
        Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) :=
    Subgroup.card_dvd_of_le hD_le_C
  have hcardC_dvd : Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) ∣ Nat.card E :=
    Subgroup.card_dvd_of_le hC_le
  have h8dvd : Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) ∣ 8 := by
    rwa [hEcard] at hcardC_dvd
  have hcardC_le : Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) ≤ 8 :=
    Nat.le_of_dvd (by norm_num) h8dvd
  obtain ⟨k, hk⟩ := hcardD_dvd
  have hk4 : Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) = 4 * k := by
    rw [hcardD] at hk; exact hk
  have hcardC : Nat.card ↥(Subgroup.closure ({x, y, t} : Set G)) = 8 := by
    rw [hk4]
    rw [hcardD] at hcard_lt
    rw [hk4] at hcard_lt hcardC_le
    omega
  exact Subgroup.eq_of_le_of_card_ge hC_le (by rw [hEcard, hcardC])

end CFSG.EvenSporadicStandard.HNRecog.Section3
