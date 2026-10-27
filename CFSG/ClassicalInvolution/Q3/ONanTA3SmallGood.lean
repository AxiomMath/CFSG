module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCore
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution Check

section Order

variable {M : Type*} [Group M] [DecidableEq M]

omit [Group M] in
theorem memB_iff {l : List M} {x : M} : memB l x = true ↔ x ∈ l := by
  simp [memB]

theorem ordAux_spec (o : M) : ∀ (fuel k m : ℕ), ordAux o fuel k = m → m ≠ 0 →
    o ^ m = 1 ∧ k ≤ m ∧ ∀ j, k ≤ j → j < m → o ^ j ≠ 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro k m h hm
    exact absurd h.symm hm
  | succ fuel ih =>
    intro k m h hm
    by_cases hk : o ^ k = 1
    · have hmk : m = k := by
        simp only [ordAux, hk, ite_true] at h
        exact h.symm
      subst hmk
      exact ⟨hk, le_rfl, fun j hj hjm => absurd hjm (not_lt.mpr hj)⟩
    · simp only [ordAux, hk, ite_false] at h
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) m h hm
      refine ⟨h1, by omega, fun j hj hjm => ?_⟩
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact hk
      · exact h3 j hlt hjm

theorem orderOf_eq_of_ordB {B : ℕ} {o : M} (h : ordB B o ≠ 0) : orderOf o = ordB B o := by
  obtain ⟨h1, h2, h3⟩ := ordAux_spec o B 1 (ordB B o) rfl h
  rw [orderOf_eq_iff (Nat.pos_of_ne_zero h)]
  exact ⟨h1, fun m hm hm0 => h3 m hm0 hm⟩

end Order

section Sound

variable {Y M : Type} [Group Y] [Group M] [DecidableEq M] {ι : Y →* M}
  (hι : Function.Injective ι) {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m)

include hι hL in
theorem mem_centB {t : Y} {m : M} : m ∈ centB L (ι t) ↔ ∃ y, y * t = t * y ∧ ι y = m := by
  classical
  simp only [centB, List.mem_filter, decide_eq_true_eq, hL]
  constructor
  · rintro ⟨⟨y, rfl⟩, h⟩
    exact ⟨y, hι (by rw [map_mul, map_mul]; exact h), rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, h]⟩

include hι hL in
theorem noOddNormalAt_of_noOddB {B : ℕ} {t : Y} (h : noOddB B (centB L (ι t)) = true) :
    NoOddNormalAt t := by
  intro o ho hne hodd
  have hot : o * t = t * o := Subgroup.mem_centralizer_singleton_iff.mp ho
  have hmem : ι o ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨o, hot, rfl⟩
  simp only [noOddB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  obtain ⟨hne0, h1⟩ := h (ι o) hmem
  have hord : orderOf o = ordB B (ι o) := by
    rw [← orderOf_injective ι hι o]
    exact orderOf_eq_of_ordB hne0
  rcases h1 with (h1 | h1) | ⟨c, hc, hc0, hc2⟩
  · exact absurd (hι (by rw [h1, map_one])) hne
  · have := Nat.odd_iff.mp hodd
    rw [hord] at this
    omega
  · obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hc
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hy, ?_⟩
    have hp : ι (o * (y * o * y⁻¹)) = ι o * (ι y * ι o * (ι y)⁻¹) := by
      simp only [map_mul, map_inv]
    have hp' : orderOf (o * (y * o * y⁻¹)) = ordB B (ι o * (ι y * ι o * (ι y)⁻¹)) := by
      rw [← orderOf_injective ι hι, hp]
      exact orderOf_eq_of_ordB hc0
    rw [hp']
    exact Nat.even_iff.mpr hc2

omit [DecidableEq M] in
theorem q8B_eq (t a b : Y) : q8B (ι t) (ι a) (ι b) = (q8List t a b).map ι := by
  simp [q8B, q8List, map_mul]

include hι hL in
theorem witness_of_pairsB {t : Y} (h : pairsB (ι t) (centB L (ι t)) = true) (a b : Y)
    (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) :
    ∃ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 ∧ ¬ (x * a = a * x ∧ x * b = b * x) ∧
      ∀ y ∈ Subgroup.centralizer ({t} : Set Y), y * a = a * y → y * b = b * y →
        x * y = y * x := by
  have hta : a * t = t * a := by rw [← haa]; exact (mul_assoc a a a).symm
  have htb : b * t = t * b := by rw [← hbb]; exact (mul_assoc b b b).symm
  have haC : ι a ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨a, hta, rfl⟩
  have hbC : ι b ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨b, htb, rfl⟩
  unfold pairsB at h
  rw [List.all_eq_true] at h
  have h1 := h (ι a) (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, haa])⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (ι b) (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hbb])⟩)
  rcases Bool.or_eq_true_iff.1 h2 with h3 | hD
  · rcases Bool.or_eq_true_iff.1 h3 with hA | hB
    · exfalso
      have hrel : ι b * ι a = ι t * ι a * ι b := by simp only [← map_mul, hba]
      rw [decide_eq_true hrel] at hA
      exact absurd hA (by decide)
    · exfalso
      have hall : (centB L (ι t)).all (fun c => memB (q8B (ι t) (ι a) (ι b)) (c * ι a * c⁻¹) &&
          memB (q8B (ι t) (ι a) (ι b)) (c * ι b * c⁻¹)) = true := by
        rw [List.all_eq_true]
        intro c hc
        obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hc
        obtain ⟨hya, hyb⟩ := hnorm y (Subgroup.mem_centralizer_singleton_iff.mpr hy)
        rw [q8B_eq (ι := ι), Bool.and_eq_true]
        exact ⟨memB_iff.2 (List.mem_map.2 ⟨_, hya, by simp only [map_mul, map_inv]⟩),
          memB_iff.2 (List.mem_map.2 ⟨_, hyb, by simp only [map_mul, map_inv]⟩)⟩
      rw [hall] at hB
      exact absurd hB (by decide)
  · obtain ⟨xm, hxm, hx⟩ := List.any_eq_true.1 hD
    obtain ⟨x, hxt, rfl⟩ := (mem_centB hι hL).1 hxm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      List.all_eq_true, Bool.or_eq_true] at hx
    obtain ⟨⟨hx3, hmv⟩, hy⟩ := hx
    refine ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hxt, hι (by simpa using hx3), ?_,
      fun y hyc hya hyb => ?_⟩
    · rintro ⟨h7, h8⟩
      exact hmv ⟨by simp only [← map_mul, h7], by simp only [← map_mul, h8]⟩
    · have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
      have hyC : ι y ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨y, hyt, rfl⟩
      rcases hy (ι y) hyC with hyn | hyn
      · exfalso
        exact hyn ⟨by simp only [← map_mul, hya], by simp only [← map_mul, hyb]⟩
      · exact hι (by simpa [map_mul] using hyn)

include hι hL in
theorem goodPred_of_goodCheck [Finite Y] {B : ℕ} (h : goodCheck B L = true) {t : Y}
    (ht : orderOf t = 2) : GoodPred t := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht
    omega
  have h1 := List.all_eq_true.1 h (ι t) ((hL _).2 ⟨t, rfl⟩)
  rcases Bool.or_eq_true_iff.1 h1 with hA | hB
  · exfalso
    have hP : ι t * ι t = 1 ∧ ι t ≠ 1 :=
      ⟨by rw [← map_mul, ht2, map_one], fun h2 => ht1 (hι (by rw [h2, map_one]))⟩
    rw [decide_eq_true hP] at hA
    exact absurd hA (by decide)
  · have hB' : noOddB B (centB L (ι t)) = true ∧ pairsB (ι t) (centB L (ι t)) = true :=
      Bool.and_eq_true_iff.1 hB
    exact ⟨noOddNormalAt_of_noOddB hι hL hB'.1, fun a b haa hbb hba hnorm =>
      witness_of_pairsB hι hL hB'.2 a b haa hbb hba hnorm⟩

include hι hL in
theorem good_of_goodCheck [Finite Y] {B : ℕ} (h : goodCheck B L = true) {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) : GoodThreeElement R t :=
  good_of_goodPred hd hq (goodPred_of_goodCheck hι hL h hd.order)

end Sound

end CFSG.ClassicalInvolution.Q3.TA3
