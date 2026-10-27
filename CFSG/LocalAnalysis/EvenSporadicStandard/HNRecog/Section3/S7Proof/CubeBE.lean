module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeFig
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_cubeB_explicit {a z b t : G} (H : S7Hyps a z) (hb : b ∈ orb2A a a)
    (ht : t ∈ derivedOf (Gxy a b)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    (∀ w ∈ Subgroup.closure ({a, b, t} : Set G), w ≠ 1 → IsConj a w ∨ IsConj z w) ∧
    ({w : G | w ∈ Subgroup.closure ({a, b, t} : Set G) ∧ IsConj z w}.ncard = 1 ∨
      {w : G | w ∈ Subgroup.closure ({a, b, t} : Set G) ∧ IsConj z w}.ncard = 3) := by
  have ha2 : a ^ 2 = 1 := s7_sq_of_isConj_a H (IsConj.refl a)
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hb2 : b ^ 2 = 1 := s7_sq_of_isConj_a H hb.1
  have hbb : b * b = 1 := by simpa [pow_two] using hb2
  have ha1 : a ≠ 1 := s7_ne_one_of_isConj_a H (IsConj.refl a)
  have hb1 : b ≠ 1 := s7_ne_one_of_isConj_a H hb.1
  have hbconj : IsConj a b ∧ IsConj a (a * b) := by
    simpa only [orb2A, Set.mem_setOf_eq] using hb
  have hab : a * b = b * a := s7_comm_orb2A H (IsConj.refl a) hb
  have hne : a ≠ b := by
    intro h
    apply ha1
    have hbc : IsConj a (a * b) := hbconj.2
    have hab1 : a * b = 1 := by rw [← h]; exact haa
    rw [hab1] at hbc
    exact isConj_one_left.1 hbc
  have htG : t ∈ Gxy a b :=
    Subgroup.map_subtype_le (_root_.commutator ↥(Gxy a b)) (by simpa [derivedOf] using ht)
  have hat : a * t = t * a := mem_Gx.1 (mem_Gxy.1 htG).1
  have hbt : b * t = t * b := mem_Gx.1 (mem_Gxy.1 htG).2
  have haC : a ∈ Subgroup.closure ({a, b, t} : Set G) := Subgroup.subset_closure (by simp)
  have hbC : b ∈ Subgroup.closure ({a, b, t} : Set G) := Subgroup.subset_closure (by simp)
  have htC : t ∈ Subgroup.closure ({a, b, t} : Set G) := Subgroup.subset_closure (by simp)
  have hfig := s7_fig_cases H hb ht ht2 ht1
  constructor
  · intro w hw hw1
    have hcases := eq_of_mem_closure_three ha2 hb2 ht2 hab hat hbt hw
    rcases hfig with ⟨hatc, hzat, hzbt, hzabt⟩ | ⟨hztc, haat, habt, haabt⟩
    · rcases hcases with h | h | h | h | h | h | h | h
      · exact (hw1 h).elim
      · rw [h]; exact Or.inl (IsConj.refl a)
      · rw [h]; exact Or.inl hbconj.1
      · rw [h]; exact Or.inl hbconj.2
      · rw [h]; exact Or.inl hatc
      · rw [h]; exact Or.inr hzat
      · rw [h]; exact Or.inr hzbt
      · rw [h]; exact Or.inr hzabt
    · rcases hcases with h | h | h | h | h | h | h | h
      · exact (hw1 h).elim
      · rw [h]; exact Or.inl (IsConj.refl a)
      · rw [h]; exact Or.inl hbconj.1
      · rw [h]; exact Or.inl hbconj.2
      · rw [h]; exact Or.inr hztc
      · rw [h]; exact Or.inl haat
      · rw [h]; exact Or.inl habt
      · rw [h]; exact Or.inl haabt
  · rcases hfig with ⟨hatc, hzat, hzbt, hzabt⟩ | ⟨hztc, haat, habt, haabt⟩
    · right
      have hT : {w : G | w ∈ Subgroup.closure ({a, b, t} : Set G) ∧ IsConj z w} =
          ({a * t, b * t, a * b * t} : Set G) := by
        ext w
        constructor
        · intro hw
          rcases hw with ⟨hwE, hzw⟩
          have hcases := eq_of_mem_closure_three ha2 hb2 ht2 hab hat hbt hwE
          rcases hcases with h | h | h | h | h | h | h | h
          · exact (s7_ne_one_of_isConj_z H hzw h).elim
          · exact (s7_not_both H (IsConj.refl a) (h ▸ hzw)).elim
          · exact (s7_not_both H hbconj.1 (h ▸ hzw)).elim
          · exact (s7_not_both H hbconj.2 (h ▸ hzw)).elim
          · exact (s7_not_both H hatc (h ▸ hzw)).elim
          · rw [h]; simp
          · rw [h]; simp
          · rw [h]; simp
        · intro hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with h | h | h
          · rw [h]
            exact ⟨(Subgroup.closure ({a, b, t} : Set G)).mul_mem haC htC, hzat⟩
          · rw [h]
            exact ⟨(Subgroup.closure ({a, b, t} : Set G)).mul_mem hbC htC, hzbt⟩
          · rw [h]
            exact ⟨(Subgroup.closure ({a, b, t} : Set G)).mul_mem
              ((Subgroup.closure ({a, b, t} : Set G)).mul_mem haC hbC) htC, hzabt⟩
      rw [hT]
      have hu_not : a * t ∉ ({b * t, a * b * t} : Set G) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨?_, ?_⟩
        · intro h
          exact hne (mul_right_cancel h)
        · intro h
          have h1 : a = a * b := mul_right_cancel h
          have h2 : b = 1 := by
            have h3 : a * b = a * 1 := by rw [mul_one]; exact h1.symm
            exact mul_left_cancel h3
          exact hb1 h2
      have hv_not : b * t ∉ ({a * b * t} : Set G) := by
        simp only [Set.mem_singleton_iff]
        intro h
        have h1 : b = a * b := mul_right_cancel h
        have h2 : a = 1 := by
          calc a = a * (b * b) := by rw [hbb, mul_one]
            _ = (a * b) * b := (mul_assoc a b b).symm
            _ = b * b := congrArg (· * b) h1.symm
            _ = 1 := hbb
        exact ha1 h2
      rw [Set.ncard_insert_of_notMem hu_not, Set.ncard_insert_of_notMem hv_not,
        Set.ncard_singleton]
    · left
      have hT : {w : G | w ∈ Subgroup.closure ({a, b, t} : Set G) ∧ IsConj z w} =
          ({t} : Set G) := by
        ext w
        constructor
        · intro hw
          rcases hw with ⟨hwE, hzw⟩
          have hcases := eq_of_mem_closure_three ha2 hb2 ht2 hab hat hbt hwE
          rcases hcases with h | h | h | h | h | h | h | h
          · exact (s7_ne_one_of_isConj_z H hzw h).elim
          · exact (s7_not_both H (IsConj.refl a) (h ▸ hzw)).elim
          · exact (s7_not_both H hbconj.1 (h ▸ hzw)).elim
          · exact (s7_not_both H hbconj.2 (h ▸ hzw)).elim
          · rw [h]; simp
          · exact (s7_not_both H haat (h ▸ hzw)).elim
          · exact (s7_not_both H habt (h ▸ hzw)).elim
          · exact (s7_not_both H haabt (h ▸ hzw)).elim
        · intro hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact ⟨htC, hztc⟩
      rw [hT, Set.ncard_singleton]

end CFSG.EvenSporadicStandard.HNRecog.Section3
