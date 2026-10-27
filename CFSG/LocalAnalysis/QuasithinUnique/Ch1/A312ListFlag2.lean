module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBlock

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Small

theorem hom_eq_one_of_perfect_of_solvable {N S : Type*} [Group N] [Group S]
    (hN : Group.IsPerfect N) [Group.IsSolvable S] (f : N →* S) (x : N) : f x = 1 := by
  have hperf : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hsolv : Group.IsSolvable ↥f.range := inferInstance
  have hsub : Subsingleton ↥f.range := by
    by_contra h
    have : Nontrivial ↥f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable ↥f.range hsolv
  have hx : (⟨f x, ⟨x, rfl⟩⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val hx

variable {K : Type*} [Field K]

theorem isSolvable_specialLinear_small [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : m ≤ 2) :
    Group.IsSolvable (SpecialLinearGroup (Fin m) K) := by
  interval_cases m
  · have : Subsingleton (SpecialLinearGroup (Fin 0) K) :=
      ⟨fun A B => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  · have : Subsingleton (SpecialLinearGroup (Fin 1) K) :=
      ⟨fun A B => Subtype.ext (by
        have hA := A.2
        have hB := B.2
        rw [Matrix.det_unique] at hA hB
        ext i j
        rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
        exact hA.trans hB.symm)⟩
    infer_instance
  · refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num

variable {n : ℕ}

theorem blockLeft_of_cut {I : Set ℕ} {a : ℕ} (m : ℕ) (ha : a = 0 ∨ a ∈ I) :
    BlockLeft (flagStabilizer n K I) a m := by
  rcases ha with rfl | ha
  · exact blockLeft_zero _ m
  · exact blockLeft_of_stabilizer fun g hg => mem_flagStabilizer.mp hg a ha

theorem blockRight_of_cut {I : Set ℕ} {a m : ℕ} (hb : a + m = n ∨ a + m ∈ I) :
    BlockRight (flagStabilizer n K I) a m := by
  rcases hb with hb | hb
  · exact blockRight_top _ hb
  · exact blockRight_of_stabilizer fun g hg => mem_flagStabilizer.mp hg (a + m) hb

theorem blkAt_eq_one_of_small [Finite K] (hK : Nat.card K = 2) {I : Set ℕ} {a m : ℕ}
    (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) (hm : m ≤ 2)
    {N : Subgroup (SpecialLinearGroup (Fin n) K)} (hNH : N ≤ flagStabilizer n K I)
    (hN : Group.IsPerfect ↥N) (x : ↥N) : blkAt a m h (x.1 : Matrix (Fin n) (Fin n) K) = 1 := by
  have := isSolvable_specialLinear_small hK hm
  have h1 := hom_eq_one_of_perfect_of_solvable hN
    (blkSL (flagStabilizer n K I) a m h (blockLeft_of_cut m ha) (blockRight_of_cut hb) hNH hN) x
  have h2 := congrArg (fun A : SpecialLinearGroup (Fin m) K => (A : Matrix (Fin m) (Fin m) K)) h1
  simpa [blkSL_coe] using h2

end Small

end CFSG.QuasithinUnique.Vol2Native.A312L
