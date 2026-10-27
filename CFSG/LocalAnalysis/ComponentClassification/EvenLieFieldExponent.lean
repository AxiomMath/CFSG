module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Blueprint (LieModel)

@[expose] def IsChar2LieShape (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ n = 2) ∨ (t = .PSU ∧ n = 3) ∨ (t = .twistedB2 ∧ n = 0) ∨
    (t = .PSp ∧ n = 2) ∨ (t = .G2 ∧ n = 0) ∨ (t = .PSU ∧ n = 4) ∨ (t = .PSU ∧ n = 5)


theorem lieModel_eq_of_isChar2LieShape {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel X t n 2 f) (hshape : IsChar2LieShape t n)
    {t' : StatedLieTag} {n' f' : ℕ} (h' : LieModel X t' n' 2 f') :
    t' = t ∧ n' = n ∧ f' = f := by
  rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact CFSG.SeitzReduction.RankOne.sl2EvenTypeDet X f t' n' f' h
      (CFSG.Blueprint.LieModel.admissible h') h'
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet X f t' n' f' h
      (CFSG.Blueprint.LieModel.admissible h') h'
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.szEvenTypeDet X f t' n' f' h
      (CFSG.Blueprint.LieModel.admissible h') h'
  · exact CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet 2 X f t' n' f' h
      (CFSG.Blueprint.LieModel.admissible h') h'
  · obtain ⟨ht, hf⟩ := CFSG.EvenSporadicStandard.Induction.lieModel_G2_two_unique h h'
    refine ⟨ht, ?_, hf⟩
    have hadm := CFSG.Blueprint.LieModel.admissible h'
    rw [ht] at hadm
    exact hadm.2.2.1
  · exact (CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 4) (by norm_num))
      X f t' n' f' h (CFSG.Blueprint.LieModel.admissible h') h'
  · exact (CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 5) (by norm_num))
      X f t' n' f' h (CFSG.Blueprint.LieModel.admissible h') h'

theorem fieldExponent_eq_of_isChar2LieShape {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel X t n 2 f) (hshape : IsChar2LieShape t n)
    {t' : StatedLieTag} {n' f' : ℕ} (h' : LieModel X t' n' 2 f') : f' = f :=
  (lieModel_eq_of_isChar2LieShape h hshape h').2.2

end CFSG.ComponentClassification.CatLeafProof
