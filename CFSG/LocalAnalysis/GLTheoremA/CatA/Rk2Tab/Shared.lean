module

public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.LieType.SeitzGeneration

theorem lieModel_of_markedModel_E6 {X : Type} [Group X] {lab : GLALabel}
    (htag : lab.tag = .E6) (h : MarkedModel lab X) :
    LieModel X .E6 0 2 lab.n := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simpa [MarkedModel, markTag, markRank, markChar, markDeg] using h

theorem lieModel_of_markedModel_E7 {X : Type} [Group X] {lab : GLALabel}
    (htag : lab.tag = .E7) (h : MarkedModel lab X) :
    LieModel X .E7 0 2 lab.n := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simpa [MarkedModel, markTag, markRank, markChar, markDeg] using h

theorem lieModel_of_markedModel_E8 {X : Type} [Group X] {lab : GLALabel}
    (htag : lab.tag = .E8) (h : MarkedModel lab X) :
    LieModel X .E8 0 2 lab.n := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simpa [MarkedModel, markTag, markRank, markChar, markDeg] using h

theorem lieModel_of_markedModel_F4 {X : Type} [Group X] {lab : GLALabel}
    (htag : lab.tag = .F4) (h : MarkedModel lab X) :
    LieModel X .F4 0 2 lab.n := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  simpa [MarkedModel, markTag, markRank, markChar, markDeg] using h


theorem rk2Ord_three_one_eq_two : rk2Ord 3 1 = 2 :=
  (rk2Ord_one_eq_two_iff (by norm_num) (by norm_num)).mpr rfl

theorem rk2Ord_five_one_eq_four : rk2Ord 5 1 = 4 := by
  have hpos : 0 < rk2Ord 5 1 := rk2Ord_pos (by norm_num) (by norm_num) 1
  have hdvd : rk2Ord 5 1 ∣ 4 := by
    rw [rk2Ord_dvd_iff]; norm_num
  have hnot2 : ¬ rk2Ord 5 1 ∣ 2 := by
    rw [rk2Ord_dvd_iff]; norm_num
  have hle : rk2Ord 5 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases rk2Ord 5 1 <;> simp_all

theorem rk2Ord_seven_one_eq_three : rk2Ord 7 1 = 3 :=
  (rk2Ord_one_eq_three_iff (by norm_num)).mpr rfl

theorem pRank_le_of_sylowTorusDatum {G : Type} [Group G] [Finite G] {p m : ℕ}
    (h : SylowTorus G p m) (hp : p.Prime) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ m :=
  CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => h.rank_le hp hE

end CFSG.LocalAnalysis.GLTheoremA
