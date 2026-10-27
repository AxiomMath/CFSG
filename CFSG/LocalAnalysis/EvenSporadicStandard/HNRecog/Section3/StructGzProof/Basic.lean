module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_aschbacherHyp_congr {C : Type} [Group C] {Q Q' : Subgroup C} [Q.Normal]
    [Q'.Normal] (hQ : Q = Q') (h : AschbacherHyp C Q) : AschbacherHyp C Q' := by
  subst hQ
  exact h

theorem structGz_aschbacherHyp_pCore {G : Type} [Group G] {a z : G} (hGz9 : Gz9Facts a z) :
    AschbacherHyp ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) := by
  obtain ⟨Q, hQn, hA⟩ := hGz9.aschbacher
  exact structGz_aschbacherHyp_congr
    (IsExtraspecialPlusByA5WrTwoWith.pCore_eq hA.toIsExtraspecialPlusByA5WrTwoWith).symm hA

theorem structGz_cIrreducible_of_aschbacherHyp {G : Type} [Group G] {z : G}
    (hA : AschbacherHyp ↥(Gx z) (CFSG.pCore 2 ↥(Gx z))) :
    CIrreducible ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
  hA.irreducible

end CFSG.EvenSporadicStandard.HNRecog.Section3
