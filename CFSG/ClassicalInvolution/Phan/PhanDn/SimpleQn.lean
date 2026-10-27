module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType
public import CFSG.ClassicalGroups.Orthogonal.IsometryConj
public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoClassical.ORigid
  (isSimpleGroup_statedOmega_quadPlus_of_three_le isSimpleGroup_statedOmega_quadMinus_of_two_le)

theorem isSimpleGroup_orthDerived_Qn {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K]
    [CharP K 2] {f : ℕ} (E : QuadExt F K (unitaryInvolution K 2 f)) {n : ℕ} (he : Even n)
    (hn : 4 ≤ n) : IsSimpleGroup (CFSG.RankThree.Classical2.orthDerived (Qn E n)) := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  obtain ⟨e⟩ := nonempty_isometryEquiv_quadPlus E he
  have : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)) :=
    isSimpleGroup_statedOmega_quadPlus_of_three_le (K := F) (k := n) (by omega)
  exact ((CFSG.ClassicalGroups.Orthogonal.commutatorOrthogonalGroupCongr e).trans
    (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
      (Q := quadPlus n F) (coe_quadPlus n F)).symm).isSimpleGroup

theorem isSimpleGroup_orthDerived_Qn_of_three_le {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] {f : ℕ} (E : QuadExt F K (unitaryInvolution K 2 f)) {n : ℕ}
    (hn : 3 ≤ n) : IsSimpleGroup (CFSG.RankThree.Classical2.orthDerived (Qn E n)) := by
  rcases Nat.even_or_odd n with he | ho
  · exact isSimpleGroup_orthDerived_Qn E he (by obtain ⟨j, rfl⟩ := he; omega)
  · let : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
    have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
    obtain ⟨b, c, hirr⟩ := CFSG.GroupTheory.WeirSylow.exists_irreducible_quadratic F
    obtain ⟨e⟩ := nonempty_isometryEquiv_quadMinus E ho hirr
    have : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus n F b c)) :=
      isSimpleGroup_statedOmega_quadMinus_of_two_le (m := n) (by omega) hirr
    exact ((CFSG.ClassicalGroups.Orthogonal.commutatorOrthogonalGroupCongr e).trans
      (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
        (Q := quadMinus n F b c) (coe_quadMinus n F b c)).symm).isSimpleGroup

end CFSG.ClassicalInvolution.PhanDn

end
