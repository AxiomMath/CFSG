module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate113
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Goldschmidt75

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

theorem outer_solvable_of_bender
    {X : Type} [Group X] (h : CFSG.Open.fusionIsBenderGroup X) :
    Group.IsSolvable (Outer X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv _ e
  · have hc : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
      rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, Nat.mul_comm]
    let eC : CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) (GaloisField 2 (2 * f)) (2 ^ f)) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
      MulEquiv.refl _
    have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f :=
      ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible f hf, GaloisField 2 (2 * f),
        inferInstance, inferInstance, hc,
        ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm).trans eC⟩⟩
    exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      hmodel).2
  · have hmodel : CFSG.Blueprint.SuzukiModel X 2 (2 * a + 1) :=
      ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
        GaloisField.card 2 (2 * a + 1) (by omega),
        ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSzCanonicalEquivNative a).symm).trans
          (MulEquiv.subgroupCongr
            (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1)))).symm⟩⟩
    exact (CFSG.LocalAnalysis.ComponentInitial.Suzuki_model_Schreier X 2 (2 * a + 1) hmodel).2

theorem exists_conj_of_bender
    {Λ X : Type} [Group Λ] [Group.IsPerfect Λ] [Group X]
    (h : CFSG.Open.fusionIsBenderGroup X) (Φ : Λ →* MulAut X) (l : Λ) :
    ∃ x : X, Φ l = MulAut.conj x := by
  have := outer_solvable_of_bender h
  exact perfect_action_inner Φ l

end CFSG.Goldschmidt75
