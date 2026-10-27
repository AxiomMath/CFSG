module

public import CFSG.ClassicalInvolution.Q3.TL4ConnBendTot
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.GH74.Bender.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import Certificates.Certificate113
import CFSG.CGT.Timmesfeld75.BenderInputs3
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.SimpleCase
import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Bend

open Subgroup CFSG.BenderSuzuki CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem isCyclic_outer_psl2_even {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : IsCyclic (Outer (GorensteinWalter.PSL2 K)) := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hdvd : Nat.card (quotientFieldProjection K).ker ∣ 1 := by
    rw [quotientFieldProjection_ker, ← Subgroup.index_ker]
    have hle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ≤
        (diagonalHom K).ker := by
      rintro _ ⟨y, rfl⟩
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' (GorensteinWalter.pGammaL2PSLRange K)
        (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (GorensteinWalter.mem_pGammaL2PSLRange_iff K _).mpr ⟨y, rfl⟩
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_eq_card]
    refine (LocalAnalysis.ComponentInitial.card_pgl_quotient_psl_dvd K).trans ?_
    have hodd : Odd (Nat.card K - 1) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso
        have : 1 < Nat.card K := Finite.one_lt_card
        rw [hK, pow_zero] at this
        omega
      · rw [hK]
        have h2 : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 odd_one
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)]
  have hker : (quotientFieldProjection K).ker = ⊥ :=
    (Subgroup.card_eq_one).mp (Nat.eq_one_of_dvd_one hdvd)
  have : IsCyclic (SemilinearQuotient K) :=
    isCyclic_of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp hker)
  let e : SemilinearQuotient K ≃* Outer (GorensteinWalter.PSL2 K) :=
    (semilinearQuotientEquivCoordinateEG K).trans
      ((coordinateOuterQuotientEquiv K).trans (coordinateOuterEquivPSL K))
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem statedClassicalModel_psu3 {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* PSU3Model n) : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 2 n :=
  CFSG.CGT.Timmesfeld75.statedClassicalModel_psu3_of_mulEquiv hn e

theorem finite_outer' {X : Type*} [Group X] [Finite X] : Finite (Outer X) := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) DFunLike.coe_injective
  infer_instance

theorem twoTot_outer {F : Type} [Group F] [Finite F] (hB : IsBenderGroup F) : TwoTot (Outer F) := by
  have := finite_outer' (X := F)
  rcases hB with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have := isCyclic_outer_psl2_even hK
    have := finite_outer' (X := PSL2Model n)
    exact TwoTot.of_mulEquiv (equivalence e).symm TwoTot.of_isCyclic
  · obtain ⟨-, a', ha', K, _, _, hfa, hK, ⟨e'⟩⟩ := CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a)))
    have hK' : Nat.card K = 2 ^ (2 * a' + 1) := hfa ▸ hK
    have hodd := (RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a' ha' K
      hK').2.2.2.2.2.2
    exact TwoTot.of_odd (by rw [Nat.card_congr (equivalence e').toEquiv]; exact hodd)
  · have h := statedClassicalModel_psu3 hn e
    refine TwoTot.of_outPNice (RankThree.PartOne.OutStructure.outPNice_PSU Nat.prime_two h ?_)
    intro h2
    have := h2.trans (Nat.gcd_dvd_left 3 _)
    norm_num at this

end CFSG.ClassicalInvolution.Q3.TL4.Bend
