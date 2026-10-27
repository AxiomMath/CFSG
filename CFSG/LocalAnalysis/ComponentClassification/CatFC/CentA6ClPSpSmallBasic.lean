module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpBase
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelfNormal
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewE
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewFour
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd
public import CFSG.Open.StandardDefs
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Walter.JRFacts
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate1016Base
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate9201

public section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent conjAut_eq_of_eq_smul)
open scoped Matrix

section Card

variable {K : Type} [Field K] [Finite K]

theorem card_spCent_le_two_mul_range (A : gsp 2 K) :
    Nat.card (spCent 2 K A) ≤ 2 * Nat.card ↥(spCentFix A).range := by
  have h1 : Nat.card (spCent 2 K A) =
      Nat.card ↥(spCentFix A).range * Nat.card ↥(spCentFix A).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (spCentFix A).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (spCentFix A)).toEquiv]
  have h2 : Nat.card ↥(spCentFix A).ker ≤ 2 := card_ker_spCentFix_le (by norm_num) A
  calc Nat.card (spCent 2 K A) =
        Nat.card ↥(spCentFix A).range * Nat.card ↥(spCentFix A).ker := h1
    _ ≤ Nat.card ↥(spCentFix A).range * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card ↥(spCentFix A).range := mul_comm _ _

theorem card_spCent_le_two_mul (A : gsp 2 K) :
    Nat.card (spCent 2 K A) ≤ 2 * Nat.card (fixedSubgroup (conjAut 2 K A)) :=
  (card_spCent_le_two_mul_range A).trans
    (Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _))

end Card

section Solvable

variable {K : Type} [Field K] [Finite K]

theorem isSolvable_fixed_of_spCent (A : gsp 2 K) (hs : Group.IsSolvable (spCent 2 K A)) :
    Group.IsSolvable (fixedSubgroup (conjAut 2 K A)) := by
  set θ := conjSp 2 K A with hθ
  set α := conjAut 2 K A with hα
  have hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g) := conjAut_proj A
  set F := (CatFactsSp4.fixOf α).comap (proj 2 K) with hF
  have hle : CatFactsSp4.fixOf θ ≤ F := fun g hg => by
    change α (proj 2 K g) = proj 2 K g
    rw [hθα]
    exact congrArg (proj 2 K) hg
  haveI : Group.IsSolvable (spScalars 2 K) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (CatFactsSp4.mem_center_of_mem_spScalars b.2)
        (a : StatedSp 2 K))
  haveI : Group.IsSolvable ↥(CatFactsSp4.fixOf θ) := hs
  have hFs : Group.IsSolvable F := by
    refine solvable_of_ker_le_range (Subgroup.inclusion hle) (CatFactsSp4.twistHom θ hθα) ?_
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h' := congrArg Subtype.val hg
    change θ g * (g : StatedSp 2 K)⁻¹ = 1 at h'
    refine ⟨⟨g, mul_inv_eq_one.mp h'⟩, Subtype.ext rfl⟩
  exact solvable_of_surjective (f := (proj 2 K).subgroupComap (CatFactsSp4.fixOf α))
    ((proj 2 K).subgroupComap_surjective (CatFactsSp4.fixOf α) proj_surjective)

end Solvable

section Inner

variable {K : Type} [Field K] [Finite K]

local notation "𝐌" A => (((A : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem conjAut_statedSp_eq_conj (B : StatedSp 2 K) :
    conjAut 2 K ⟨(B : GL (Fin 2 ⊕ Fin 2) K), statedSp_le_gsp B.2⟩ =
      MulAut.conj (proj 2 K B) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective x
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, conjAut_proj]
  refine congrArg (proj 2 K) (Subtype.ext ?_)
  rw [coe_conjSp]
  simp

theorem exists_sq_of_conjAut_inner {A : gsp 2 K} {μ : K}
    (hμ : (𝐌 A)ᵀ * formJ 2 K * (𝐌 A) = μ • formJ 2 K)
    (hA : conjAut 2 K A ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))).range) : ∃ l : K, l ^ 2 = μ := by
  obtain ⟨g, hg⟩ := hA
  obtain ⟨B, rfl⟩ := proj_surjective g
  set Bg : gsp 2 K := ⟨(B : GL (Fin 2 ⊕ Fin 2) K), statedSp_le_gsp B.2⟩ with hBg
  have h1 : conjAut 2 K (Bg⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one, conjAut_statedSp_eq_conj, hg]
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by norm_num) _).1 h1
  have hA' : (A : GL (Fin 2 ⊕ Fin 2) K) =
      (B : GL (Fin 2 ⊕ Fin 2) K) * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    have : (Bg : GL (Fin 2 ⊕ Fin 2) K) * ((Bg⁻¹ * A : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        (A : GL (Fin 2 ⊕ Fin 2) K) := by
      rw [Subgroup.coe_mul, ← mul_assoc, Subgroup.coe_inv, mul_inv_cancel, one_mul]
    rw [← this, hc]
  set Bm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hBm
  have hM : (𝐌 A) = Bm * ((c : K) • 1) := by
    rw [hA', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hB : Bmᵀ * formJ 2 K * Bm = formJ 2 K := SymplecticTorusWeyl.mem_statedSp_iff.mp B.2
  have key : (𝐌 A)ᵀ * formJ 2 K * (𝐌 A) = ((c : K) ^ 2) • formJ 2 K := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one]
    calc ((c : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * Bmᵀ * formJ 2 K *
          (Bm * ((c : K) • 1)) = (c : K) • ((c : K) • (Bmᵀ * formJ 2 K * Bm)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
            Matrix.mul_assoc]
      _ = ((c : K) ^ 2) • formJ 2 K := by rw [hB, smul_smul, sq]
  exact ⟨c, smul_formJ_injective 2 (key.symm.trans hμ)⟩

theorem conjAut_inner_of_sq {A : gsp 2 K} {μ l : K}
    (hμ : (𝐌 A)ᵀ * formJ 2 K * (𝐌 A) = μ • formJ 2 K) (hl : l ^ 2 = μ) (hl0 : l ≠ 0) :
    conjAut 2 K A ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))).range := by
  set M := (𝐌 A) with hMdef
  have hli : l⁻¹ ≠ 0 := inv_ne_zero hl0
  let B : GL (Fin 2 ⊕ Fin 2) K :=
    (A : GL (Fin 2 ⊕ Fin 2) K) *
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l⁻¹ hli)
  have hBm : (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = l⁻¹ • M := by
    simp only [B, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Units.val_mk0]
    rw [Matrix.mul_smul, Matrix.mul_one]
  have hB : B ∈ StatedSp 2 K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, hBm]
    have h1 : (l⁻¹ • M)ᵀ * formJ 2 K * (l⁻¹ • M) = (l⁻¹ * l⁻¹) • (Mᵀ * formJ 2 K * M) := by
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [h1, hμ, smul_smul, ← hl]
    have : l⁻¹ * l⁻¹ * l ^ 2 = 1 := by field_simp
    rw [this, one_smul]
  refine ⟨proj 2 K ⟨B, hB⟩, ?_⟩
  rw [← conjAut_statedSp_eq_conj ⟨B, hB⟩]
  refine (conjAut_eq_of_eq_smul (by norm_num) hl0 ?_).symm
  change M = l • (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  rw [hBm, smul_smul, mul_inv_cancel₀ hl0, one_smul]

end Inner

end CFSG.ComponentClassification.CatFC.PSpSmall
