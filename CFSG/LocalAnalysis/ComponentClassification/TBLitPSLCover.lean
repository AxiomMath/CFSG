module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsic
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerParameters
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGADefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def specialLinearTwoRingEquiv {K K' : Type*} [CommRing K] [CommRing K'] (e : K ≃+* K') :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K' where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' := map_mul _

theorem card_psl_two_multiplier_table {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ m : ℕ, Odd m ∧
      Nat.card (Multiplier.generic .PSL 2 p f × Multiplier.exceptional .PSL 2 p f) = 2 * m := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have hgen : Multiplier.genericOrders .PSL 2 p f = (2, 1) := by
    change (Nat.gcd 2 (p ^ f - 1), 1) = (2, 1)
    rw [hgcd]
  have hexc : Multiplier.exceptionalOrders .PSL 2 p f = (1, 1) ∨
      Multiplier.exceptionalOrders .PSL 2 p f = (3, 1) := by
    by_cases h : p = 3 ∧ f = 2
    · obtain ⟨rfl, rfl⟩ := h
      exact .inr rfl
    · left
      unfold Multiplier.exceptionalOrders
      split <;> simp_all
  unfold Multiplier.generic Multiplier.exceptional
  rw [hgen]
  rcases hexc with h | h <;> rw [h]
  · exact ⟨1, odd_one, by simp⟩
  · exact ⟨3, by decide, by simp⟩

theorem sylow_two_card_griessHopfMultiplier_psl_two (hGA : GriessMultipliersOdd)
    {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Models.LieModel X .PSL 2 p f) :
    ∀ S : Sylow 2 (Open.griessHopfMultiplier X), Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := (hGA X .PSL 2 p f hm hp2 (Or.inl rfl)).2
  obtain ⟨m, hm, hcard⟩ := card_psl_two_multiplier_table hp hp2 (f := f)
  have hcardM : Nat.card (Open.griessHopfMultiplier X) = 2 * m := by
    rw [Nat.card_congr e.toEquiv, hcard]
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hm) (by decide)
  have : Finite (Open.griessHopfMultiplier X) :=
    Nat.finite_of_card_ne_zero (by rw [hcardM]; exact Nat.mul_ne_zero two_ne_zero hm0)
  intro S
  rw [Sylow.card_eq_multiplicity, hcardM, Nat.factorization_mul two_ne_zero hm0,
    Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h)), pow_one]

theorem models_lieModel_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (hm : LieModel X .PSL 2 p f) : Models.LieModel X .PSL 2 p f := by
  rcases hm with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨hc.1, .inl hc⟩
  all_goals exact absurd h0 (by norm_num)

theorem psl_two_double_cover (hGA : GriessMultipliersAllModels)
    (hGC : GriessMultipliersCentralCovers) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q)) (hZ1 : center Q ≠ ⊥) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : LieModel (Q ⧸ center Q) .PSL 2 p f) :
    0 < f ∧ ∃ _ : Fact p.Prime, Nonempty (Q ≃* SL(2, GaloisField p f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact : Fact p.Prime := ⟨hp⟩
  have hm' := models_lieModel_of_lieModel_psl_two hm
  obtain ⟨hf, h5⟩ := lieModel_psl_two_params hm hp2
  obtain ⟨-, -, K, hK, hKf, hcardK, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ := hm
  rotate_left
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  refine ⟨hf, hfact, ?_⟩
  have hS2 := sylow_two_card_griessHopfMultiplier_psl_two (GriessMultipliersOdd.of_allModels hGA)
    hp hp2 hm'
  obtain ⟨hcov1, hcov2⟩ := hGC (Q ⧸ center Q) .PSL 2 p f hm'
  have hcardZ : Nat.card (center Q) = 2 := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 (center Q)) := inferInstance
    have hle := hcov1 (fun S => (hS2 S).le) Q hQ ⟨MulEquiv.refl _⟩ S
    have hSZ : Nat.card S = Nat.card (center Q) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hZ)
      rw [Sylow.card_eq_multiplicity, hk, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same]
    have h1 : 1 < Nat.card (center Q) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hZ1
    rw [hSZ] at hle
    omega
  have hKodd : Odd (Nat.card K) := by
    rw [hcardK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hSLq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CatalogueBHigherLinearInner.sl_quasisimple 2 K le_rfl (.inr (by rw [hcardK]; exact h5))
  have hcardSL := ABGLocalTools.card_center_sl2 (F := K) hKodd
  obtain ⟨eQ⟩ := hcov2 (fun S => hS2 S) Q (Matrix.SpecialLinearGroup (Fin 2) K) hQ hSLq hcardZ
    hcardSL ⟨MulEquiv.refl _⟩ ⟨(SectionRank.OddCover.pslEquiv K).trans eK.symm⟩
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite (GaloisField p f)
  have hcardGF : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardK,
      GaloisField.card p f (by omega)]
  exact ⟨eQ.trans (specialLinearTwoRingEquiv (FiniteField.ringEquivOfCardEq hcardGF))⟩

end CFSG.ComponentClassification.TBLit
