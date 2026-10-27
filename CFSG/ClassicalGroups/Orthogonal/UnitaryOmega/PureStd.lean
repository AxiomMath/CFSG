module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureEmbed
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PurePairGeneration
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlocks
public import CFSG.ClassicalInvolution.Phan.PhanDn.Dictionary
public import CFSG.RankThree.PartOne.KFR4.DerivedLe
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.ThreePlaneFourierGeneration
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyGood
public import CFSG.LocalAnalysis.StandardType.PhanELiftOfFamily
public import CFSG.Mathlib.GroupTheory.SimpleFactorPair
public import CFSG.ClassicalInvolution.Phan.SuTwoSimple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import all CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureEmbed
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.CTP.ExtPhan
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.S12.Sec1322Fin
public import CFSG.RankThree.PartOne.S12.Sec136Inputs
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec138Loc
public import CFSG.RankThree.PartOne.S12.Sec1511Y3
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import Certificates.Certificate9530

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan
open CFSG.GroupTheory CFSG.ClassicalGroups.Unitary CFSG.GorensteinWalter

open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

def stdPerm : Equiv.Perm (Fin 4) := (finRotate 4).symm

private theorem stdPerm_zero : stdPerm 0 = 3 := by decide

private theorem stdPerm_one : stdPerm 1 = 0 := by decide

private theorem stdPerm_two : stdPerm 2 = 1 := by decide

private theorem stdPerm_three : stdPerm 3 = 2 := by decide

noncomputable def stdEmb : DΩ E 3 →* normOmega E 4 :=
  pureEmb E stdPerm.toEmbedding

theorem stdEmb_injective : Function.Injective (stdEmb E) :=
  pureEmb_injective E stdPerm.toEmbedding

theorem range_stdEmb : (stdEmb E).range = normPureBlock E 4 Finset.univ := by
  rw [stdEmb, range_pureEmb, Finset.map_univ_equiv]

private theorem succEmb_trans_stdPerm_eq (h : 3 ≤ 4) :
    (Fin.succEmb 3).trans stdPerm.toEmbedding =
      (Function.Embedding.refl (Fin 3)).trans (Fin.castLEEmb h) := by
  ext i
  fin_cases i <;> rfl

theorem stdEmb_comp_qnExtΩ_succ :
    (stdEmb E).comp (qnExtΩ E (Fin.succEmb 3)) =
      (normOmegaCast E (by norm_num : 3 ≤ 4)).comp
        (pureEmb E (Function.Embedding.refl (Fin 3))) := by
  rw [stdEmb, pureEmb_comp_qnExtΩ, normOmegaCast_comp_pureEmb,
    succEmb_trans_stdPerm_eq]

private def stdPairEmb (k : Fin 3) : Fin 2 ↪ Fin 4 :=
  (Fin.natAddEmb k.val).trans (Fin.castLEEmb (by omega : k.val + 2 ≤ 4))

private theorem stdPairEmb_zero (k : Fin 3) :
    stdPairEmb k 0 = ⟨k.val, by omega⟩ := rfl

private theorem stdPairEmb_one (k : Fin 3) :
    stdPairEmb k 1 = ⟨k.val + 1, by omega⟩ := rfl

private theorem suEndN_blockEmb2_eq_coordExt {k : Fin 3} (g : Su K 2 f 2) :
    suEndN (F := F) (unitaryInvolution K 2 f) 4 (blockEmb2 K 2 f 3 k g) =
      coordExt (stdPairEmb k) (suEndN (F := F) (unitaryInvolution K 2 f) 2 g) := by
  apply LinearEquiv.ext
  intro x
  funext j
  rw [suEndN_apply, coordExt_apply]
  by_cases h0 : j = ⟨k.val, by omega⟩
  · subst j
    rw [← stdPairEmb_zero k, (stdPairEmb k).injective.extend_apply, stdPairEmb_zero k]
    rw [blockEmb2_smul_apply_left, suEndN_apply, smul_def, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    simp [Function.comp_apply, stdPairEmb_zero, stdPairEmb_one]
  · by_cases h1 : j = ⟨k.val + 1, by omega⟩
    · subst j
      rw [← stdPairEmb_one k, (stdPairEmb k).injective.extend_apply, stdPairEmb_one k]
      rw [blockEmb2_smul_apply_right, suEndN_apply, smul_def, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two]
      simp [Function.comp_apply, stdPairEmb_zero, stdPairEmb_one]
    · rw [Function.extend_apply' _ _ _ (by
        rintro ⟨i, hi⟩
        fin_cases i
        · exact h0 (by simpa [stdPairEmb_zero] using hi.symm)
        · exact h1 (by simpa [stdPairEmb_one] using hi.symm))]
      rw [smul_def, coe_coe_blockEmb2]
      exact blockMat_mulVec_of_not_mem _ _ (by
        rintro ⟨hle, hlt⟩
        have hj : j.val = k.val ∨ j.val = k.val + 1 := by omega
        rcases hj with h | h
        · exact h0 (Fin.ext h)
        · exact h1 (Fin.ext (by simpa using h)))


private noncomputable def suTwo (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    Su K 2 f 2 →* orthDerived (Qn E 2) :=
  (suEndN (F := F) (unitaryInvolution K 2 f) 2).codRestrict (orthDerived (Qn E 2))
    (fun g => range_le_commutator_of_su2 E 1 hK hq
      (suEndN (F := F) (unitaryInvolution K 2 f) 2)
      (by rintro x ⟨y, rfl⟩; exact suEndN_mem_orthogonalGroup E 2 y)
      (MonoidHom.mem_range.mpr ⟨g, rfl⟩))

private theorem suTwo_coe (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (g : Su K 2 f 2) :
    ((suTwo E hK hq g : orthDerived (Qn E 2)) : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)) =
      suEndN (F := F) (unitaryInvolution K 2 f) 2 g := rfl

private noncomputable def chainNode (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (k : Fin 3) : Su K 2 f 2 →* DΩ E 3 :=
  (stdFamilyΩ E 3 le_rfl hK hq).ι (Fin.castSucc k)

private theorem chainNode_coe (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (k : Fin 3) (g : Su K 2 f 2) :
    ((chainNode E hK hq k g : DΩ E 3) :
        (Fin 4 → K) ≃ₗ[F] (Fin 4 → K)) =
      suEndN (F := F) (unitaryInvolution K 2 f) 4 (blockEmb2 K 2 f 3 k g) := by
  change ((Subgroup.subtype (orthDerived (Qn E 4)))
    ((stdFamilyΩ E 3 le_rfl hK hq).ι (Fin.castSucc k) g) : _) = _
  rw [← MonoidHom.comp_apply, coe_stdFamilyΩ_ι, stdFamilyV_ι_castSucc]
  rfl

private theorem stdEmb_comp_chainNode (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin 3) :
    (stdEmb E).comp (chainNode E hK hq k) =
      (pureEmb E ((stdPairEmb k).trans stdPerm.toEmbedding)).comp (suTwo E hK hq) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  change ((pureEmb E stdPerm.toEmbedding (chainNode E hK hq k g) : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) v =
    ((pureEmb E ((stdPairEmb k).trans stdPerm.toEmbedding) (suTwo E hK hq g) :
      normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) v
  rw [pureEmb_apply, pureEmb_apply]
  congr 1
  rw [chainNode_coe, suTwo_coe, suEndN_blockEmb2_eq_coordExt, coordExt_trans]

private theorem map_univ_stdPairEmb_zero :
    Finset.univ.map ((stdPairEmb 0).trans stdPerm.toEmbedding) = ({0, 3} : Finset (Fin 4)) := by
  decide

private theorem map_univ_stdPairEmb_one :
    Finset.univ.map ((stdPairEmb 1).trans stdPerm.toEmbedding) = ({0, 1} : Finset (Fin 4)) := by
  decide

private theorem map_univ_stdPairEmb_two :
    Finset.univ.map ((stdPairEmb 2).trans stdPerm.toEmbedding) = ({1, 2} : Finset (Fin 4)) := by
  decide

noncomputable def stdNode (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (k : Fin 4) :
    Subgroup (normOmega E 4) :=
  ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).ι k)).range

private theorem chainNode_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (k : Fin 3) (S : Finset (Fin 4))
    (hS : Finset.univ.map ((stdPairEmb k).trans stdPerm.toEmbedding) = S) :
    stdNode E hK hq (Fin.castSucc k) ≤ normPureBlock E 4 S := by
  unfold stdNode
  calc
    ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).ι (Fin.castSucc k))).range
        = ((stdEmb E).comp (chainNode E hK hq k)).range := rfl
    _ = (suTwo E hK hq).range.map
          (pureEmb E ((stdPairEmb k).trans stdPerm.toEmbedding)) := by
          rw [stdEmb_comp_chainNode, MonoidHom.range_comp]
    _ ≤ (pureEmb E ((stdPairEmb k).trans stdPerm.toEmbedding)).range :=
          Subgroup.map_le_range _ _
    _ = normPureBlock E 4 S := by rw [range_pureEmb, hS]

theorem stdNode_zero_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 0 ≤ normPureBlock E 4 {0, 3} := by
  simpa using chainNode_le E hK hq 0 {0, 3} map_univ_stdPairEmb_zero

theorem stdNode_one_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 1 ≤ normPureBlock E 4 {0, 1} := by
  simpa using chainNode_le E hK hq 1 {0, 1} map_univ_stdPairEmb_one

theorem stdNode_two_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 2 ≤ normPureBlock E 4 {1, 2} := by
  simpa using chainNode_le E hK hq 2 {1, 2} map_univ_stdPairEmb_two


noncomputable def tauConjDerived (n : ℕ) (j : Fin n) :
    MulAut (orthDerived (Qn E n)) :=
  letI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  letI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  ((MulAut.conj (tauAt E j)).subgroupMap (orthDerived (Qn E n))).trans
    (MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.KFR4.DLe.map_conj_orthDerived (Qn E n)
        (tauAt_mem_orthogonalGroup E j)))

private theorem tauConjDerived_val (n : ℕ) (j : Fin n) (x : orthDerived (Qn E n)) :
    ((tauConjDerived E n j x : orthDerived (Qn E n)) :
        (Fin n → K) ≃ₗ[F] (Fin n → K)) =
      (tauAt E j) * (x : (Fin n → K) ≃ₗ[F] (Fin n → K)) * (tauAt E j)⁻¹ := rfl

private theorem stdEmb_coe (x : DΩ E 3) :
    ((stdEmb E x : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      hypExt (coordExt stdPerm.toEmbedding (x : (Fin 4 → K) ≃ₗ[F] (Fin 4 → K))) := by
  apply LinearEquiv.ext
  intro v
  change ((pureEmb E stdPerm.toEmbedding x : normOmega E 4) :
    ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) v = _
  rw [pureEmb_apply]
  rfl

theorem stdEmb_tauConj (c : Fin 4) (x : DΩ E 3) :
    stdEmb E (tauConjDerived E 4 c x) =
      tauConj E 4 (stdPerm c) (stdEmb E x) := by
  apply Subtype.ext
  have hL := stdEmb_coe E (tauConjDerived E 4 c x)
  have hx := stdEmb_coe E x
  rw [hL]
  conv_rhs => rw [tauConj_coe]
  conv_rhs => rw [hx]
  rw [tauConjDerived_val, map_mul, map_mul, map_inv, coordExt_tauAt]
  set A : (Fin 4 → K) ≃ₗ[F] (Fin 4 → K) := tauAt E (stdPerm c) with hA
  set B : (Fin 4 → K) ≃ₗ[F] (Fin 4 → K) :=
    coordExt stdPerm.toEmbedding (x : (Fin 4 → K) ≃ₗ[F] (Fin 4 → K)) with hB
  change hypExt (K := F) (W := Fin 4 → K) (A * B * A⁻¹) =
    hypExt (K := F) (W := Fin 4 → K) A * hypExt (K := F) (W := Fin 4 → K) B *
      (hypExt (K := F) (W := Fin 4 → K) A)⁻¹
  change (hypExtHom (F := F) (K := K) 4) (A * B * A⁻¹) =
    (hypExtHom (F := F) (K := K) 4) A * (hypExtHom (F := F) (K := K) 4) B *
      ((hypExtHom (F := F) (K := K) 4) A)⁻¹
  rw [map_mul, map_mul, map_inv]

private theorem stdEmb_comp_tauConjDerived (c : Fin 4) :
    (stdEmb E).comp (tauConjDerived E 4 c).toMonoidHom =
      (tauConj E 4 (stdPerm c)).toMonoidHom.comp (stdEmb E) :=
  MonoidHom.ext (stdEmb_tauConj E c)

private theorem iota_three_coe (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (g : Su K 2 f 2) :
    (((stdFamilyΩ E 3 le_rfl hK hq).ι 3 g : DΩ E 3) :
        (Fin 4 → K) ≃ₗ[F] (Fin 4 → K)) =
      (tauAt E 3) * (((stdFamilyΩ E 3 le_rfl hK hq).ι 2 g : DΩ E 3) :
        (Fin 4 → K) ≃ₗ[F] (Fin 4 → K)) * (tauAt E 3)⁻¹ := by
  change ((Subgroup.subtype (orthDerived (Qn E 4)))
    ((stdFamilyΩ E 3 le_rfl hK hq).ι 3 g) : _) = _
  rw [← MonoidHom.comp_apply, coe_stdFamilyΩ_ι]
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, stdFamilyV_ι_last]
  unfold stdForkIota stdConj stdTau
  rw [MonoidHom.comp_apply]
  change MulAut.conj (tauAt E (Fin.last 3))
      ((stdChainIota (F := F) (f := f) 3 ⟨3 - 1, by omega⟩) g) =
    tauAt E (Fin.last 3) * _ * (tauAt E (Fin.last 3))⁻¹
  rw [MulAut.conj_apply]
  congr 2

private theorem iota_three_eq (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((stdFamilyΩ E 3 le_rfl hK hq).ι 3) =
      (tauConjDerived E 4 3).toMonoidHom.comp
        ((stdFamilyΩ E 3 le_rfl hK hq).ι 2) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [MonoidHom.comp_apply]
  change (((stdFamilyΩ E 3 le_rfl hK hq).ι 3 g : DΩ E 3) :
      (Fin 4 → K) ≃ₗ[F] (Fin 4 → K)) =
    ((tauConjDerived E 4 3
      (((stdFamilyΩ E 3 le_rfl hK hq).ι 2) g) : DΩ E 3) :
        (Fin 4 → K) ≃ₗ[F] (Fin 4 → K))
  rw [iota_three_coe, tauConjDerived_val]

theorem stdNode_three (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 3 = (stdNode E hK hq 2).map (tauConj E 4 2).toMonoidHom := by
  unfold stdNode
  rw [iota_three_eq E hK hq]
  rw [← MonoidHom.comp_assoc, stdEmb_comp_tauConjDerived E 3]
  rw [show stdPerm 3 = 2 from stdPerm_three]
  rw [MonoidHom.range_comp]
  conv_rhs => rw [MonoidHom.range_comp]
  rw [Subgroup.map_map]

private noncomputable def swapSU : Su K 2 f 2 :=
  CFSG.SectionRank.EvenCover.swapSU (K := K) (f := f)

private theorem coordExt_suTwo_swapSU (e : Fin 2 ↪ Fin 4) (x : Fin 4 → K) (j : Fin 4) :
    coordExt e (suEndN (F := F) (unitaryInvolution K 2 f) 2 (swapSU (K := K) (f := f))) x j =
      x (Equiv.swap (e 0) (e 1) j) := by
  rw [coordExt_apply]
  by_cases h0 : j = e 0
  · subst j
    rw [e.injective.extend_apply, suEndN_apply, smul_def]
    change (Matrix.mulVec (CFSG.SectionRank.EvenCover.swapMat (K := K)) (x ∘ e)) 0 = _
    simp [CFSG.SectionRank.EvenCover.swapMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Function.comp_apply, Equiv.swap_apply_left]
  · by_cases h1 : j = e 1
    · subst j
      rw [e.injective.extend_apply, suEndN_apply, smul_def]
      change (Matrix.mulVec (CFSG.SectionRank.EvenCover.swapMat (K := K)) (x ∘ e)) 1 = _
      simp [CFSG.SectionRank.EvenCover.swapMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_apply, Equiv.swap_apply_right]
    · rw [Function.extend_apply' _ _ _ (by
        rintro ⟨i, hi⟩
        fin_cases i
        · exact h0 (by simpa using hi.symm)
        · exact h1 (by simpa using hi.symm))]
      rw [Equiv.swap_apply_of_ne_of_ne (a := e 0) (b := e 1) (x := j) h0 h1]

private theorem pureEmb_suTwo_swapSU (e : Fin 2 ↪ Fin 4) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) :
    pureEmb E e (suTwo E hK hq (swapSU (K := K) (f := f))) =
      normPerm E (by norm_num : 3 ≤ 4) (Equiv.swap (e 0) (e 1)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [pureEmb_apply, normPerm_apply]
  congr 1
  funext j
  rw [suTwo_coe, coordExt_suTwo_swapSU, Equiv.swap_inv]

private theorem stdPairEmb_trans_stdPerm_zero (k : Fin 3) :
    ((stdPairEmb k).trans stdPerm.toEmbedding) 0 = stdPerm (Fin.castSucc k) := by
  change stdPerm (stdPairEmb k 0) = stdPerm (Fin.castSucc k)
  rw [stdPairEmb_zero]
  rfl

private theorem stdPairEmb_trans_stdPerm_one (k : Fin 3) :
    ((stdPairEmb k).trans stdPerm.toEmbedding) 1 = stdPerm (Fin.castSucc k + 1) := by
  change stdPerm (stdPairEmb k 1) = stdPerm (Fin.castSucc k + 1)
  rw [stdPairEmb_one]
  congr 1
  apply Fin.ext
  have hk : (Fin.castSucc k).val + 1 < 4 := by
    simp only [Fin.val_castSucc]
    have := k.isLt
    omega
  rw [Fin.val_add_one_of_lt' hk]
  simp only [Fin.val_castSucc]

theorem normPerm_swap_mem_stdNode (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (k : Fin 4) (hk : (k : ℕ) < 3) :
    normPerm E (by norm_num) (Equiv.swap (stdPerm k) (stdPerm (k + 1))) ∈
      stdNode E hK hq k := by
  let k' : Fin 3 := ⟨k, hk⟩
  have hk_eq : k = Fin.castSucc k' := Fin.ext rfl
  rw [hk_eq, stdNode, MonoidHom.mem_range]
  refine ⟨swapSU (K := K) (f := f), ?_⟩
  have h := congrArg
    (fun g : Su K 2 f 2 →* normOmega E 4 => g (swapSU (K := K) (f := f)))
    (stdEmb_comp_chainNode E hK hq k')
  change (stdEmb E) ((chainNode E hK hq k') (swapSU (K := K) (f := f))) = _
  rw [show (stdEmb E) ((chainNode E hK hq k') (swapSU (K := K) (f := f))) =
      (pureEmb E ((stdPairEmb k').trans stdPerm.toEmbedding)).comp (suTwo E hK hq)
        (swapSU (K := K) (f := f)) from h]
  rw [MonoidHom.comp_apply, pureEmb_suTwo_swapSU]
  congr 1
  rw [stdPairEmb_trans_stdPerm_zero, stdPairEmb_trans_stdPerm_one]

noncomputable def stdNodeTw (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    Subgroup (normOmega E 4) :=
  (stdNode E hK hq 1).map (tauConj E 4 1).toMonoidHom

private theorem card_base_eq_pow (E : QuadExt F K (unitaryInvolution K 2 f))
    (hK : Nat.card K = (2 ^ f) ^ 2) : Nat.card F = 2 ^ f := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have h1 : Nat.card K = Nat.card F ^ Module.finrank F K :=
    Module.natCard_eq_pow_finrank (K := F) (V := K)
  rw [E.finrank_eq] at h1
  have h2 : Nat.card F ^ 2 = (2 ^ f) ^ 2 := by rw [← h1, hK]
  exact Nat.pow_left_injective (by norm_num) h2

private theorem card_su_two_eq (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (Su K 2 f 2) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
  rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv P hP).toEquiv,
    CFSG.LieType.Steinberg.card_SU_two (p := 2) hK]

private theorem card_stdNode (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (k : Fin 4) :
    Nat.card (stdNode E hK hq k) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hinj : Function.Injective
      ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).ι k)) :=
    (stdEmb_injective E).comp ((stdFamilyΩ_good E 3 le_rfl hK hq).inj k)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [show stdNode E hK hq k =
      ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).ι k)).range from rfl]
  rw [← h, card_su_two_eq hK]

private theorem stdNode_three_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 3 ≤ normPureBlock E 4 {1, 2} := by
  rw [stdNode_three E hK hq]
  calc
    (stdNode E hK hq 2).map (tauConj E 4 2).toMonoidHom
        ≤ (normPureBlock E 4 {1, 2}).map (tauConj E 4 2).toMonoidHom :=
          Subgroup.map_mono (stdNode_two_le E hK hq)
    _ = normPureBlock E 4 {1, 2} :=
      map_normPureBlock_tauConj (E := E) (n := 4) (j := 2) (S := {1, 2})

private theorem disjoint_stdNode_two_three (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 2 ⊓ stdNode E hK hq 3 = ⊥ := by
  rw [stdNode, stdNode, MonoidHom.range_comp, MonoidHom.range_comp,
    ← Subgroup.map_inf_eq _ _ _ (stdEmb_injective E),
    (stdFamilyΩ_good E 3 le_rfl hK hq).disj 2 3 (by decide), Subgroup.map_bot]

private theorem commute_stdNode_two_three (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) :
    ∀ x ∈ stdNode E hK hq 2, ∀ y ∈ stdNode E hK hq 3, x * y = y * x := by
  have hM : CFSG.StandardType.ggCoxeterMatrixD 4 2 3 = 2 := by
    rw [CFSG.StandardType.ggCoxeterMatrixD_apply]
    decide
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, (stdFamilyΩ E 3 le_rfl hK hq).comm 2 3 hM a b, map_mul]

theorem stdNode_two_sup_three (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 2 ⊔ stdNode E hK hq 3 = normPureBlock E 4 {1, 2} := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : Finite (normOmega E 4) := Subtype.finite
  have hle : stdNode E hK hq 2 ⊔ stdNode E hK hq 3 ≤ normPureBlock E 4 {1, 2} :=
    sup_le (stdNode_two_le E hK hq) (stdNode_three_le E hK hq)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_sup_eq_mul_of_disjoint_of_le_normalizer]
  · rw [card_stdNode E hK hq, card_stdNode E hK hq]
    rw [card_normPureBlock_pair (E := E) (hq := by rw [card_base_eq_pow E hK]; exact hq)
      (n := 4) (i := 1) (j := 2) (hij := by decide)]
    rw [card_base_eq_pow E hK]
    ring_nf
    exact le_rfl
  · refine Subgroup.le_normalizer_iff.mpr fun y hy x hx => ?_
    have hyx : y * x * y⁻¹ = x := by
      rw [show y * x = x * y from (commute_stdNode_two_three E hK hq x hx y hy).symm]
      group
    rw [hyx]
    exact hx
  · rw [disjoint_iff]
    exact disjoint_stdNode_two_three E hK hq

private noncomputable abbrev stdRho : normOmega E 4 :=
  normPerm E (by norm_num : 3 ≤ 4) stdPerm

private theorem stdNode_eq_map_pureEmb (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin 3) :
    stdNode E hK hq (Fin.castSucc k) =
      (suTwo E hK hq).range.map
        (pureEmb E ((stdPairEmb k).trans stdPerm.toEmbedding)) := by
  rw [stdNode]
  change ((stdEmb E).comp (chainNode E hK hq k)).range = _
  rw [stdEmb_comp_chainNode, MonoidHom.range_comp]

private theorem map_conj_stdRho_stdNode_two (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) :
    (stdNode E hK hq 2).map (MulAut.conj (stdRho E)).toMonoidHom =
      stdNode E hK hq 1 := by
  rw [show (2 : Fin 4) = Fin.castSucc (2 : Fin 3) from rfl,
    show (1 : Fin 4) = Fin.castSucc (1 : Fin 3) from rfl,
    stdNode_eq_map_pureEmb E hK hq 2, stdNode_eq_map_pureEmb E hK hq 1,
    Subgroup.map_map]
  congr 2
  rw [show stdRho E = normPerm E (by norm_num : 3 ≤ 4) stdPerm from rfl,
    conj_normPerm_comp_pureEmb (E := E) (n := 4) (by norm_num) stdPerm]
  congr 1
  ext i
  fin_cases i <;> rfl

private theorem conj_stdRho_comp_tauConj (j : Fin 4) :
    (MulAut.conj (stdRho E)).toMonoidHom.comp
        (tauConj E 4 j).toMonoidHom =
      (tauConj E 4 (stdPerm j)).toMonoidHom.comp
        (MulAut.conj (stdRho E)).toMonoidHom :=
  MonoidHom.ext fun x =>
    conj_normPerm_tauConj (E := E) (n := 4) (by norm_num) stdPerm j x

private theorem map_conj_stdRho_stdNode_three (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) :
    (stdNode E hK hq 3).map (MulAut.conj (stdRho E)).toMonoidHom =
      stdNodeTw E hK hq := by
  rw [stdNode_three E hK hq, stdNodeTw, Subgroup.map_map,
    conj_stdRho_comp_tauConj, stdPerm_two, ← Subgroup.map_map,
    map_conj_stdRho_stdNode_two E hK hq]

theorem stdNode_one_sup_tw (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 1 ⊔ stdNodeTw E hK hq = normPureBlock E 4 {0, 1} := by
  have h := congrArg
    (fun H : Subgroup (normOmega E 4) =>
      H.map (MulAut.conj (stdRho E)).toMonoidHom)
    (stdNode_two_sup_three E hK hq)
  rw [Subgroup.map_sup, map_conj_stdRho_stdNode_two E hK hq,
    map_conj_stdRho_stdNode_three E hK hq] at h
  rw [show (normPureBlock E 4 {1, 2}).map
      (MulAut.conj (stdRho E)).toMonoidHom =
      normPureBlock E 4 ((({1, 2} : Finset (Fin 4))).image stdPerm) from by
    rw [show stdRho E = normPerm E (by norm_num : 3 ≤ 4) stdPerm from rfl,
      map_normPureBlock_normPerm (E := E) (n := 4) (by norm_num) stdPerm {1, 2}]] at h
  have hset : ({1, 2} : Finset (Fin 4)).image stdPerm = {0, 1} := by decide
  rwa [hset] at h

theorem commute_stdNode_one_tw (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {x y : normOmega E 4} (hx : x ∈ stdNode E hK hq 1) (hy : y ∈ stdNodeTw E hK hq) :
    x * y = y * x := by
  have hx' : x ∈ (stdNode E hK hq 2).map (MulAut.conj (stdRho E)).toMonoidHom := by
    rw [map_conj_stdRho_stdNode_two E hK hq]
    exact hx
  have hy' : y ∈ (stdNode E hK hq 3).map (MulAut.conj (stdRho E)).toMonoidHom := by
    rw [map_conj_stdRho_stdNode_three E hK hq]
    exact hy
  obtain ⟨x', hx₂, rfl⟩ := Subgroup.mem_map.mp hx'
  obtain ⟨y', hy₃, rfl⟩ := Subgroup.mem_map.mp hy'
  rw [← map_mul, ← map_mul, commute_stdNode_two_three E hK hq x' hx₂ y' hy₃]

private theorem isSimpleGroup_stdNode_one (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) : IsSimpleGroup (stdNode E hK hq 1) := by
  have hinj : Function.Injective
      ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 1)) :=
    (stdEmb_injective E).comp ((stdFamilyΩ_good E 3 le_rfl hK hq).inj 1)
  have : IsSimpleGroup (Su K 2 f 2) := isSimpleGroup_Su_two hK hq
  exact MulEquiv.isSimpleGroup (MonoidHom.ofInjective hinj).symm

private theorem isSimpleGroup_stdNodeTw (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) : IsSimpleGroup (stdNodeTw E hK hq) := by
  have := isSimpleGroup_stdNode_one E hK hq
  exact MulEquiv.isSimpleGroup
    (Subgroup.equivMapOfInjective (stdNode E hK hq 1) (tauConj E 4 1).toMonoidHom
      (tauConj E 4 1).injective).symm

private theorem card_stdNodeTw (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    Nat.card (stdNodeTw E hK hq) = Nat.card (stdNode E hK hq 1) := by
  rw [stdNodeTw]
  exact Subgroup.card_map_of_injective (tauConj E 4 1).injective

theorem eq_or_eq_stdNode_one (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {X : Subgroup (normOmega E 4)} (hX : X ≤ normPureBlock E 4 {0, 1})
    (hn : normPureBlock E 4 {0, 1} ≤ Subgroup.normalizer (X : Set (normOmega E 4)))
    (hc : Nat.card X = Nat.card (Su K 2 f 2))
    (hnab : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) :
    X = stdNode E hK hq 1 ∨ X = stdNodeTw E hK hq := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : Finite (normOmega E 4) := Subtype.finite
  refine eq_or_eq_of_le_sup_of_isSimpleGroup
    (A := stdNode E hK hq 1) (B := stdNodeTw E hK hq) (X := X)
    (fun a ha b hb => commute_stdNode_one_tw E hK hq ha hb)
    (isSimpleGroup_stdNode_one E hK hq)
    (isSimpleGroup_stdNodeTw E hK hq) ?_ ?_ ?_ ?_ hnab
  · rw [stdNode_one_sup_tw E hK hq]
    exact hX
  · rw [stdNode_one_sup_tw E hK hq]
    exact hn
  · rw [card_stdNode E hK hq 1, ← card_su_two_eq hK]
    exact hc
  · rw [card_stdNodeTw E hK hq, card_stdNode E hK hq 1, ← card_su_two_eq hK]
    exact hc

theorem stdNode_zero_sup (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 0 ⊔ normPureBlock E 4 {0, 1} = normPureBlock E 4 {0, 1, 3} := by
  have hq2 : 2 < Nat.card F := by
    rw [card_base_eq_pow E hK]
    omega
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact (stdNode_zero_le E hK hq).trans (normPureBlock_mono E 4 (by decide))
    · exact normPureBlock_mono E 4 (by decide)
  · have hσeq : Equiv.swap (stdPerm 0) (stdPerm (0 + 1)) = Equiv.swap (3 : Fin 4) 0 := by
      have h1 : stdPerm (0 + 1) = (0 : Fin 4) := by decide
      rw [stdPerm_zero, h1]
    let σ : Equiv.Perm (Fin 4) := Equiv.swap 3 0
    have hσmem : normPerm E (by norm_num : 3 ≤ 4) σ ∈ stdNode E hK hq 0 := by
      rw [show σ = Equiv.swap (stdPerm 0) (stdPerm (0 + 1)) from hσeq.symm]
      exact normPerm_swap_mem_stdNode E hK hq 0 (by norm_num)
    have hconj : (normPureBlock E 4 {0, 1}).map
        (MulAut.conj (normPerm E (by norm_num : 3 ≤ 4) σ)).toMonoidHom ≤
        stdNode E hK hq 0 ⊔ normPureBlock E 4 {0, 1} := by
      rintro - ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hσmem) (Subgroup.mem_sup_right hx))
        (Subgroup.mem_sup_left (inv_mem hσmem))
    have hset : ({0, 1} : Finset (Fin 4)).image σ = {1, 3} := by
      dsimp [σ]
      decide
    have hmap := map_normPureBlock_normPerm (E := E) (n := 4) (by norm_num) σ {0, 1}
    rw [hset] at hmap
    have hP13 : normPureBlock E 4 {1, 3} ≤
        stdNode E hK hq 0 ⊔ normPureBlock E 4 {0, 1} := by
      rw [← hmap]
      exact hconj
    have hpair := normPureBlock_pair_sup_pair (E := E) (hq := hq2) (n := 4)
      (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide)
    calc
      normPureBlock E 4 {0, 1, 3} = normPureBlock E 4 {0, 1} ⊔ normPureBlock E 4 {1, 3} :=
        hpair.symm
      _ ≤ stdNode E hK hq 0 ⊔ normPureBlock E 4 {0, 1} := sup_le le_sup_right hP13

theorem stdNode_one_sup (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    stdNode E hK hq 1 ⊔ normPureBlock E 4 {1, 2} = normPureBlock E 4 {0, 1, 2} := by
  have hq2 : 2 < Nat.card F := by
    rw [card_base_eq_pow E hK]
    omega
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact (stdNode_one_le E hK hq).trans (normPureBlock_mono E 4 (by decide))
    · exact normPureBlock_mono E 4 (by decide)
  · have hσeq : Equiv.swap (stdPerm 1) (stdPerm (1 + 1)) = Equiv.swap (0 : Fin 4) 1 := by
      have h1 : stdPerm (1 + 1) = (1 : Fin 4) := by decide
      rw [stdPerm_one, h1]
    let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
    have hσmem : normPerm E (by norm_num : 3 ≤ 4) σ ∈ stdNode E hK hq 1 := by
      rw [show σ = Equiv.swap (stdPerm 1) (stdPerm (1 + 1)) from hσeq.symm]
      exact normPerm_swap_mem_stdNode E hK hq 1 (by norm_num)
    have hconj : (normPureBlock E 4 {1, 2}).map
        (MulAut.conj (normPerm E (by norm_num : 3 ≤ 4) σ)).toMonoidHom ≤
        stdNode E hK hq 1 ⊔ normPureBlock E 4 {1, 2} := by
      rintro - ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hσmem) (Subgroup.mem_sup_right hx))
        (Subgroup.mem_sup_left (inv_mem hσmem))
    have hset : ({1, 2} : Finset (Fin 4)).image σ = {0, 2} := by
      dsimp [σ]
      decide
    have hmap := map_normPureBlock_normPerm (E := E) (n := 4) (by norm_num) σ {1, 2}
    rw [hset] at hmap
    have hP02 : normPureBlock E 4 {0, 2} ≤
        stdNode E hK hq 1 ⊔ normPureBlock E 4 {1, 2} := by
      rw [← hmap]
      exact hconj
    have hpair := normPureBlock_pair_sup_pair (E := E) (hq := hq2) (n := 4)
      (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
    have hpair' : normPureBlock E 4 {0, 1, 2} =
        normPureBlock E 4 {1, 2} ⊔ normPureBlock E 4 {0, 2} := by
      rw [show ({2, 0} : Finset (Fin 4)) = {0, 2} from by decide,
        show ({1, 0, 2} : Finset (Fin 4)) = {0, 1, 2} from by decide] at hpair
      exact hpair.symm
    calc
      normPureBlock E 4 {0, 1, 2} = normPureBlock E 4 {1, 2} ⊔ normPureBlock E 4 {0, 2} :=
        hpair'
      _ ≤ stdNode E hK hq 1 ⊔ normPureBlock E 4 {1, 2} := sup_le le_sup_right hP02

private theorem ggD_zero_one : CFSG.StandardType.ggCoxeterMatrixD 4 0 1 = 3 := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply]
  decide

private theorem ggD_one_two : CFSG.StandardType.ggCoxeterMatrixD 4 1 2 = 3 := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply]
  decide

private theorem ggD_one_three : CFSG.StandardType.ggCoxeterMatrixD 4 1 3 = 3 := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply]
  decide

theorem stdEdge01_le (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 0 1)).range ≤
      normPureBlock E 4 {0, 1, 3} := by
  have hθ := PhanFamilyE.range_θ_eq_sup (S := stdFamilyΩ E 3 le_rfl hK hq)
    (hK := hK) (hq := pow_ne_two_of_four_le hq) (i := 0) (j := 1)
    (hij := by decide) (h3 := ggD_zero_one)
  rw [MonoidHom.range_comp, hθ, Subgroup.map_sup,
    show Subgroup.map (stdEmb E) ((stdFamilyΩ E 3 le_rfl hK hq).ι 0).range =
      stdNode E hK hq 0 from by rw [stdNode, MonoidHom.range_comp],
    show Subgroup.map (stdEmb E) ((stdFamilyΩ E 3 le_rfl hK hq).ι 1).range =
      stdNode E hK hq 1 from by rw [stdNode, MonoidHom.range_comp]]
  refine sup_le ?_ ?_
  · exact (stdNode_zero_le E hK hq).trans (normPureBlock_mono E 4 (by decide))
  · exact (stdNode_one_le E hK hq).trans (normPureBlock_mono E 4 (by decide))

theorem stdEdges_sup (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2)).range ⊔
      ((stdEmb E).comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3)).range =
        normPureBlock E 4 {0, 1, 2} := by
  have h12 := PhanFamilyE.range_θ_eq_sup (S := stdFamilyΩ E 3 le_rfl hK hq)
    (hK := hK) (hq := pow_ne_two_of_four_le hq) (i := 1) (j := 2)
    (hij := by decide) (h3 := ggD_one_two)
  have h13 := PhanFamilyE.range_θ_eq_sup (S := stdFamilyΩ E 3 le_rfl hK hq)
    (hK := hK) (hq := pow_ne_two_of_four_le hq) (i := 1) (j := 3)
    (hij := by decide) (h3 := ggD_one_three)
  rw [MonoidHom.range_comp, MonoidHom.range_comp, h12, h13,
    Subgroup.map_sup, Subgroup.map_sup,
    show Subgroup.map (stdEmb E) ((stdFamilyΩ E 3 le_rfl hK hq).ι 1).range =
      stdNode E hK hq 1 from by rw [stdNode, MonoidHom.range_comp],
    show Subgroup.map (stdEmb E) ((stdFamilyΩ E 3 le_rfl hK hq).ι 2).range =
      stdNode E hK hq 2 from by rw [stdNode, MonoidHom.range_comp],
    show Subgroup.map (stdEmb E) ((stdFamilyΩ E 3 le_rfl hK hq).ι 3).range =
      stdNode E hK hq 3 from by rw [stdNode, MonoidHom.range_comp]]
  change (stdNode E hK hq 1 ⊔ stdNode E hK hq 2) ⊔
      (stdNode E hK hq 1 ⊔ stdNode E hK hq 3) = normPureBlock E 4 {0, 1, 2}
  have h : (stdNode E hK hq 1 ⊔ stdNode E hK hq 2) ⊔
      (stdNode E hK hq 1 ⊔ stdNode E hK hq 3) =
        stdNode E hK hq 1 ⊔ (stdNode E hK hq 2 ⊔ stdNode E hK hq 3) := by
    ac_rfl
  rw [h, stdNode_two_sup_three E hK hq, stdNode_one_sup E hK hq]

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
