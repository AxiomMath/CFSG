module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClDist
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClDeg
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Fischer.Uniq.CompTau
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
import CFSG.Monster.Existence.Defs
import CFSG.Open.MonsterY443Defs
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Polynomial CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (quasisimple_or_solvable_spSupported)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
theorem false_of_component_statedSp_five {r f e : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) {x : StatedSp r K} (hx : x ^ 5 = 1)
    (hx1 : x ≠ 1) {J : Subgroup (StatedProj (StatedSp r K))}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))))
    (hZ : Subgroup.center ↥J = ⊥) (h5 : 5 ∣ 2 ^ e + 1)
    (hcard : Nat.card J = ordTwistedA 4 (2 ^ e)) : False := by
  classical
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num at h5
    · exact he
  have hπ : ∀ s, 1 ≤ s → Function.Bijective (SymplecticFlag.proj s K) := fun s hs => by
    haveI : NeZero s := ⟨by omega⟩
    exact UnitaryHigher.proj_bijective_of_charTwo
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 (hπ r hr).1]
    exact bot_le
  have hxp : orderOf x = 5 := orderOf_eq_prime hx hx1
  have hap : orderOf (SymplecticFlag.proj r K x) = 5 := by
    rw [orderOf_injective _ (hπ r hr).1 x, hxp]
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK
    (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num) hr _ hap).2 x rfl hxp
  have hpK : ((5 : ℕ) : K) ≠ 0 := fun h0 =>
    absurd ((CharP.cast_eq_zero_iff K 2 5).1 h0) (by norm_num)
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  obtain ⟨⟨O, k, hk, rfl⟩, hQ, hJeq⟩ := components_conj_of_orbit_family
    (SymplecticFlag.proj r K) (hπ r hr).2 hZc x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => quasisimple_or_solvable_spSupported (by norm_num) hq hsq blocks O) J hJ
  obtain ⟨Y, _, _, ψ, hψ, hψr, -, hfac⟩ := good_spSupported_of_factor (a6 := False) (p := 5)
    (by norm_num) hK (ringChar.eq K 2) False.elim slFactorFacts_holds False.elim
    suFactorFacts_holds False.elim spFactorFacts_holds False.elim spFourTwoFacts_holds hq hsq
    blocks ⟨k, hk⟩ hQ
  have hJY : J = ((SymplecticFlag.proj r K).comp ψ).range := by
    rw [MonoidHom.range_comp, hψr]
    exact hJeq
  let eY : Y ≃* ↥J :=
    (MonoidHom.ofInjective (f := (SymplecticFlag.proj r K).comp ψ) ((hπ r hr).1.comp hψ)).trans
      (MulEquiv.subgroupCongr hJY.symm)
  have hZY : Subgroup.center Y = ⊥ := by
    rw [← Subgroup.map_center_eq eY.symm, hZ, Subgroup.map_bot]
  rcases hfac with ⟨m, j, E, _, _, hm, hj, -, hEc, h4, ⟨eS⟩⟩ |
    ⟨m, j, q', E, _, _, hm3, hj, -, hq', hEc, hne, ⟨eS⟩⟩ | ⟨-, -, s, hs2, hne, ⟨eS⟩⟩ |
    ⟨-, -, hK2, ⟨eS⟩⟩
  ·
    have hfj : 1 ≤ f * j := Nat.mul_pos hf hj
    have hEn : Nat.card E = 2 ^ (f * j) := by rw [Nat.card_eq_fintype_card, hEc, hK, ← pow_mul]
    have hZS : Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) = ⊥ := by
      rw [← Subgroup.map_center_eq eS, hZY, Subgroup.map_bot]
    have h4' : m = 2 → 4 ≤ 2 ^ (f * j) := fun h2 => by
      rw [← hEn, Nat.card_eq_fintype_card]
      exact h4 h2
    have hmod : StatedClassicalModel ↥J .PSL m 2 (f * j) :=
      ⟨⟨Nat.prime_two, hfj, hm, fun hc => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj hc
        have := h4' h1
        omega, fun hc => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj hc
        have := h4' h1
        omega⟩, E, inferInstance, inferInstance, hEn,
        ⟨eY.symm.trans (eS.trans (QuotientGroup.quotientBot.symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hZS.symm).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E))))⟩⟩
    exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := m - 1) (u := 4) (by omega) hfj
      (by norm_num) he1
      (((CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl).symm.trans hcard)
  ·
    have hfj : 1 ≤ f * j := Nat.mul_pos hf hj
    obtain rfl : q' = 2 ^ (f * j) := by rw [hq', hK, ← pow_mul]
    have hEn : Nat.card E = (2 ^ (f * j)) ^ 2 := by rw [Nat.card_eq_fintype_card, hEc]
    have hZS : Subgroup.center ↥(StatedSU m (2 ^ (f * j)) E) = ⊥ := by
      rw [← Subgroup.map_center_eq eS, hZY, Subgroup.map_bot]
    have hQS := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) hEn hm3 hne
    have hmod : StatedClassicalModel ↥J .PSU m 2 (f * j) :=
      ⟨⟨Nat.prime_two, hfj, hm3, hne⟩, E, inferInstance, inferInstance, hEn,
        ⟨eY.symm.trans (eS.trans (QuotientGroup.quotientBot.symm.trans
          (QuotientGroup.quotientMulEquivOfEq (hZS.symm.trans hQS.2))))⟩⟩
    obtain ⟨hm5, hfje⟩ := eq_four_of_ordTwistedA_eq (by omega) hfj he1
      (((CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl).symm.trans hcard)
    obtain rfl : m = 5 := by omega
    exact center_statedSU_five_ne_bot hEn (by rw [hfje]; exact h5) hZS
  ·
    have hne' : (s, 2 ^ f) ≠ (2, 2) := by rwa [hK] at hne
    have hmod : StatedClassicalModel ↥J .PSp s 2 f :=
      ⟨⟨Nat.prime_two, hf, hs2, hne'⟩, K, inferInstance, inferInstance, hK,
        ⟨eY.symm.trans (eS.trans
          (MulEquiv.ofBijective (SymplecticFlag.proj s K) (hπ s (by omega))))⟩⟩
    exact ordBC_ne_ordTwistedA_four (by omega) hf he1
      (((CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.1 rfl).symm.trans hcard)
  ·
    have h720 : Nat.card ↥(StatedSp 2 K) = 720 := by
      rw [SymplecticFlag.card_statedSp_two, hK2] <;> norm_num
    have hdvd : ordTwistedA 4 (2 ^ e) ∣ 720 := by
      rw [← hcard, ← Nat.card_congr eY.toEquiv, Nat.card_congr eS.toEquiv, ← h720]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨t, -, ht⟩ :=
      (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 4) (by norm_num) he1).two
    have h2 : 2 ^ 10 ∣ 720 :=
      ((Nat.pow_dvd_pow 2 (by omega : 10 ≤ e * (4 * (4 + 1) / 2))).trans ⟨t, ht⟩).trans hdvd
    norm_num at h2

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
