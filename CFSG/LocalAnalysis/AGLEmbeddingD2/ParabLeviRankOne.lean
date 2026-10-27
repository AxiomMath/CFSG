module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParND
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParRank1
import CFSG.LieType.TitsSimplicity.Core
import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.Certificates.CosetTableShort
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.ClassicalGroups
import CFSG.GroupTheory.SteinbergCBFTCores
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
import CFSG.Holt.Centralizer
import CFSG.LieType.Simplicity.Basic
import CFSG.LieType.SteinbergBRTwoRankBound
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutatorFixed
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FixedPointsTwo
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRAssemble
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltBigVector
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltFixed
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactE9U33
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Lift
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFamily
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.Milestones.AT_alternating_automorphism_permutation
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.RankThree.PartOne.CTP.StrongPClassification
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.RankThree.PartTwo.Sec4.T444.Statement
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.StronglyEmbedded.BenderNormalSeries
import Certificates.Certificate2326
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {e : ℕ}

omit [Finite K] [Finite Y] in
private theorem leviM_singleton_eq_rankOne (i : Fin D.rank) :
    leviM D {i} = rankOne D.rootGroup i := by
  simp [leviM]

omit [Finite K] [Finite Y] in
private theorem BorelQuotient.ker_le_borel (h : BorelQuotient D n H π e) :
    π.ker ≤ borel D H := fun z hz =>
  CFSG.LieType.TitsSimplicity.center_le_borel h.ct h.extras (h.ker_central z hz)

omit [Finite K] [Finite Y] in
private theorem rankOne_inf_borel_dich (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {A : Subgroup K} (hBA : borel D H ⊓ rankOne D.rootGroup i ≤ A)
    (hAL : A ≤ rankOne D.rootGroup i) :
    A ≤ borel D H ∨ A = rankOne D.rootGroup i := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hAB, hAL'⟩ := hcon
  obtain ⟨g, hgA, hgB⟩ := Set.not_subset.1 hAB
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  rcases h.extras.rankOne_bruhat i g (hAL hgA) with
    ⟨hh, hhh, u, hu, rfl⟩ | ⟨u, hu, hh, hhh, v, hv, rfl⟩
  · exact hgB (mul_mem (iSup_le_borel (le_iSup H i hhh))
      (rootGroup_le_borel hα (ht_single_pos i) hu))
  · have huA : u ∈ A := hBA (Subgroup.mem_inf.mpr
      ⟨rootGroup_le_borel hα (ht_single_pos i) hu, Subgroup.mem_sup_left hu⟩)
    have hvA : v ∈ A := hBA (Subgroup.mem_inf.mpr
      ⟨rootGroup_le_borel hα (ht_single_pos i) hv, Subgroup.mem_sup_left hv⟩)
    have hhA : hh ∈ A := hBA (Subgroup.mem_inf.mpr
      ⟨iSup_le_borel (le_iSup H i hhh), h.ct.H_le i hhh⟩)
    have hnA : n i ∈ A := by
      have h1 : u⁻¹ * (u * n i * hh * v) * v⁻¹ * hh⁻¹ = n i := by group
      rw [← h1]
      exact mul_mem (mul_mem (mul_mem (inv_mem huA) hgA) (inv_mem hvA)) (inv_mem hhA)
    have hXa : D.rootGroup (Pi.single i 1) ≤ A := fun x hx => hBA (Subgroup.mem_inf.mpr
      ⟨rootGroup_le_borel hα (ht_single_pos i) hx, Subgroup.mem_sup_left hx⟩)
    have hneg : D.rootGroup (-Pi.single i 1) ≤ A := by
      intro y hy
      have hx := h.ct.conj_mem i (-Pi.single i 1) hα' y hy
      have hx' : n i * y * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
        have h2 : weylAction D.isFiniteType
            ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) (-Pi.single i 1) =
            Pi.single i 1 := by
          rw [map_neg, weylAction_simple_single, neg_neg]
        rwa [h2] at hx
      have e : y = (n i)⁻¹ * (n i * y * (n i)⁻¹) * n i := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hnA) (hXa hx')) hnA
    exact hAL' (le_antisymm hAL (sup_le hXa hneg))

omit [Finite K] [Finite Y] in
private theorem map_inf_map_leviM_singleton_dich (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {C : Subgroup Y} (hBC : (borel D H).map π ⊓ (leviM D {i}).map π ≤ C)
    (hCL : C ≤ (leviM D {i}).map π) :
    C = (borel D H).map π ⊓ (leviM D {i}).map π ∨ C = (leviM D {i}).map π := by
  rw [leviM_singleton_eq_rankOne] at hBC hCL ⊢
  set A : Subgroup K := C.comap π ⊓ rankOne D.rootGroup i with hA
  have hAL : A ≤ rankOne D.rootGroup i := inf_le_right
  have hBA : borel D H ⊓ rankOne D.rootGroup i ≤ A := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨?_, hb.2⟩
    rw [Subgroup.mem_comap]
    exact hBC (Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem π hb.1,
      Subgroup.mem_map_of_mem π hb.2⟩)
  have hmapA : A.map π = C := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_comap.mp ha.1
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp (hCL hy)
      exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_comap.mpr hy, hl⟩, rfl⟩
  rcases rankOne_inf_borel_dich h i hBA hAL with hAB | hAeq
  · left
    apply le_antisymm
    · rw [← hmapA]
      exact (Subgroup.map_mono (le_inf hAB inf_le_right)).trans
        (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right))
    · exact hBC
  · right
    rw [← hmapA, hAeq]

omit [Finite K] [Finite Y] in
theorem BorelQuotient.map_borel_inf_map_leviM_singleton_covBy (h : BorelQuotient D n H π e)
    (i : Fin D.rank) :
    (borel D H).map π ⊓ (leviM D {i}).map π ⋖ (leviM D {i}).map π := by
  have hlt : (borel D H).map π ⊓ (leviM D {i}).map π < (leviM D {i}).map π := by
    rw [lt_iff_le_and_ne]
    refine ⟨inf_le_right, fun heq => ?_⟩
    have hnot : ¬ (leviM D {i}).map π ≤ (borel D H).map π := by
      intro hle
      have hLnot : ¬ leviM D {i} ≤ borel D H := by
        rw [leviM_singleton_eq_rankOne]
        exact not_rankOne_le_borel h.ct h.extras i
      apply hLnot
      intro g hgL
      obtain ⟨b, hbB, hbπ⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem π hgL))
      have hz : g * b⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hbπ, mul_inv_cancel]
      have e : g = (g * b⁻¹) * b := by group
      rw [e]
      exact mul_mem (h.ker_le_borel hz) hbB
    exact hnot (heq ▸ inf_le_left)
  refine (covBy_iff_wcovBy_and_lt).2 ⟨?_, hlt⟩
  rw [wcovBy_iff_le_and_eq_or_eq]
  exact ⟨inf_le_right, fun c hc1 hc2 => map_inf_map_leviM_singleton_dich h i hc1 hc2⟩

omit [Finite K] [Finite Y] in
private theorem not_n_mem_borel (h : BorelQuotient D n H π e) (i : Fin D.rank) :
    n i ∉ borel D H := by
  intro hn
  rw [← nrep_simple h.ct i] at hn
  exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_ne_one i
    ((nrep_mem_borel_iff h.ct h.extras).1 hn)

omit [Finite K] [Finite Y] in
private theorem map_borel_inf_leviM_eq (h : BorelQuotient D n H π e) (i : Fin D.rank) :
    (borel D H).map π ⊓ (leviM D {i}).map π = (borel D H ⊓ leviM D {i}).map π := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hb, hl⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b, hbB, hbb⟩ := Subgroup.mem_map.mp hb
    obtain ⟨l, hlL, hll⟩ := Subgroup.mem_map.mp hl
    have hz : b * l⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbb, hll, mul_inv_cancel]
    have hlB : l ∈ borel D H := by
      have e : l = (b * l⁻¹)⁻¹ * b := by group
      rw [e]
      exact mul_mem (inv_mem (h.ker_le_borel hz)) hbB
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_inf.mpr ⟨hlB, hlL⟩, hll⟩
  · exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

omit [Finite K] [Finite Y] in
private theorem borel_inf_leviM_le_torus_sup_single (h : BorelQuotient D n H π e)
    (i : Fin D.rank) :
    borel D H ⊓ leviM D {i} ≤ (⨆ k, H k) ⊔ D.rootGroup (Pi.single i 1) := by
  intro g hg
  have hgB : g ∈ borel D H := hg.1
  have hgL : g ∈ rankOne D.rootGroup i := by
    rw [← leviM_singleton_eq_rankOne]; exact hg.2
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  rcases h.extras.rankOne_bruhat i g hgL with
    ⟨hh, hhh, u, hu, he⟩ | ⟨u, hu, hh, hhh, v, hv, he⟩
  · rw [he]
    exact mul_mem (Subgroup.mem_sup_left (le_iSup H i hhh)) (Subgroup.mem_sup_right hu)
  · exfalso
    apply not_n_mem_borel h i
    have huB : u ∈ borel D H := rootGroup_le_borel hα (ht_single_pos i) hu
    have hvB : v ∈ borel D H := rootGroup_le_borel hα (ht_single_pos i) hv
    have hhB : hh ∈ borel D H := iSup_le_borel (le_iSup H i hhh)
    have e : n i = u⁻¹ * g * (hh * v)⁻¹ := by rw [he]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem huB) hgB) (inv_mem (mul_mem hhB hvB))

omit [Finite K] [Finite Y] in
private theorem map_borel_inf_leviM_le_normalizer_single (h : BorelQuotient D n H π e)
    (i : Fin D.rank) :
    (borel D H).map π ⊓ (leviM D {i}).map π ≤
      Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y) := by
  rw [map_borel_inf_leviM_eq h i]
  refine (Subgroup.map_mono (borel_inf_leviM_le_torus_sup_single h i)).trans ?_
  rw [Subgroup.map_sup]
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  exact sup_le ((Subgroup.map_mono (iSup_le_normalizer_rootGroup h.ct hα)).trans
    (Subgroup.le_normalizer_map π)) Subgroup.le_normalizer

omit [Finite K] [Finite Y] in
private theorem two_mem_map_unipJ' (h : BorelQuotient D n H π e) (J : Set (Fin D.rank))
    {a : Y} (ha : a ∈ (parJ D H J).map π) {k : ℕ} (hk : a ^ 2 ^ k = 1) :
    a ∈ (unipJ D J).map π := by
  rw [parJ_eq_sup, Subgroup.map_sup] at ha
  refine mem_of_pow_two_pow_eq_one_of_mem_sup (M := e) ?_ h.odd ?_ ha hk
  · exact (Subgroup.map_mono (torus_le_normalizer_unipJ h.ct J)).trans
      (Subgroup.le_normalizer_map π)
  · rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, CFSG.ClassicalInvolution.WeakCT.pow_eq_one_of_mem_torus h.extras h.torus_pow ht,
      map_one]

omit [Finite K] [Finite Y] in
private theorem eq_one_of_mem_map_posUnipotent_of_mem_H (h : BorelQuotient D n H π e)
    (i : Fin D.rank) {hh : K} (hhh : hh ∈ H i)
    (hmem : π hh ∈ (posUnipotent D).map π) : π hh = 1 := by
  have hU2 : IsPGroup 2 ((posUnipotent D).map π) := (isPGroup_iSup_pos h.extras h.pGroup).map π
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hU2) ⟨π hh, hmem⟩
  have hdvd : orderOf (π hh) ∣ e := dvd_trans (orderOf_map_dvd π hh)
    (orderOf_dvd_of_pow_eq_one (h.torus_pow i hh hhh))
  have hord : orderOf (π hh) = orderOf (⟨π hh, hmem⟩ : ↥((posUnipotent D).map π)) :=
    Subgroup.orderOf_coe ⟨π hh, hmem⟩
  have hj' : orderOf (π hh) ∣ 2 ^ j := by rw [hord, hj]
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left j (Nat.coprime_two_left.2 h.odd)) hj' hdvd)

omit [Finite K] [Finite Y] in
private theorem mem_map_rootGroup_of_mem_inf_borel (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {a : Y} (haB : a ∈ (borel D H).map π) (haL : a ∈ (leviM D {i}).map π)
    {k : ℕ} (h2 : a ^ 2 ^ k = 1) : a ∈ (D.rootGroup (Pi.single i 1)).map π := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have haU : a ∈ (posUnipotent D).map π := by
    have hpar : parJ D H (∅ : Set (Fin D.rank)) = borel D H := by simp [parJ]
    have haB' : a ∈ (parJ D H (∅ : Set (Fin D.rank))).map π := by rw [hpar]; exact haB
    have h1 := two_mem_map_unipJ' (D := D) (n := n) (H := H) (π := π) (e := e) h
      (∅ : Set (Fin D.rank)) haB' (k := k) h2
    simpa [unipJ] using h1
  obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp haU
  obtain ⟨l, hl, hla⟩ := Subgroup.mem_map.mp haL
  rw [leviM_singleton_eq_rankOne] at hl
  have hz : u * l⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hua, hla, mul_inv_cancel]
  rcases h.extras.rankOne_bruhat i l hl with
    ⟨hh, hhh, u', hu', he⟩ | ⟨u', hu', hh, hhh, v, hv, he⟩
  · have haeq : a = π hh * π u' := by rw [← hla, he, map_mul]
    have hmemU : π hh ∈ (posUnipotent D).map π := by
      have hu'U : π u' ∈ (posUnipotent D).map π :=
        Subgroup.mem_map_of_mem π (rootGroup_le_posUnipotent hα (ht_single_pos i) hu')
      have heq : π hh = a * (π u')⁻¹ := by rw [haeq]; group
      rw [heq]
      exact mul_mem haU (inv_mem hu'U)
    have hh1 := eq_one_of_mem_map_posUnipotent_of_mem_H h i hhh hmemU
    refine Subgroup.mem_map.mpr ⟨u', hu', ?_⟩
    rw [haeq, hh1, one_mul]
  · exfalso
    have haeq : a = π u' * π (n i) * π hh * π v := by
      rw [← hla, he, map_mul, map_mul, map_mul]
    have hu'B : π u' ∈ (borel D H).map π := Subgroup.mem_map_of_mem π
      (rootGroup_le_borel hα (ht_single_pos i) hu')
    have hvB : π v ∈ (borel D H).map π := Subgroup.mem_map_of_mem π
      (rootGroup_le_borel hα (ht_single_pos i) hv)
    have hhB : π hh ∈ (borel D H).map π := Subgroup.mem_map_of_mem π
      (iSup_le_borel (le_iSup H i hhh))
    have hnB : π (n i) ∈ (borel D H).map π := by
      have heq : π (n i) = (π u')⁻¹ * a * (π hh * π v)⁻¹ := by rw [haeq]; group
      rw [heq]
      exact mul_mem (mul_mem (inv_mem hu'B) haB) (inv_mem (mul_mem hhB hvB))
    obtain ⟨b, hb, hbn⟩ := Subgroup.mem_map.mp hnB
    apply not_n_mem_borel h i
    have hzb : b⁻¹ * n i ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbn, inv_mul_cancel]
    have e : n i = b * (b⁻¹ * n i) := by group
    rw [e]
    exact mul_mem hb (h.ker_le_borel hzb)

omit [Finite K] [Finite Y] in
private theorem map_single_inf_map_neg_eq_bot (h : BorelQuotient D n H π e) (i : Fin D.rank) :
    (D.rootGroup (Pi.single i 1)).map π ⊓ (D.rootGroup (-Pi.single i 1)).map π = ⊥ := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha1
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha2
  have hz : x * y⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxa, hya, mul_inv_cancel]
  have hzcen := h.ker_central _ hz
  have hcomm : x * y = y * x := by
    have hc : y * (x * y⁻¹) = (x * y⁻¹) * y := (Subgroup.mem_center_iff.1 hzcen) y
    calc x * y = ((x * y⁻¹) * y) * y := by group
      _ = (y * (x * y⁻¹)) * y := by rw [← hc]
      _ = y * x := by group
  obtain ⟨r, hr⟩ := h.pGroup _ hα' ⟨y, hy⟩
  obtain ⟨s, hs⟩ := h.pGroup _ hα ⟨x, hx⟩
  have hy2 : y ^ 2 ^ r = 1 := by simpa using congrArg Subtype.val hr
  have hx2 : x ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
  have hcyx : Commute y x := Commute.symm (show Commute x y from hcomm)
  have hz' : x * y⁻¹ = y⁻¹ * x := (Commute.inv_left hcyx).eq.symm
  have hz1 : x * y⁻¹ = 1 := eq_one_of_central_odd h.odd (h.ker_pow _ hz)
    hz' (Commute.symm (show Commute x y from hcomm)) hy2 hx2
  have hxy : x = y := mul_inv_eq_one.1 hz1
  have hxinf : x ∈ D.rootGroup (Pi.single i 1) ⊓ D.rootGroup (-Pi.single i 1) :=
    Subgroup.mem_inf.mpr ⟨hx, hxy ▸ hy⟩
  have hpos : 0 < ht (Pi.single i 1 : Fin D.rank → ℤ) := ht_single_pos i
  have hneg : ht (-Pi.single i 1 : Fin D.rank → ℤ) < 0 := by rw [ht_neg]; omega
  have hbot : D.rootGroup (Pi.single i 1) ⊓ D.rootGroup (-Pi.single i 1) = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (le_inf (inf_le_left.trans (rootGroup_le_posUnipotent hα hpos))
      (inf_le_right.trans (rootGroup_le_negUnipotent hα' hneg))).trans
      (le_of_eq (posUnipotent_inf_negUnipotent h.extras))
  have hx1 : x = 1 := by
    have := (le_of_eq hbot) hxinf
    rwa [Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, ← hxa, hx1, map_one]

private theorem mem_normalizer_of_subgroupOf {G : Type*} [Group G] {A C : Subgroup G}
    (hAC : A ≤ C) {y : C}
    (hy : y ∈ Subgroup.normalizer ((A.subgroupOf C : Subgroup C) : Set C)) :
    (y : G) ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp hy ⟨x, hAC hx⟩).mp
      (show (⟨x, hAC hx⟩ : C) ∈ A.subgroupOf C from hx)
  · intro hx
    have hxC : x ∈ C := by
      have e : x = (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * y := by group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem y.2) (hAC hx)) y.2
    exact (Subgroup.mem_normalizer_iff.mp hy ⟨x, hxC⟩).mpr hx

private theorem lt_inf_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {R Q : Subgroup G} (hQ : IsPGroup p Q) (hRQ : R ≤ Q) (hne : R ≠ Q) :
    R < Q ⊓ Subgroup.normalizer (R : Set G) := by
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q) (h := hQ.isNilpotent)
  have hlt : R.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hRQ ?_)
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ R.subgroupOf Q := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt (hnc (R.subgroupOf Q) hlt)
  refine lt_iff_le_and_ne.mpr ⟨le_inf hRQ Subgroup.le_normalizer, fun h => ?_⟩
  have hx' : (x : G) ∈ R := by
    have : (x : G) ∈ Q ⊓ Subgroup.normalizer (R : Set G) :=
      ⟨x.2, mem_normalizer_of_subgroupOf hRQ hxN⟩
    rwa [← h] at this
  exact hxR (Subgroup.mem_subgroupOf.mpr hx')


omit [Finite K] [Finite Y] in
private theorem sup_bi_eq_of_not_le (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) {q : Subgroup Y} (hq_le : q ≤ L')
    (hnot : ¬ q ≤ (borel D H).map π ⊓ (leviM D {i}).map π) :
    q ⊔ ((borel D H).map π ⊓ (leviM D {i}).map π) = L' := by
  have hcov : ((borel D H).map π ⊓ (leviM D {i}).map π) ⋖ L' := by
    rw [hL']; exact BorelQuotient.map_borel_inf_map_leviM_singleton_covBy h i
  have hw := (covBy_iff_wcovBy_and_lt.1 hcov).1
  rcases (wcovBy_iff_le_and_eq_or_eq.1 hw).2
    (q ⊔ ((borel D H).map π ⊓ (leviM D {i}).map π)) le_sup_right
    (sup_le hq_le (inf_le_right.trans (le_of_eq hL'.symm))) with hh | hh
  · exact absurd (le_sup_left.trans (le_of_eq hh)) hnot
  · exact hh

omit [Finite K] [Finite Y] in
private theorem map_neg_le_sup_of_not_le (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) {q : Subgroup Y} (hq_le : q ≤ L')
    (hqN : L' ≤ Subgroup.normalizer (q : Set Y))
    (hnot : ¬ q ≤ (borel D H).map π ⊓ (leviM D {i}).map π) :
    (D.rootGroup (-Pi.single i 1)).map π ≤ q ⊔ (D.rootGroup (Pi.single i 1)).map π := by
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
  have hEq := sup_bi_eq_of_not_le h i hL' hq_le hnot
  have hBiN : ((borel D H).map π ⊓ (leviM D {i}).map π) ≤
      Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y) :=
    map_borel_inf_leviM_le_normalizer_single h i
  have hBiNq : ((borel D H).map π ⊓ (leviM D {i}).map π) ≤
      Subgroup.normalizer (q : Set Y) := (inf_le_right.trans (le_of_eq hL'.symm)).trans hqN
  have hBiNQ : ((borel D H).map π ⊓ (leviM D {i}).map π) ≤
      Subgroup.normalizer (q ⊔ (D.rootGroup (Pi.single i 1)).map π : Subgroup Y) :=
    le_normalizer_sup hBiNq hBiN
  have hqNQ : q ≤ Subgroup.normalizer (q ⊔ (D.rootGroup (Pi.single i 1)).map π : Subgroup Y) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hL'NQ : L' ≤ Subgroup.normalizer
      (q ⊔ (D.rootGroup (Pi.single i 1)).map π : Subgroup Y) := by
    rw [← hEq]; exact sup_le hqNQ hBiNQ
  have hn'L : π (n i) ∈ q ⊔ ((borel D H).map π ⊓ (leviM D {i}).map π) := by
    rw [hEq, hL']
    exact Subgroup.mem_map_of_mem π (rankOne_le_leviM (Set.mem_singleton i) (h.ct.n_mem i))
  obtain ⟨q₀, hq₀, b, hb, hn'eq⟩ : ∃ q₀ ∈ q, ∃ b ∈
      ((borel D H).map π ⊓ (leviM D {i}).map π), q₀ * b = π (n i) := by
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left q _ hBiNq,
      Set.mem_mul] at hn'L
    exact hn'L
  have hq₀bN : q₀ * b ∈ Subgroup.normalizer
      (q ⊔ (D.rootGroup (Pi.single i 1)).map π : Subgroup Y) :=
    hL'NQ (hn'eq.symm ▸ (hEq ▸ hn'L))
  intro z hz
  obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp hz
  have hx : n i * y * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
    have h1 := h.ct.conj_mem i (-Pi.single i 1) hα' y hy
    have h2 : weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) (-Pi.single i 1) =
        Pi.single i 1 := by rw [map_neg, weylAction_simple_single, neg_neg]
    rwa [h2] at h1
  have hz' : z = (q₀ * b)⁻¹ * π (n i * y * (n i)⁻¹) * (q₀ * b) := by
    rw [← hzy, hn'eq, map_mul, map_mul, map_inv]
    group
  rw [hz']
  have hmem := (Subgroup.mem_normalizer_iff.1 (inv_mem hq₀bN) (π (n i * y * (n i)⁻¹))).1
    (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem π hx))
  simpa using hmem

omit [Finite K] [Finite Y] in
private theorem isPGroup_of_not_le (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) {q : Subgroup Y} (hq_le : q ≤ L')
    (hqN : L' ≤ Subgroup.normalizer (q : Set Y)) (hq_2 : IsPGroup 2 q)
    (hnot : ¬ q ≤ (borel D H).map π ⊓ (leviM D {i}).map π) : IsPGroup 2 L' := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hXb_le := map_neg_le_sup_of_not_le h i hL' hq_le hqN hnot
  have hXa_le : (D.rootGroup (Pi.single i 1)).map π ≤ L' := by
    rw [hL', leviM_singleton_eq_rankOne]; exact Subgroup.map_mono le_sup_left
  have hXa_2 : IsPGroup 2 ((D.rootGroup (Pi.single i 1)).map π) := (h.pGroup _ hα).map π
  have hQX2 : IsPGroup 2 (q ⊔ (D.rootGroup (Pi.single i 1)).map π : Subgroup Y) :=
    IsPGroup.to_sup_of_normal_left' hq_2 hXa_2 (hXa_le.trans hqN)
  have hgoal : L' = (D.rootGroup (Pi.single i 1)).map π ⊔
      (D.rootGroup (-Pi.single i 1)).map π := by
    rw [hL', leviM_singleton_eq_rankOne]
    change (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map π = _
    rw [Subgroup.map_sup]
  rw [hgoal]
  exact hQX2.to_le (sup_le le_sup_right hXb_le)

omit [Finite K] [Finite Y] in
private theorem bi_eq_map_single_of_isPGroup (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) (hL'2 : IsPGroup 2 L') :
    (borel D H).map π ⊓ (leviM D {i}).map π = (D.rootGroup (Pi.single i 1)).map π := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hBi_leL : (borel D H).map π ⊓ (leviM D {i}).map π ≤ L' :=
    inf_le_right.trans (le_of_eq hL'.symm)
  apply le_antisymm
  · intro a ha
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hL'2) ⟨a, hBi_leL ha⟩
    have hk' : a ^ 2 ^ k = 1 := by
      have hcoe : orderOf a = orderOf (⟨a, hBi_leL ha⟩ : ↥L') :=
        Subgroup.orderOf_coe (⟨a, hBi_leL ha⟩ : ↥L')
      have h1 : a ^ orderOf a = 1 := pow_orderOf_eq_one a
      rwa [hcoe, hk] at h1
    exact mem_map_rootGroup_of_mem_inf_borel h i ha.1 ha.2 hk'
  · have hXa_le : (D.rootGroup (Pi.single i 1)).map π ≤ L' := by
      rw [hL', leviM_singleton_eq_rankOne]
      exact Subgroup.map_mono le_sup_left
    exact le_inf (Subgroup.map_mono (rootGroup_le_borel hα (ht_single_pos i)))
      (hXa_le.trans (le_of_eq hL'))

omit [Finite K] [Finite Y] in
private theorem false_of_le_normalizer_map_single (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) (hL'2 : IsPGroup 2 L')
    {q : Subgroup Y} (hq_le : q ≤ L')
    (hnot : ¬ q ≤ (borel D H).map π ⊓ (leviM D {i}).map π)
    (hnorm : L' ≤ Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y)) : False := by
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ ((RootSystem.ofCartan
      D.isFiniteType D.divisible).single_mem i)
  have hBi_eq_Xa := bi_eq_map_single_of_isPGroup h i hL' hL'2
  have hEq := sup_bi_eq_of_not_le h i hL' hq_le hnot
  have hn'L : π (n i) ∈ q ⊔ ((borel D H).map π ⊓ (leviM D {i}).map π) := by
    rw [hEq, hL']
    exact Subgroup.mem_map_of_mem π (rankOne_le_leviM (Set.mem_singleton i) (h.ct.n_mem i))
  have hn'L' : π (n i) ∈ L' := hEq ▸ hn'L
  have hXb_le_Xa : (D.rootGroup (-Pi.single i 1)).map π ≤
      (D.rootGroup (Pi.single i 1)).map π := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp hz
    have hx : n i * y * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
      have h1 := h.ct.conj_mem i (-Pi.single i 1) hα' y hy
      have h2 : weylAction D.isFiniteType
          ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) (-Pi.single i 1) =
          Pi.single i 1 := by rw [map_neg, weylAction_simple_single, neg_neg]
      rwa [h2] at h1
    have hz' : z = (π (n i))⁻¹ * π (n i * y * (n i)⁻¹) * π (n i) := by
      rw [← hzy, map_mul, map_mul, map_inv]
      group
    rw [hz']
    have hmem := (Subgroup.mem_normalizer_iff.1 (hnorm (L'.inv_mem hn'L'))
      (π (n i * y * (n i)⁻¹))).1 (Subgroup.mem_map_of_mem π hx)
    simpa using hmem
  have hXa_le' : (D.rootGroup (Pi.single i 1)).map π ≤ L' := by
    rw [hL', leviM_singleton_eq_rankOne]; exact Subgroup.map_mono le_sup_left
  have hL'Xa : L' = (D.rootGroup (Pi.single i 1)).map π := by
    refine le_antisymm ?_ hXa_le'
    have hgoal : L' = (D.rootGroup (Pi.single i 1)).map π ⊔
        (D.rootGroup (-Pi.single i 1)).map π := by
      rw [hL', leviM_singleton_eq_rankOne]
      change (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map π = _
      rw [Subgroup.map_sup]
    rw [hgoal]
    exact sup_le le_rfl hXb_le_Xa
  have hBiL' : ((borel D H).map π ⊓ (leviM D {i}).map π) = L' := by rw [hBi_eq_Xa, hL'Xa]
  exact hnot (hBiL' ▸ hq_le)

omit [Finite K] [Finite Y] in
private theorem normalizer_inf_eq_bi_of_isPGroup (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) (hL'2 : IsPGroup 2 L')
    {q : Subgroup Y} (hq_le : q ≤ L')
    (hnot : ¬ q ≤ (borel D H).map π ⊓ (leviM D {i}).map π) :
    L' ⊓ Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y) =
      ((borel D H).map π ⊓ (leviM D {i}).map π) := by
  have hBiN : ((borel D H).map π ⊓ (leviM D {i}).map π) ≤
      Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y) :=
    map_borel_inf_leviM_le_normalizer_single h i
  have hBi_leL : (borel D H).map π ⊓ (leviM D {i}).map π ≤ L' :=
    inf_le_right.trans (le_of_eq hL'.symm)
  have hle1 : ((borel D H).map π ⊓ (leviM D {i}).map π) ≤
      L' ⊓ Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y) :=
    le_inf hBi_leL hBiN
  have hle2 : L' ⊓ Subgroup.normalizer ((D.rootGroup (Pi.single i 1)).map π : Set Y) ≤ L' :=
    inf_le_left
  have hcov : ((borel D H).map π ⊓ (leviM D {i}).map π) ⋖ L' := by
    rw [hL']; exact BorelQuotient.map_borel_inf_map_leviM_singleton_covBy h i
  have hw := (covBy_iff_wcovBy_and_lt.1 hcov).1
  rcases (wcovBy_iff_le_and_eq_or_eq.1 hw).2 _ hle1 hle2 with hh | hh
  · exact hh
  · exact (false_of_le_normalizer_map_single h i hL' hL'2 hq_le hnot
      (hh ▸ inf_le_right)).elim

omit [Finite K] in
private theorem self_normalizing_false (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π) {q : Subgroup Y} (hq_le : q ≤ L')
    (hqN : L' ≤ Subgroup.normalizer (q : Set Y)) (hq_2 : IsPGroup 2 q)
    (hnot : ¬ q ≤ (borel D H).map π ⊓ (leviM D {i}).map π) : False := by
  have hL'2 := isPGroup_of_not_le h i hL' hq_le hqN hq_2 hnot
  have hBi_eq_Xa := bi_eq_map_single_of_isPGroup h i hL' hL'2
  have hN_eq_Bi := normalizer_inf_eq_bi_of_isPGroup h i hL' hL'2 hq_le hnot
  have hXa_le : (D.rootGroup (Pi.single i 1)).map π ≤ L' := by
    rw [hL', leviM_singleton_eq_rankOne]; exact Subgroup.map_mono le_sup_left
  have hne : (D.rootGroup (Pi.single i 1)).map π ≠ L' := by
    intro heq
    exact hnot (by rw [hBi_eq_Xa, heq]; exact hq_le)
  have hlt := lt_inf_normalizer hL'2 hXa_le hne
  rw [hN_eq_Bi, hBi_eq_Xa] at hlt
  exact absurd hlt (lt_irrefl _)

omit [Finite K] [Finite Y] in
private theorem eq_bot_of_le_inf (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π)
    {Q : Subgroup ↥L'} (hQn : Q.Normal) (hQp : IsPGroup 2 Q)
    (hle : Q.map (Subgroup.subtype L') ≤ (borel D H).map π ⊓ (leviM D {i}).map π) :
    Q = ⊥ := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hq_le : Q.map (Subgroup.subtype L') ≤ L' := Subgroup.map_subtype_le Q
  have hq_2 : IsPGroup 2 (Q.map (Subgroup.subtype L')) := hQp.map (Subgroup.subtype L')
  have hqN : L' ≤ Subgroup.normalizer (Q.map (Subgroup.subtype L') : Set Y) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hq_le).mp ?_
    have hsub : (Q.map (Subgroup.subtype L')).subgroupOf L' = Q := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨fun ⟨z, hz, hzx⟩ => (Subtype.ext hzx) ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
    rw [hsub]; exact hQn
  have hqXa : Q.map (Subgroup.subtype L') ≤ (D.rootGroup (Pi.single i 1)).map π := by
    intro a ha
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hq_2) ⟨a, ha⟩
    have hk' : a ^ 2 ^ k = 1 := by
      have hcoe : orderOf a = orderOf (⟨a, ha⟩ : ↥(Q.map (Subgroup.subtype L'))) :=
        Subgroup.orderOf_coe (⟨a, ha⟩ : ↥(Q.map (Subgroup.subtype L')))
      have h1 : a ^ orderOf a = 1 := pow_orderOf_eq_one a
      rwa [hcoe, hk] at h1
    exact mem_map_rootGroup_of_mem_inf_borel h i (hle ha).1 (hle ha).2 hk'
  have hqXb : Q.map (Subgroup.subtype L') ≤ (D.rootGroup (-Pi.single i 1)).map π := by
    intro a ha
    have hn'L : π (n i) ∈ L' := by
      rw [hL']
      exact Subgroup.mem_map_of_mem π (rankOne_le_leviM (Set.mem_singleton i) (h.ct.n_mem i))
    have h1 : (π (n i))⁻¹ * a * π (n i) ∈ Q.map (Subgroup.subtype L') := by
      have hmem := (Subgroup.mem_normalizer_iff.1 (hqN (L'.inv_mem hn'L)) a).1 ha
      simpa using hmem
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp (hqXa h1)
    refine Subgroup.mem_map.mpr ⟨n i * x * (n i)⁻¹, ?_, ?_⟩
    · have hc := h.ct.conj_mem i (Pi.single i 1) hα x hx
      rwa [weylAction_simple_single D.isFiniteType i] at hc
    · have hxπ' : π (n i) * π x * (π (n i))⁻¹ = a := by rw [hxπ]; group
      calc π (n i * x * (n i)⁻¹) = π (n i) * π x * (π (n i))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = a := hxπ'
  rw [eq_bot_iff]
  intro x hx
  have hxq : (x : Y) ∈ Q.map (Subgroup.subtype L') := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have h1 : (x : Y) ∈ (D.rootGroup (Pi.single i 1)).map π ⊓
      (D.rootGroup (-Pi.single i 1)).map π := Subgroup.mem_inf.mpr ⟨hqXa hxq, hqXb hxq⟩
  rw [map_single_inf_map_neg_eq_bot h i, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

omit [Finite K] in
private theorem normal_isPGroup_eq_bot (h : BorelQuotient D n H π e) (i : Fin D.rank)
    {L' : Subgroup Y} (hL' : L' = (leviM D {i}).map π)
    {Q : Subgroup ↥L'} (hQn : Q.Normal) (hQp : IsPGroup 2 Q) : Q = ⊥ := by
  have hq_le : Q.map (Subgroup.subtype L') ≤ L' := Subgroup.map_subtype_le Q
  have hq_2 : IsPGroup 2 (Q.map (Subgroup.subtype L')) := hQp.map (Subgroup.subtype L')
  have hqN : L' ≤ Subgroup.normalizer (Q.map (Subgroup.subtype L') : Set Y) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hq_le).mp ?_
    have hsub : (Q.map (Subgroup.subtype L')).subgroupOf L' = Q := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨fun ⟨z, hz, hzx⟩ => (Subtype.ext hzx) ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
    rw [hsub]; exact hQn
  by_cases hle : Q.map (Subgroup.subtype L') ≤ (borel D H).map π ⊓ (leviM D {i}).map π
  · exact eq_bot_of_le_inf h i hL' hQn hQp hle
  · exact (self_normalizing_false h i hL' hq_le hqN hq_2 hle).elim

omit [Finite K] in
theorem BorelQuotient.pCore_map_leviM_singleton_eq_bot (h : BorelQuotient D n H π e)
    (i : Fin D.rank) : CFSG.pCore 2 ↥((leviM D {i}).map π) = ⊥ :=
  normal_isPGroup_eq_bot h i rfl (CFSG.pCore_normal (p := 2) (G := ↥((leviM D {i}).map π)))
    (CFSG.pCore_isPGroup (p := 2) (G := ↥((leviM D {i}).map π)))

end CFSG.AGLEmbedding.ParabHub
