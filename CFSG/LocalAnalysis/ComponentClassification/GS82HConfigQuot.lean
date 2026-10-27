module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCore
public import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.C3.Layer1.BackStmt
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigOrbit
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.ComponentClassification.GSThmB.HConfig

open CFSG Subgroup
open scoped commutatorElement

abbrev Bar (H : Type) [Group H] : Type := H ⧸ pPrimeCore 2 H

abbrev bar (H : Type) [Group H] : H →* Bar H := QuotientGroup.mk' (pPrimeCore 2 H)

variable {H : Type} [Group H] [Finite H]

theorem odd_card_ker_bar : Odd (Nat.card (bar H).ker) := by
  rw [QuotientGroup.ker_mk']
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem not_two_dvd_card_ker_bar : ¬ 2 ∣ Nat.card (bar H).ker := fun h =>
  (Nat.not_even_iff_odd.mpr odd_card_ker_bar) (even_iff_two_dvd.mpr h)

theorem card_ker_subgroupMap_dvd {Y : Type*} [Group Y] (f : H →* Y) (L : Subgroup H) :
    Nat.card (f.subgroupMap L).ker ∣ Nat.card f.ker := by
  have h1 : ((f.subgroupMap L).ker).map L.subtype ≤ f.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
  rw [← Subgroup.card_map_of_injective L.subtype_injective]
  exact Subgroup.card_dvd_of_le h1

theorem nonempty_quot_equiv_map {Y : Type} [Group Y] [Finite Y] (f : H →* Y)
    (hodd : Odd (Nat.card f.ker)) (L : Subgroup H) :
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* ↥(L.map f) ⧸ pPrimeCore 2 ↥(L.map f)) :=
  OddQuot.nonempty_pPrimeCore_equiv_of_surjective (f.subgroupMap L) (f.subgroupMap_surjective L)
    fun h => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (h.trans (card_ker_subgroupMap_dvd f L)))

theorem isTwoQuasisimple_map {Y : Type} [Group Y] [Finite Y] (f : H →* Y)
    (hodd : Odd (Nat.card f.ker)) {L : Subgroup H} (hL : HarrisLit.IsTwoQuasisimple ↥L) :
    HarrisLit.IsTwoQuasisimple ↥(L.map f) := by
  haveI := hL.1
  obtain ⟨e⟩ := nonempty_quot_equiv_map f hodd L
  exact ⟨Group.IsPerfect.map f, LocalCores.isQuasisimple_of_mulEquiv e hL.2⟩

theorem map_comap_inf {Y : Type*} [Group Y] (f : H →* Y) (S : Subgroup Y) (A : Subgroup H) :
    (S.comap f ⊓ A).map f = S ⊓ A.map f := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxA⟩, rfl⟩
    exact ⟨hxS, x, hxA, rfl⟩
  · rintro ⟨hyS, x, hxA, rfl⟩
    exact ⟨x, ⟨hyS, hxA⟩, rfl⟩

theorem le_canonicalPrimeLift_of_isPerfect (Kb : Subgroup (Bar H)) {P : Subgroup H}
    (hP : Group.IsPerfect P) (hPM : P ≤ Kb.comap (bar H)) :
    P ≤ CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb := by
  refine (GH74.GLS.Th2.CaseI.le_closure_two_elements hP).trans (Subgroup.closure_mono ?_)
  rintro g ⟨hgP, n, hgn⟩
  refine ⟨hPM hgP, ?_⟩
  have h1 : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hgn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact ⟨k, hk⟩

theorem push_config {B N : Subgroup H} (hB : IsPGroup 2 B) (hNC : N ≤ centralizer (B : Set H))
    (hN : IsPComponent 2 (N.subgroupOf (centralizer (B : Set H)))) {t : H}
    (htZ : t ∈ center H) (htN : t ∈ N) (ht : orderOf t = 2) {q : ℕ}
    (hSL : HarrisLit.IsSLTwoOver q (↥N ⧸ pPrimeCore 2 ↥N)) :
    N.map (bar H) ≤ centralizer ((B.map (bar H) : Subgroup (Bar H)) : Set (Bar H)) ∧
      IsPComponent 2 ((N.map (bar H)).subgroupOf
        (centralizer ((B.map (bar H) : Subgroup (Bar H)) : Set (Bar H)))) ∧
      N.map (bar H) ≤ layer (Bar H) ∧ bar H t ∈ center (Bar H) ∧ bar H t ∈ N.map (bar H) ∧
      bar H t ≠ 1 ∧ bar H t * bar H t = 1 ∧
      HarrisLit.IsSLTwoOver q (↥(N.map (bar H)) ⧸ pPrimeCore 2 ↥(N.map (bar H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := bar H with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hcent : (centralizer (B : Set H)).map φ = centralizer ((B.map φ : Subgroup (Bar H)) :
      Set (Bar H)) := GrSLit.map_centralizer_eq_of_odd_ker φ hφs not_two_dvd_card_ker_bar hB
  have hNC' : N.map φ ≤ centralizer ((B.map φ : Subgroup (Bar H)) : Set (Bar H)) :=
    hcent ▸ map_mono hNC
  have hN' := (HarrisLit.isTwoComponentIn_iff hNC).mpr hN
  obtain ⟨-, hNsub, hNq⟩ := hN'
  refine ⟨hNC', ?_, ?_, ?_, ⟨t, htN, rfl⟩, ?_, ?_, ?_⟩
  ·
    refine (HarrisLit.isTwoComponentIn_iff hNC').mp ⟨hNC', ?_, isTwoQuasisimple_map φ
      odd_card_ker_bar hNq⟩
    set C := centralizer (B : Set H)
    set C' := centralizer ((B.map φ : Subgroup (Bar H)) : Set (Bar H))
    have hmem : ∀ x : ↥C, φ x ∈ C' := fun x => hcent ▸ ⟨x, x.2, rfl⟩
    let f' : ↥C →* ↥C' := (φ.comp C.subtype).codRestrict C' hmem
    have hf' : Function.Surjective f' := by
      rintro ⟨y, hy⟩
      rw [← hcent] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have heq : (N.subgroupOf C).map f' = (N.map φ).subgroupOf C' := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine mem_subgroupOf.mpr ⟨x, hx, ?_⟩
        exact congrArg Subtype.val hxy
      · intro h
        obtain ⟨x, hx, hxy⟩ := mem_subgroupOf.mp h
        exact ⟨⟨x, hNC hx⟩, hx, Subtype.ext hxy⟩
    rw [← heq]
    exact hNsub.map hf'
  ·
    have h1 : N ≤ pLayer H 2 := by
      have h2 := ClassicalInvolution.l2PrimeBalance H B hB
      have h3 : N.subgroupOf (centralizer (B : Set H)) ≤ pLayer (centralizer (B : Set H)) 2 :=
        le_sSup hN
      calc N = (N.subgroupOf (centralizer (B : Set H))).map (centralizer (B : Set H)).subtype :=
            (map_subgroupOf_eq_of_le hNC).symm
        _ ≤ _ := map_mono h3
        _ ≤ pLayer H 2 := h2
    calc N.map φ ≤ (pLayer H 2).map φ := map_mono h1
      _ = layer (Bar H) := LBalance.Quot.map_pLayer_eq_layer_quotient
  · rw [mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := hφs g
    rw [← map_mul, ← map_mul, (mem_center_iff.mp htZ h)]
  · intro h1
    have h2 : t ∈ pPrimeCore 2 H := (QuotientGroup.eq_one_iff t).mp h1
    have h3 : orderOf (⟨t, h2⟩ : ↥(pPrimeCore 2 H)) ∣ Nat.card ↥(pPrimeCore 2 H) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ht] at h3
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr h3)
  · rw [← map_mul]
    have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    rw [htt, map_one]
  · obtain ⟨F, hF, hFt, hFq, ⟨eA⟩⟩ := hSL
    obtain ⟨e⟩ := nonempty_quot_equiv_map φ odd_card_ker_bar N
    exact ⟨F, hF, hFt, hFq, ⟨e.symm.trans eA⟩⟩

end CFSG.ComponentClassification.GSThmB.HConfig
