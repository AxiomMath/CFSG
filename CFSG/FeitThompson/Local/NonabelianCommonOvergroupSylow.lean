module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementAbelianNilpotent
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormalizer
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Local.PrimeFixedSectionExtension
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Definitions.MaximumElementaryAbelianPrimeRank
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem eq_of_isSylowSubgroupOf_of_normalizer_le [Finite G] {p : ℕ} (hp : p.Prime)
    {K R : Subgroup G} (hR : _root_.CFSG.FeitThompson.IsSylowIn p K R)
    (hN : normalizer (R : Set G) ≤ K) {Q : Subgroup G} (hQ : IsPGroup p Q) (hRQ : R ≤ Q) :
    Q = R := by
  have hfp := Fact.mk hp
  obtain ⟨S, hS⟩ := hR
  by_contra hne
  have hlt : R < Q := lt_of_le_of_ne hRQ (Ne.symm hne)
  have hX : R < Q ⊓ normalizer (R : Set G) := lt_inf_normalizer_of_isPGroup hp hQ hlt
  set X : Subgroup G := Q ⊓ normalizer (R : Set G) with hXdef
  have hXK : X ≤ K := inf_le_right.trans hN
  have hXp : IsPGroup p X := hQ.to_le inf_le_left
  have hXp' : IsPGroup p ↥(X.subgroupOf K) := hXp.of_equiv (subgroupOfEquivOfLe hXK).symm
  have hSX : (S : Subgroup ↥K) ≤ X.subgroupOf K := fun y hy => hX.le (hS ▸ ⟨y, hy, rfl⟩)
  have hXS : X.subgroupOf K = (S : Subgroup ↥K) := S.is_maximal' hXp' hSX
  have hXR : X = R := by rw [← hS, ← hXS, Subgroup.map_subgroupOf_eq_of_le hXK]
  exact absurd hXR hX.ne'

theorem FNI_nonabelian_common_overgroup_sylow
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_common_overgroup_sylow.{u} := by
  intro G _ _ hG p M T P hM hT hMT hp hPMT hPp hPna
  have hsimple := hG.isSimpleGroup
  have hfp := Fact.mk hp
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG08 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hPne : P ≠ ⊥ := by
    rintro rfl
    exact hPna (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hPne (Subgroup.card_eq_one.1 hn)
  have hpdvdG : p ∣ Nat.card G := (hn ▸ dvd_pow_self p hn0).trans P.card_subgroup_dvd_card
  have hpodd : Odd p := hp.odd_of_ne_two (by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hG.odd_natCard) (even_iff_two_dvd.2 hpdvdG))
  have key : ∀ K : Subgroup G, IsCoatom K → P ≤ K → p ∈ sigmaPrimes K := by
    intro K hK hPK
    by_contra hpσ
    have : Fintype G := Fintype.ofFinite G
    exact hPna ((FBG_sigma_complement_abelian_nilpotent h₁ h₂ G hG02 K hK).1 P hPK
      hPp.isNilpotent (isPiSubgroup_of_natCard_eq_pow hp hn hpσ))
  have hpM : p ∈ sigmaPrimes M := key M hM (hPMT.trans inf_le_left)
  have hpT : p ∈ sigmaPrimes T := key T hT (hPMT.trans inf_le_right)
  refine ⟨hpodd, ?_, hpM, hpT⟩
  obtain ⟨R, hRsyl, hPR⟩ := exists_isSylowSubgroupOf_ge_of_isPGroup hPMT hPp
  have hRp : IsPGroup p R := isPGroup_of_isSylowSubgroupOf hRsyl
  have hRMT : R ≤ M ⊓ T := hRsyl.le
  have hRM : R ≤ M := hRMT.trans inf_le_left
  have hRT : R ≤ T := hRMT.trans inf_le_right
  have hRna : ¬ IsMulCommutative R := by
    intro hcomm
    have := hcomm
    exact hPna (isMulCommutative_of_le hPR)
  have hRnc : ¬ IsCyclic R := fun hcyc => hRna (by have := hcyc; exact IsCyclic.isMulCommutative)
  have hNMT : normalizer (R : Set G) ≤ M ⊓ T :=
    le_inf (FTS_noncyclic_sigma_normalizer h₃ G hG08 M R p hM hpM hRM hRp hRnc)
      (FTS_noncyclic_sigma_normalizer h₃ G hG08 T R p hT hpT hRT hRp hRnc)
  have hfull : ∀ K : Subgroup G, R ≤ K → _root_.CFSG.FeitThompson.IsSylowIn p K R := by
    intro K hRK
    obtain ⟨Q, hQsyl, hRQ⟩ := exists_isSylowSubgroupOf_ge_of_isPGroup hRK hRp
    have hQR : Q = R := eq_of_isSylowSubgroupOf_of_normalizer_le hp hRsyl hNMT
      (isPGroup_of_isSylowSubgroupOf hQsyl) hRQ
    exact hQR ▸ hQsyl
  have hRG : _root_.CFSG.FeitThompson.IsSylowSubgroup p R := by
    obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
    exact ⟨Q, eq_of_isSylowSubgroupOf_of_normalizer_le hp hRsyl hNMT Q.isPGroup' hRQ⟩
  have hrank : elementaryAbelianPRank p R = 2 := by
    have h2 : 2 ≤ elementaryAbelianPRank p R :=
      two_le_elementaryAbelianPRank_of_not_isCyclic hp hpodd hRp hRnc
    have hle : elementaryAbelianPRank p R ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ maxElementaryAbelianPRank ↥R :=
        le_trans (by omega) (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp)
      have hRtop : R ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hRM))
      obtain ⟨N, -, huniq⟩ := existsUnique_isCoatom_ge_of_three_le_maxElementaryAbelianPRank
        hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hRtop h3
      exact hMT ((huniq M ⟨hM, hRM⟩).trans (huniq T ⟨hT, hRT⟩).symm)
    omega
  exact ⟨R, hRna, hPR, hRsyl, hfull M hRM, hfull T hRT, hRG, hNMT, hrank⟩

end

end CFSG.FeitThompson.Proofs
