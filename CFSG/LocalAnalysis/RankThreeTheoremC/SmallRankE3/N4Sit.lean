module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem n4_eq_top_of_isPGroup_quotient (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) (N : Subgroup M) [N.Normal] (hN : IsPGroup p (M ⧸ N)) :
    N = ⊤ := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  by_contra hNtop
  have hidx : 1 < N.index := by
    have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : N.index ≠ 1 := fun h => hNtop (Subgroup.index_eq_one.mp h)
    omega
  haveI hnt : Nontrivial (M ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp hidx
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  set P' : Sylow p M := P.subtype hPM with hP'
  have himg : (P' : Subgroup M).map π = ⊤ := by
    have h := (Sylow.mapSurjective hπ P').3 (hN.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hPcomm : (P' : Subgroup M) ≤ _root_.commutator M := by
    have h1 : (_root_.commutator M).map M.subtype = ⁅M, M⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    intro y hy
    have hyP : (y : G) ∈ (P : Subgroup G) := hy
    have := CFSG.LocalAnalysis.RankThreeTheoremC.sylow_le_commutator_of_gamma_two hS
      hsit.mem_sigmaA hsit.isCoreMaxLocal hsit.gamma_two_le hyP
    rw [← h1] at this
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp this
    exact (Subtype.ext hyy) ▸ hy'
  have hperfQ : _root_.commutator (M ⧸ N) = ⊤ := by
    have h2 : (_root_.commutator M).map π = _root_.commutator (M ⧸ N) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr hπ]
    rw [← h2, eq_top_iff, ← himg]
    exact Subgroup.map_mono hPcomm
  haveI : Group.IsPerfect (M ⧸ N) := Group.isPerfect_def.mpr hperfQ
  exact Group.IsPerfect.not_isNilpotent (M ⧸ N) hN.isNilpotent

theorem n4_plane63E3 (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) (hp5 : 5 ≤ p) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    ∃ (hPM : (P : Subgroup G) ≤ M) (hxM : x ∈ M) (hzM : z ∈ M),
      N3.Plane63E3 p ↥M (P.subtype hPM) ⟨x, hxM⟩ ⟨z, hzM⟩ := by
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  have hxM : x ∈ M := hPM hx.mem
  have hzM : z ∈ M := hPM hz.mem
  refine ⟨hPM, hxM, hzM, ?_⟩
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hne : M ≠ ⊤ := by
    intro h
    apply hx.not_centralizer_le
    rw [h]
    exact le_top
  refine ⟨hprime, hp5,
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hne, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.smallRankPlane_subgroupOf hPM hxM hzM
      (SmallRankPlane.of_situation hS hsit hx hz)
  · rw [mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (mem_centralizer_iff.mp hz.centralizes (h : G) hh)
  · change Open.pRank p ((P : Subgroup G).subgroupOf M) = 3
    rwa [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pRank_subgroupOf hprime.one_lt hPM]
  · calc Open.pRank p (centralizer ({(⟨x, hxM⟩ : M)} : Set M))
        = Open.pRank p ((centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map M.subtype) :=
          (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pRank_map_subtype hprime.one_lt _).symm
      _ ≤ Open.pRank p (centralizer ({x} : Set G)) := by
          refine CFSG.SectionRank.pRank_mono hprime.one_lt ?_
          rintro _ ⟨y, hy, rfl⟩
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      _ ≤ 2 := by
          by_contra h
          push Not at h
          exact hsit.largeObstruction_empty x
            ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩
  · have hB : (centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map M.subtype =
        M ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    have hA : ((P.subtype hPM : Subgroup M) ⊓ centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map
        M.subtype = (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', ⟨hy'P, hy'C⟩, rfl⟩
        exact ⟨hy'P, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'C))⟩
      · rintro ⟨hyP, hyC⟩
        exact ⟨⟨y, hPM hyP⟩, ⟨hyP, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
    have hG : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
        (centralizer ({x} : Set G)) :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr
        ⟨inf_le_right, (P.isPGroup').to_le inf_le_left, hx.sylow_centralizer⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M, hA, hB]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hG (inf_le_inf_right _ hPM) inf_le_right

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
