module

public import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoKill

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

theorem isPerfect_of_simple_nonabelian {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : Group.IsPerfect L := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hL
    have h1 : (⊤ : Subgroup L) ≤ Subgroup.centralizer ((⊤ : Subgroup L) : Set L) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact hbot)
    exact hab (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top b)) a trivial)
  · exact htop

theorem center_eq_bot_of_simple_nonabelian' {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : Subgroup.center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with hbot | htop
  · exact hbot
  · exfalso
    obtain ⟨a, b, hab⟩ := hL
    have hb : b ∈ Subgroup.center L := htop ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

namespace D1SocleConfig

variable {G : Type} [Group G] [Finite G] {T : Type} [Group T] [Finite T] {p a b : ℕ}
  [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}

theorem not_le_of_nclIn_le_two (h : D1SocleConfig T p P M H R X) (hT : JStarTargetTwo p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') : ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨K, hKn, ⟨e⟩, hC, hXK⟩ := h.socle
  obtain ⟨Rbar, -, hred⟩ := h.ext.reducedNongeneration
  have : K.Normal := hKn
  have hle : K ≤ ((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [← h.map_nclIn_eq hT.toJStarTargetBase hTc hKn ⟨e⟩ hXK]
    exact Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩
  have : IsSimpleGroup T := hT.simple
  have : IsSimpleGroup K := e.isSimpleGroup
  have hKab : ∃ x y : K, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hT.nonabelian
    exact ⟨e.symm x, e.symm y, fun h' => hxy (by simpa using congrArg e h')⟩
  have : Group.IsPerfect K := isPerfect_of_simple_nonabelian hKab
  have hZ := center_eq_bot_of_simple_nonabelian' hKab
  let e' : K ⧸ Subgroup.center K ≃* T :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  exact false_of_le_of_normal_sup hred hle (normal_sup_of_outer K e' Rbar
    (by rw [hC]; exact bot_le) hT.outer_sylow_normal)

theorem competitorTwo (h : D1SocleConfig T p P M H R X) (hT : JStarTargetTwo p b T)
    (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T) (hβ : KFactBeta)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    D1SocleConfig T p P M H' R X ∧ nclIn H X ≤ nclIn H' X :=
  h.competitor_of_not_le hT.toJStarTargetBase hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'
    (h.not_le_of_nclIn_le_two hT hTc hJH')

end D1SocleConfig

theorem competitorsOn_socleConfigTwo {G : Type} [Group G] [Finite G] {T : Type} [Group T]
    [Finite T] {p a b : ℕ} [Fact p.Prime] {P : Sylow p G} {M R U : Subgroup G}
    (hT : JStarTargetTwo p b T) (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T)
    (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) : D1JCompetitorsOn (D1SocleConfig T p P M · R U) R U :=
  fun _ h _ hH' hJH' hRH' => h.competitorTwo hT hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'

end CFSG.AGLEmbedding
