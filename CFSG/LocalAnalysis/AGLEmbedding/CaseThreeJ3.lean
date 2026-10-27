module

public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section J3Assembly

variable {G : Type} [Group G] [Finite G]

theorem D1SocleConfig.toD1J3Config [Fact (Nat.Prime 3)] {T : Type} [Group T] {P : Sylow 3 G}
    {M H R U : Subgroup G} (h : D1SocleConfig T 3 P M H R U)
    (e : Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) : D1J3Config P M H R := by
  obtain ⟨K, hKn, ⟨eK⟩, hC, -⟩ := h.socle
  obtain ⟨e⟩ := e
  exact ⟨h.ext, h.glob, K, hKn, ⟨eK.trans e⟩, hC⟩

theorem false_of_j3_of_competitors (hD : StmtJ3Data) (hM : StmtJ3MSide)
    (hOR : KFactJ3OuterRank) (hT : StmtJ3Target) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) [Fact (Nat.Prime 3)] {P : Sylow 3 G}
    {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G) (hext : D1Extremal 3 P M H R)
    (hrbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥)
    (hZ : Subgroup.center K = ⊥)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (hJ : D1J3Config P M H R)
    (hcomp : (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
      D1JCompetitorsOn (D1SocleConfig (↥K) 3 P M · R R) R R) : False := by
  obtain ⟨e'⟩ := e
  have e₀ : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e'
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤ K := by
    have : Finite (MulAut K) := MulEquiv.finite_left
    have hOut : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
      have h2 := (hOR K ⟨e₀⟩).1
      intro hd
      have := Nat.le_of_dvd Nat.card_pos hd
      omega
    intro x hx
    rw [← hrbar] at hx
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem := mem_sup_centralizer_of_pow Nat.prime_three hOut hxk
    rwa [hC, sup_bot_eq] at hmem
  have hS0 : D1SocleConfig (↥K) 3 P M H R R :=
    ⟨hext, hglob, le_rfl, K, hKn, ⟨MulEquiv.refl _⟩, hC, (inf_eq_left.mpr hRK).symm⟩
  have hcompR : D1JCompetitorsOn (D1SocleConfig (↥K) 3 P M · R R) R R := hcomp e₀
  have hcompZ := competitorsOn_of_le (hT _ ⟨e₀⟩).simple hcompR
    (inf_le_left : centerOf R ≤ R) (hD hJ).surv.ne_bot
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig (↥K) 3 P M H' R R)
    (fun H' h' => (hD (h'.toD1J3Config ⟨e₀⟩)).surv) (hM (hD hJ)) hcompZ hS0

theorem d1CaseThreeJ3_of (hD : StmtJ3Data) (hM : StmtJ3MSide) (hOR : KFactJ3OuterRank)
    (hT : StmtJ3Target) (hTc : StmtJ3TargetCard) (hE : KFactJStarElimJ3) (hβ : KFactBeta)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) :
    D1CaseThreeJ3 := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq _ hcent _ hZ e
  exact false_of_j3_of_competitors hD hM hOR hT h84 hCGT hD2 hcfg.glob.toAGLGlobal hcfg.ext
    hcfg.rbar hK huniq (hcfg.centralizer_eq_bot hK huniq hcent hZ) hZ e
    (hcfg.d1J3Config hK huniq hcent hZ e) fun e₀ =>
      competitorsOn_socleConfig (hT _ ⟨e₀⟩) (hTc _ ⟨e₀⟩) (hE _ ⟨e₀⟩) hβ hP1L hP1A hP1S

end J3Assembly

end CFSG.AGLEmbedding
