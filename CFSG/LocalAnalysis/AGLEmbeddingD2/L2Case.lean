module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Competitor

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2SurvivorsAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) (P : Sylow p G) (M A H : Subgroup G), D2Escape p P M A H A →
      D2EscapeMax p P M A → p ∈ GLBBetaFour G → AGLSurvivorData p M H A A

@[expose] def D2L2MSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Sylow p G) (M A H : Subgroup G),
      D2Escape p P M A H A → D2EscapeMax p P M A → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* PSL2GF p 2) → CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem five_le_of_valid_A_one {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .A 1 q) (hq : q.exponent = 2) (hp2 : q.p ≠ 2) : 5 ≤ q.p := by
  have hv := (TauCeti.LieTypeIndex.valid_iff _).mp d.2
  rw [hd] at hv
  obtain ⟨-, hdup⟩ := hv
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  have hp := q.prime_p
  have h2 := hp.two_le
  by_contra hlt
  have hcases : q.p = 3 ∨ q.p = 4 := by omega
  rcases hcases with h3 | h4
  · apply hdup
    left
    refine ⟨rfl, Or.inr (Or.inr ?_)⟩
    rw [TauCeti.PrimePower.card_def, hq, h3]
    norm_num
  · rw [h4] at hp
    norm_num at hp

theorem d2CaseL2Square_of (hS : D2SurvivorsAll) (hM : D2L2MSide) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : D2CaseL2Square := by
  intro d ⟨q, hq2, hd⟩ G _ _ hglob hD1 p hpc P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  have hp : p.Prime := hesc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hqp : q.p = p := by rw [hpc, hd, TauCeti.LieTypeIndex.characteristic_A]
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := 2) ⟨q, hd, hqp, hq2⟩
  have hp5 : 5 ≤ p := hqp ▸ five_le_of_valid_A_one hd hq2 (hqp ▸ hesc.ne_two)
  have hAR : A = R := hesc.A_eq_of_psl2 hRbar hK (e.trans e')
  subst hAR
  exact false_of_survivorsAt hglob.toAGLGlobal (hD1.at hβ) h84 hCGT
    (hD2.noXBlockFor hglob.toD1Global) hesc hmax
    (fun H' h' => hS G hglob hD1 p P M A H' h' hmax hβ)
    (hM G hglob hD1 p hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e.trans e'⟩)

end CFSG.AGLEmbeddingD2
