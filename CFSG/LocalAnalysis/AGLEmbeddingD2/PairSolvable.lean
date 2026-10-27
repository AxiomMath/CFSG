module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeSolvableM
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectCore
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem false_of_isSolvable (h : AGLPair p M H R) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) (hM : Group.IsSolvable M) : False := by
  have hodd := h.oddCore_le_centralizer h84 hD2
  have hSp : IsPGroup 2 (barM M (pCoreOf 2 H)) :=
    isPGroup_barM (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
  have hle : barM M (pCoreOf 2 H) ≤ CFSG.pCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    le_pCore_of_le_centralizer_components hSp
      (fun L hL => (no_component_of_isSolvable hM L hL).elim) fun l hl => by
        by_cases hl2 : l = 2
        · rw [hl2, pCore_quotient_pCore_eq_bot']
          exact Subgroup.le_centralizer_iff.mp bot_le
        · exact Subgroup.le_centralizer_iff.mp ((pCore_le_pPrimeCore_two hl hl2).trans hodd)
  rw [pCore_quotient_pCore_eq_bot'] at hle
  have hSQ : pCoreOf 2 H ≤ pCoreOf 2 M := fun s hs => by
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, h.twoCore_le hs⟩ ∈
        barM M (pCoreOf 2 H) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
    exact coe_mem_pCoreOf_two_of_mk_eq_one _ (Subgroup.mem_bot.mp (hle hmem))
  have hMH : M ≤ H := by
    rw [← h.normalizer_twoCore_H, le_antisymm hSQ h.twoCore_M_le]
    exact localGroup_le_normalizer_pCoreOf 2 M
  exact h.not_le (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

end AGLPair

section Three

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem D2Escape.stronglyEmbedded_of_pair (h : D2Escape 3 P M A H R) (hglob : D2Global G)
    (h3 : 3 ∈ GLBBetaFour G) (hpair : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : GLBStronglyEmbedded 3 M := by
  rcases h.deltaTwo_cases hglob h3 with hstr | ⟨hsolv, -⟩
  · exact hstr
  · exact (hpair.false_of_isSolvable h84 hD2 hsolv).elim

end Three

@[expose] def D2PairAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → primeComplementCore (G := X₀) p = ⊥

@[expose] def D2SolvableAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → Group.IsSolvable X₀

@[expose] def D2IndexCaseStrongAt (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (P : Sylow 3 G) (M A H R : Subgroup G), D2Escape 3 P M A H R →
    D2EscapeMax 3 P M R → 3 ∈ GLBBetaFour G → GLBStronglyEmbedded 3 M →
    ∀ (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K →
      Nonempty (K ≃* i.Group) → False

theorem d2IndexCaseAt_three_of_pair {i : TauCeti.CFSGIndex} (hpair : D2PairAt i fun p => p = 3)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hS : D2IndexCaseStrongAt i) :
    D2IndexCaseAt i fun p => p = 3 := by
  intro G _ _ hglob hD1 p hp3 P M A H R hesc hmax hβ Rbar K hRbar hK he
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU := hpair _ 3 rfl Rbar _ _ K hK he
  have hpr : AGLPair 3 M H R := hesc.toPair hglob.toAGLGlobal
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
  exact hS G hglob hD1 P M A H R hesc hmax hβ
    (hesc.stronglyEmbedded_of_pair hglob hβ hpr h84 (hD2.noXBlockFor hglob.toD1Global))
    Rbar K hRbar hK he

theorem d2PairAt_altSix : D2PairAt (.alternating 6 (by norm_num)) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK ⟨e⟩
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  exact hK.primeComplementCore_eq_bot_of_psl2 (e.trans e'.symm)

theorem d2SolvableAt_altSix : D2SolvableAt (.alternating 6 (by norm_num)) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK ⟨e⟩
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  rw [← hK.normalizer_A_eq_of_psl2 (e.trans e'.symm)]
  exact isSolvable_normalizer_of_card_eq_nine_of_le hK.card_A
    (hK.centralizer_A_le_of_psl2 (e.trans e'.symm))

theorem d2AltSixCase_of_strong (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hS : D2IndexCaseStrongAt (.alternating 6 (by norm_num))) : D2AltSixCase :=
  d2IndexCaseAt_three_of_pair d2PairAt_altSix h84 hD2 hS

end CFSG.AGLEmbeddingD2
