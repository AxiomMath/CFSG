module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveFaithful
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocks
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveMSide

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2AltFiveBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], p = 5 → ∀ (P : Sylow p G) (M A H : Subgroup G),
      D2Escape p P M A H A → D2EscapeMax p P M A → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → False

theorem false_of_altFiveResidue {G : Type} [Group G] [Finite G] (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven)
    (hglob : AGLGlobal G) (hD1 : D1For G) (hNX : NoXBlockFor G) {p : ℕ} [Fact p.Prime]
    (hp5 : p = 5) {P : Sylow p G} {M A H : Subgroup G} (hesc : D2Escape p P M A H A)
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p)))
    (hblock : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → False)
    (hres : ((∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
          ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∨
        ∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
          barM M A ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥)) : False := by
  have hdata : D2AltData p M H A A :=
    hesc.altData_of_alt hglob hRbar hK e hp5.ge
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L :=
    fun L hL => hdata.pair.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL
  rcases hres with ⟨L, hL, hA⟩ | ⟨Lb, hLb, hfaith⟩
  · exact hblock L hL hA
  obtain ⟨L, hL2, hbar, hLw | hLK⟩ := hdata.pair.exists_weakSBlock_or_le_inf hLb
  · refine hblock L hLw fun hle => ?_
    obtain ⟨c₀, c₁, s, g, hsc⟩ := hdata.scalar
    have hc₀A : c₀ ∈ A := hsc.mem_zero
    have hc₀ne : c₀ ≠ 1 := by
      intro hc
      have hc' : c₁ = 1 := by rw [← hsc.conj_zero, hc]; group
      have hAbot : A = ⊥ := by rw [hsc.span, hc, hc']; simp
      have := hdata.card
      rw [hAbot, Subgroup.card_bot] at this
      have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
      omega
    have hc₀M : c₀ ∈ M := hdata.pair.le_M (hdata.eq_R ▸ hc₀A)
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c₀, hc₀M⟩ ∈
        barM M A ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc₀A),
        hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc₀A))⟩
    rw [hbar, hfaith, Subgroup.mem_bot] at hmem
    exact hc₀ne (hdata.pair.eq_one_of_mem_twoCore hdata.elem hc₀A
      (coe_mem_pCoreOf_two_of_mk_eq_one _ hmem))
  · exact hesc.false_of_faithful_component_alt hglob hD1 hα hSch hB3 hRbar hK e
      hp5.ge hL2 hLK (hbar ▸ hfaith)

theorem d2AltFiveResidue_of_block (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hblock : D2AltFiveBlock) : D2AltFiveResidue := by
  intro G _ _ hglob hD1 p _ hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩ hres
  exact false_of_altFiveResidue hα hSch h85 h86 h93 hK2 hC3 hK5 hglob.toAGLGlobal hD1
    (hD2.noXBlockFor hglob.toD1Global) hp5 hesc hRbar hK e
    (fun L hL hA => hblock G hglob hD1 p hp5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩ L hL hA) hres

theorem d2AltFive_of_block (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hblock : D2AltFiveBlock) : D2AltFive :=
  d2AltFive_of_residue hα hSch h84 h85 h86 h93 hD2 hK2 hC3 hK5
    (d2AltFiveResidue_of_block hα hSch h85 h86 h93 hD2 hK2 hC3 hK5 hblock)

end CFSG.AGLEmbeddingD2
