module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBIrrGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizerAux
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

namespace ToralReduce

theorem card_center_eq_card_inf_centralizer {Y : Type*} [Group Y] (K : Subgroup Y) :
    Nat.card (Subgroup.center ↥K) =
      Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) := by
  have h : (Subgroup.center ↥K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    · rintro ⟨hyK, hyC⟩
      refine ⟨⟨y, hyK⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hyC k k.2
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

variable {G : Type} [Group G] [Finite G]

theorem odd_card_center_barM {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) :
    Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
  rw [card_center_eq_card_inf_centralizer, ← Nat.coprime_two_left]
  exact coprime_two_card_inf_centralizer (pCore_quotient_pCore_eq_bot' 2) hL.component.2.1

theorem compParab_of_nineThreeTwo {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) :
    CompParab (barM M L) (blockPL M S L) :=
  ⟨hL.component, h2.1, odd_card_center_barM hL.toIsTwoPrimeComponent, h2.2.1,
    barM_normalizer_inf_ne_of_asc81bHyp hA hL, ne_inf_normalizer_of_asc81bHyp hA hL hS h2⟩

theorem exists_census_of_nineThreeTwo (hC : KFactFixCensusThree) (hG : GlueVhyp)
    {M S L : Subgroup G} (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L)
    (hcyc : CycPerfect 3 (blockPL M S L)) {u : ↥M ⧸ CFSG.pCore 2 ↥M} (hu : u ∈ barM M L)
    (hu3 : u ^ 3 = 1) (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V)
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) :
    CompParab (barM M L) (blockPL M S L) ∧
      u ∈ perfectJoin (blockPL M S L) ⊔
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∃ e : ℕ, 2 ≤ e ∧ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
        projectiveSL 3 (GaloisField 2 e)) := by
  have hCP := compParab_of_nineThreeTwo hA hL hS h2
  obtain ⟨V, hVp, hVL, hVS, huV⟩ := hV
  have hVO : V ≤ Subgroup.normalizer (pCoreOf 2 (blockPL M S L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [← h2.2.2]
    exact hVS
  exact ⟨hCP, hG _ _ _ hCP V hVp hVL hVO huV,
    hC _ _ _ hCP hcyc u hu hu3 huC ⟨V, hVp, hVL, hVO, huV⟩ hfix⟩

theorem four_le_card_galoisField {e : ℕ} (he : 2 ≤ e) : 4 ≤ Nat.card (GaloisField 2 e) := by
  rw [GaloisField.card 2 e (by omega)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

end ToralReduce

end CFSG.AGLEmbedding
