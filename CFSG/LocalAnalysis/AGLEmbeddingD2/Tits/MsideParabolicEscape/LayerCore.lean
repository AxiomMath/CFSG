module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedStructure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.CharSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.QuasithinUnique CFSG.Quasithin CFSG.AGLEmbeddingD2.Tits.MsidePrelim

@[expose] def AGL81II1320Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T : Subgroup G), CFSG.Open.IsKProper G → M ≠ ⊤ →
    CharTwo M → IsSylowTwoOf T M →
    (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (C : Set G) ⊓ M)) →
    (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      ∀ U : Subgroup G, U ≤ Subgroup.normalizer (C : Set G) ⊓ M → IsPGroup 3 U →
        ¬ IsCyclic U → IsElemAbelian 3 U ∧ Nat.card U = 9 ∧
          ∀ x ∈ U, x ≠ 1 → ∀ y ∈ U, y ≠ 1 →
            ∃ n ∈ M ⊓ Subgroup.normalizer (U : Set G), n * x * n⁻¹ = y) →
    (∀ Y : Subgroup G, Y ≤ M → IsSubnormal Y M → InClassXBlock Y → False) →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∃ L : Subgroup G, IsRankTwoLayer M L

theorem normalizer_le_normalizer_of_char {G : Type} [Group G] {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf S)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCS] at h

theorem d2L34BetaLayerExists_of_core
    (hcore : AGL81II1320Core) (hFF : CitedFFL34BestOffender)
    (hN : D2L34BetaNormalizerSolvable) (hD1 : D1NoXBlock) : D2L34BetaLayerExists := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOnly := hAll.onlyL34At
  obtain ⟨T, hT, -⟩ := B6.exists_isSylowTwoOf_ge (J := H ⊓ M) (X := ⊥) IsPGroup.of_bot bot_le
  obtain ⟨hTM, -⟩ :=
    D2L34BetaConf.isSylowTwoOf_of_cover (d2L34BetaPushUpCoverSyl hFF) hc hstr hOnly hT
  obtain ⟨x, -, hxN, hxM, -⟩ := D2L34BetaConf.exists_two_element hc hT
  have hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M := fun hle => hxM (hle hxN)
  have hMtop : M ≠ ⊤ := fun h => hNT (h ▸ le_top)
  refine hcore G M T hc.glob.kProper hMtop (hc.glob.charTwo M hc.esc.maxTwoLocal_M.1) hTM
    (fun C hC1 hCT hchar => hN d G P M A H R Rbar K hc hstr hAll hKmax T hTM C hC1 hCT hchar)
    (fun C hC1 hCT hchar U hU hU3 hUc => ?_)
    (fun Y hYM hYs hYX => hD1 G hc.glob.toAGLGlobal M Y hc.esc.maxTwoLocal_M hYM hYs hYX) hcon
  have hNC : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC1, hTM.2.1.to_le hCT, rfl⟩
  have hNCM : ¬ Subgroup.normalizer (C : Set G) ≤ M := fun hle =>
    hNT ((normalizer_le_normalizer_of_char hCT hchar).trans hle)
  exact D2L34BetaConf.exists_conj_eq_of_not_isCyclic hc hstr hOnly hNC hNCM
    (hU.trans inf_le_left) (hU.trans inf_le_right) hU3 hUc

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
