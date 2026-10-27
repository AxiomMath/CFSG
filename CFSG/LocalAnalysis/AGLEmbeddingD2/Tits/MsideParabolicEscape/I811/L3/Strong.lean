module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

section Cases

variable {F : Type} [Field F] [Finite F]

theorem transitive_cases (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) (h3 : (3 : F) ≠ 0) (hmax : GL2NonsplitMax F)
    {μ : F} (hμ0 : μ ≠ 0) (hμ6 : μ ^ 6 ≠ 1) {W : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) :
    W = ⊤ ∨ (W.index = Nat.card F ^ 2 ∧ (W ⊓ P1) ⊓ Q1 = ⊥) := by
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  have hlevY : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W ⊓ P1 :=
    fun X hX => ⟨hlev X hX, lev_mem_P1 X⟩
  rcases inf_Q1_eq_bot_or_le hroot hcube hlevY with hb | hle
  · right
    refine ⟨?_, hb⟩
    have hNtY : (Nt : Subgroup (GL (Fin 2) F)) ≤ ((W ⊓ P1).subgroupOf P1).map rho1 := by
      intro X hX
      exact ⟨⟨lev X, lev_mem_P1 X⟩,
        Subgroup.mem_subgroupOf.mpr ⟨hNW (lev_mem_normalizer_A0 hX), lev_mem_P1 X⟩, rho1_lev X⟩
    rcases hmax _ hNtY with h | h
    · exact (false_of_map_rho1_le_Nt hroot hμ0 hμ6 hlev htr h.le).elim
    · have htop := map_rho1_eq_top hroot h3 hNtY h
      have hrel := relIndex_P1_eq htop
      rw [index_eq_relIndex_of_transitive htr, ← Subgroup.inf_relIndex_right, hrel,
        Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hb),
        Subgroup.index_bot, card_Q1]
  · left
    exact eq_top_of_Q1_le_of_transitive htr (hle.trans inf_le_left)

end Cases

variable {F : Type} [Field F] [Finite F]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
