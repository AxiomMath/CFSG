module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem charTwo_of_pCoreOf_le (hX : GNSetting X T) {H : Subgroup X}
    (hO : pCoreOf 2 (⊤ : Subgroup X) ≤ H) : CharTwo H := by
  have hQ : pCoreOf 2 (⊤ : Subgroup X) ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO
      (fun h _ => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤ (Subgroup.mem_top h))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)
  have hchar : (⊤ : Subgroup X) ⊓ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) ≤
      pCoreOf 2 ⊤ := hX.charTwo
  intro x hx
  exact hQ (hchar ⟨Subgroup.mem_top x, Subgroup.centralizer_le hQ hx.2⟩)

end CFSG.AGLEmbeddingD2.Tits.GN516
