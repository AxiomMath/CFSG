module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderLift
public import CFSG.RankThree.FFModules.Natural

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement MatrixGroups

section General

variable {K : Type*} [Group K] {L B : Subgroup K}

theorem le_sup_centralizer_of_forall_conjAgree
    (h : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l) :
    B ≤ L ⊔ Subgroup.centralizer (L : Set K) := by
  intro b hb
  obtain ⟨l, hl, hag⟩ := h b hb
  have hc : l⁻¹ * b ∈ Subgroup.centralizer (L : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hconj : (l⁻¹ * b) * k * (l⁻¹ * b)⁻¹ = k := by
      calc (l⁻¹ * b) * k * (l⁻¹ * b)⁻¹
          = l⁻¹ * (b * k * b⁻¹) * l := by group
        _ = l⁻¹ * (l * k * l⁻¹) * l := by rw [hag k hk]
        _ = k := by group
    calc k * (l⁻¹ * b)
        = ((l⁻¹ * b) * k * (l⁻¹ * b)⁻¹) * (l⁻¹ * b) := by rw [hconj]
      _ = (l⁻¹ * b) * k := by group
  have hmem : l * (l⁻¹ * b) ∈ L ⊔ Subgroup.centralizer (L : Set K) :=
    Subgroup.mul_mem_sup hl hc
  rwa [mul_inv_cancel_left] at hmem

end General

section Setting

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

abbrev gnW (T : Subgroup X) (hV : IsElemAbelian 2 (gnV T)) : Type :=
  Additive (IntMod (gnV T) hV)

end Setting

end CFSG.LocalAnalysis.RankThreeUC.S15
