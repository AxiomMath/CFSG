module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLAltMain
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.Blueprint

@[expose] def NonExactShapeEightLookup : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X) (Sg V K : Subgroup X),
    CFSG.SectionRank.IsKGroupCat X → CFSG.oddCore X = ⊥ → SwapShape t Sg V →
    K = CFSG.layer X → CFSG.IsComponent K → ⁅Sg, Sg⁆ ≤ K → ⁅Sg, Sg⁆ ≠ K →
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 10)) ∨
        Nonempty (K ⧸ Subgroup.center K ≃* NativeSporadic.HS) ∨
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 4 2 2

theorem nonExactShapeEight_of_alternating {X : Type} [Group X] [Finite X] {t : X}
    {Sg V K : Subgroup X} (hS : SwapShape t Sg V) (hK : K = CFSG.layer X)
    (hc : CFSG.IsComponent K) (hA : ⁅Sg, Sg⁆ ≤ K) (hne : ⁅Sg, Sg⁆ ≠ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 10)) ∧ Subgroup.center K = ⊥ := by
  have : K.Characteristic := by
    subst hK
    exact CFSG.LocalCores.layer_characteristic
  obtain ⟨hm, hZ⟩ := eq_ten_of_alternating hS hc.1 hA hne e
  subst hm
  exact ⟨⟨e⟩, hZ⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
