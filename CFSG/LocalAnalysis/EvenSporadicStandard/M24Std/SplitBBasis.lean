module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def fB (i : Fin 4) : S24 := m24B0B.getD i 1

@[expose] def BasisData : Prop :=
  (∀ i, fB i ∈ m24B0l) ∧
    (∀ c d : Fin 4 → ZMod 2, ebasis4 fB c = ebasis4 fB d → c = d) ∧
    (∀ c d : Fin 4 → ZMod 2, ebasis4 fB c * ebasis4 fB d = ebasis4 fB (c + d)) ∧
    (∀ c : Fin 4 → ZMod 2, ebasis4 fB c ∈ m24B0l) ∧
    (∀ y ∈ m24B0l, ∃ c : Fin 4 → ZMod 2, ebasis4 fB c = y)

instance : Decidable BasisData := by unfold BasisData; infer_instance

@[expose] def NormB0 (x : S24) : Prop :=
  (∀ y ∈ m24B0l, x * y * x⁻¹ ∈ m24B0l) ∧ ∀ y ∈ m24B0l, x⁻¹ * y * x ∈ m24B0l

instance (x : S24) : Decidable (NormB0 x) := by unfold NormB0; infer_instance

theorem NormB0.mem_iff {x : S24} (hx : NormB0 x) (y : S24) :
    y ∈ m24B0l ↔ x * y * x⁻¹ ∈ m24B0l := by
  refine ⟨hx.1 y, fun h => ?_⟩
  have h2 := hx.2 _ h
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h2

end CFSG.EvenSporadicStandard.M24Std.SplitB
