module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.ComponentClassification.GHarris.SCert.SE

@[expose] def parF1 : Fin 8 → ℕ := ![0, 1, 1, 0, 0, 0, 0, 0]

@[expose] def parF2 : Fin 8 → ℕ := ![0, 0, 1, 1, 0, 0, 0, 0]

@[expose] def predE (s : SE) : Prop := s.d.val < 4 ∧ s.v1.val % 2 = 0 ∧ s.v2.val % 2 = 0

@[expose] def predF (s : SE) : Prop :=
  s.d.val < 4 ∧ s.v1.val % 2 = parF1 s.d ∧ s.v2.val % 2 = parF2 s.d

instance : DecidablePred predE := fun s => by unfold predE; infer_instance

instance : DecidablePred predF := fun s => by unfold predF; infer_instance

@[expose] def O4E (s : SE) : Prop := predE s ∧ s * s = gen 0

@[expose] def O4F (s : SE) : Prop := predF s ∧ s * s = gen 0

instance : DecidablePred O4E := fun s => by unfold O4E; infer_instance

instance : DecidablePred O4F := fun s => by unfold O4F; infer_instance

@[expose] def comm (e f : SE) : SE := e⁻¹ * f⁻¹ * e * f

@[expose] def commZ (e f : SE) : Prop := comm e f = 1 ∨ comm e f = gen 0

instance (e f : SE) : Decidable (commZ e f) := by unfold commZ; infer_instance

end CFSG.ComponentClassification.GHarris.SCert.SE
