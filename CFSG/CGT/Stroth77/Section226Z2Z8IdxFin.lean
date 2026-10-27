module

public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

namespace Sec226ZIdx

variable (τ : StrothTypeIndex)

@[expose] def lin (pa pb v : Torus τ.k) : Torus τ.k :=
  (v 0).val • gen τ.k 0 + (v 1).val • pa + (v 2).val • pb

@[expose] def five (v : Torus τ.k) : Torus τ.k := lin τ (5 • gen τ.k 1) (5 • gen τ.k 2) v

@[expose] def DecompFact : Prop := ∀ v : Torus τ.k, lin τ (gen τ.k 1) (gen τ.k 2) v = v

@[expose] def OrderFact : Prop :=
  2 • gen τ.k 0 = (0 : Torus τ.k) ∧ 8 • gen τ.k 1 = (0 : Torus τ.k) ∧
    8 • gen τ.k 2 = (0 : Torus τ.k)

@[expose] def LinFact : Prop := ∀ pa pb : Torus τ.k,
  lin τ pa pb (gen τ.k 0) = gen τ.k 0 ∧ lin τ pa pb (gen τ.k 1) = pa ∧
    lin τ pa pb (gen τ.k 2) = pb ∧ lin τ pa pb (2 • gen τ.k 1) = 2 • pa ∧
    lin τ pa pb (2 • gen τ.k 2) = 2 • pb

@[expose] def AuxAt (pa pb w : Torus τ.k) : Prop :=
  τ.action.φuv (lin τ pa pb (τ.action.φuv w)) = lin τ pa pb w ∧
    τ.action.φt (lin τ pa pb (τ.action.φt w)) = lin τ pa pb w ∧ lin τ pa pb (lin τ pa pb w) = w

instance (pa pb w : Torus τ.k) : Decidable (AuxAt τ pa pb w) := by unfold AuxAt; infer_instance

@[expose] def AuxFact : Prop := ∀ pa pb : Torus τ.k, 4 • pa = 4 • gen τ.k 1 →
  4 • pb = 4 • gen τ.k 2 →
    AuxAt τ pa pb (gen τ.k 0) ∧ AuxAt τ pa pb (2 • gen τ.k 1) ∧ AuxAt τ pa pb (2 • gen τ.k 2)

@[expose] def Om2DecompFact : Prop := ∀ v : Torus τ.k, 4 • v = (0 : Torus τ.k) →
  (v 0).val • gen τ.k 0 + ((v 1).val / 2) • (2 • gen τ.k 1) + ((v 2).val / 2) • (2 • gen τ.k 2) = v

@[expose] def MainFact : Prop := ∀ pa pb : Torus τ.k, 4 • pa = 4 • gen τ.k 1 →
  4 • pb = 4 • gen τ.k 2 →
  ((∀ i, τ.action.φuv (lin τ pa pb (τ.action.φuv (gen τ.k i))) = lin τ pa pb (gen τ.k i)) ∨
    ∀ i, τ.action.φuv (lin τ pa pb (τ.action.φuv (gen τ.k i))) =
      five τ (lin τ pa pb (gen τ.k i))) →
  ((∀ i, τ.action.φt (lin τ pa pb (τ.action.φt (gen τ.k i))) = lin τ pa pb (gen τ.k i)) ∨
    ∀ i, τ.action.φt (lin τ pa pb (τ.action.φt (gen τ.k i))) =
      five τ (lin τ pa pb (gen τ.k i))) →
  ((∀ i, lin τ pa pb (lin τ pa pb (gen τ.k i)) = gen τ.k i) ∨
    ∀ i, lin τ pa pb (lin τ pa pb (gen τ.k i)) = five τ (gen τ.k i)) →
  (2 • pa = 2 • gen τ.k 1 ∧ 2 • pb = 2 • gen τ.k 2) ∨
    (2 • pa = -(2 • gen τ.k 1 : Torus τ.k) ∧ 2 • pb = -(2 • gen τ.k 2 : Torus τ.k))

@[expose] def TrivFact : Prop := ∀ pa pb : Torus τ.k, 2 • pa = 2 • gen τ.k 1 →
  2 • pb = 2 • gen τ.k 2 → ∀ v : Torus τ.k, 4 • v = (0 : Torus τ.k) → lin τ pa pb v = v

@[expose] def InvFact : Prop := ∀ pa pb : Torus τ.k, 2 • pa = -(2 • gen τ.k 1 : Torus τ.k) →
  2 • pb = -(2 • gen τ.k 2 : Torus τ.k) → ∀ v : Torus τ.k, 4 • v = (0 : Torus τ.k) →
    lin τ pa pb v = lin τ (-gen τ.k 1) (-gen τ.k 2) v

@[expose] def CentFact : Prop := ∀ pa pb : Torus τ.k, 2 • pa = -(2 • gen τ.k 1 : Torus τ.k) →
  2 • pb = -(2 • gen τ.k 2 : Torus τ.k) → ∀ v : Torus τ.k, 2 • v = (0 : Torus τ.k) ∨
    lin τ pa pb v ≠ v

instance : Decidable (DecompFact τ) := by unfold DecompFact; infer_instance
instance : Decidable (OrderFact τ) := by unfold OrderFact; infer_instance
instance : Decidable (LinFact τ) := by unfold LinFact; infer_instance
instance : Decidable (AuxFact τ) := by unfold AuxFact; infer_instance
instance : Decidable (Om2DecompFact τ) := by unfold Om2DecompFact; infer_instance
instance : Decidable (MainFact τ) := by unfold MainFact; infer_instance
instance : Decidable (TrivFact τ) := by unfold TrivFact; infer_instance
instance : Decidable (InvFact τ) := by unfold InvFact; infer_instance
instance : Decidable (CentFact τ) := by unfold CentFact; infer_instance

structure IdxFacts : Prop where
  decomp : DecompFact τ
  order : OrderFact τ
  linf : LinFact τ
  aux : AuxFact τ
  om2decomp : Om2DecompFact τ
  main : MainFact τ
  triv : TrivFact τ
  inv : InvFact τ
  cent : CentFact τ

abbrev τ₀ : StrothTypeIndex := .t200 1
abbrev τ₁ : StrothTypeIndex := .t201 1

theorem decompFact_t200 : DecompFact τ₀ := by decide +kernel
theorem orderFact_t200 : OrderFact τ₀ := by decide +kernel
theorem linFact_t200 : LinFact τ₀ := by decide +kernel
theorem auxFact_t200 : AuxFact τ₀ := by decide +kernel
theorem om2DecompFact_t200 : Om2DecompFact τ₀ := by decide +kernel
theorem mainFact_t200 : MainFact τ₀ := by decide +kernel
theorem trivFact_t200 : TrivFact τ₀ := by decide +kernel
theorem invFact_t200 : InvFact τ₀ := by decide +kernel
theorem centFact_t200 : CentFact τ₀ := by decide +kernel

theorem decompFact_t201 : DecompFact τ₁ := by decide +kernel
theorem orderFact_t201 : OrderFact τ₁ := by decide +kernel
theorem linFact_t201 : LinFact τ₁ := by decide +kernel
theorem auxFact_t201 : AuxFact τ₁ := by decide +kernel
theorem om2DecompFact_t201 : Om2DecompFact τ₁ := by decide +kernel
theorem mainFact_t201 : MainFact τ₁ := by decide +kernel
theorem trivFact_t201 : TrivFact τ₁ := by decide +kernel
theorem invFact_t201 : InvFact τ₁ := by decide +kernel
theorem centFact_t201 : CentFact τ₁ := by decide +kernel

theorem idxFacts_t200 : IdxFacts τ₀ :=
  ⟨decompFact_t200, orderFact_t200, linFact_t200, auxFact_t200, om2DecompFact_t200,
    mainFact_t200, trivFact_t200,
    invFact_t200, centFact_t200⟩

theorem idxFacts_t201 : IdxFacts τ₁ :=
  ⟨decompFact_t201, orderFact_t201, linFact_t201, auxFact_t201, om2DecompFact_t201,
    mainFact_t201, trivFact_t201,
    invFact_t201, centFact_t201⟩

theorem idxFacts_of {τ : StrothTypeIndex} (hτ : τ = .t200 1 ∨ τ = .t201 1) : IdxFacts τ := by
  rcases hτ with rfl | rfl
  exacts [idxFacts_t200, idxFacts_t201]

end Sec226ZIdx

end CFSG.CGT.Stroth77
