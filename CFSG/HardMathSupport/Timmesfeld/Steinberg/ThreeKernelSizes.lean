module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.KernelComponentSizes
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def triIn (b : Fin τ.rank → ZMod 3) (k : ℕ) : Bool :=
  decide (triPairing b (ComponentCert.rt τ k) = 0)

theorem triIn_iff (b : Fin τ.rank → ZMod 3) (k : ℕ) :
    triIn b k = true ↔ triChar b (Multiplicative.ofAdd (ComponentCert.rt τ k)) = 1 := by
  rw [triIn, decide_eq_true_iff, triChar_apply, Z3.ofAdd_eq_one]

theorem kernelSizes_triChar (b : Fin τ.rank → ZMod 3)
    (S : ComponentCert) (h : S.check τ (triIn b) = true) :
    KernelSizes (triChar b) (S.sizes τ (triIn b)) :=
  ComponentCert.kernelSizes_of_check (fun k _ => triIn_iff b k) h

theorem ncard_kernelRoots_triChar_filter
    (b : Fin τ.rank → ZMod 3) (P : (Fin τ.rank → ℤ) → Prop) [DecidablePred P] :
    {α | α ∈ kernelRoots (triChar b) ∧ P α}.ncard =
      ((ComponentCert.sigmaIdx τ (triIn b)).filter fun k =>
        decide (P (ComponentCert.rt τ k))).length :=
  ComponentCert.ncard_kernelRoots_filter (fun k _ => triIn_iff b k) P

end CFSG.HardMathSupport.Timmesfeld.Steinberg
