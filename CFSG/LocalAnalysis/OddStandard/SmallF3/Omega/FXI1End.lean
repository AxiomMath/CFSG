module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fx_toEnd_pow (u : OGroup Q) (n : ℕ) :
    (((u ^ n : OGroup Q) : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) =
      ((u : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) ^ n := by
  induction n with
  | zero =>
    ext v
    simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    ext v
    simp

theorem fx_toEnd_commute (g : ↥(simGroup Q)) (u : OGroup Q) (h : simAct Q g u = u) :
    ((g : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) *
        ((u : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) =
      ((u : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) *
        ((g : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V) := by
  have h1 := congrArg (fun t : OGroup Q => (t : V ≃ₗ[ZMod 3] V)) h
  simp only [coe_simAct] at h1
  have h2 : (g : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V) =
      (u : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) :=
    calc (g : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V)
        = ((g : V ≃ₗ[ZMod 3] V) * (u : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V)⁻¹) *
            (g : V ≃ₗ[ZMod 3] V) := by group
      _ = (u : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) := by rw [h1]
  ext v
  have h3 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) h2
  simpa using h3

theorem fx_toEnd_mul_self_eq_neg_one (γ : V ≃ₗ[ZMod 3] V) (h : ∀ v, γ (γ v) = -v) :
    (γ : Module.End (ZMod 3) V) * (γ : Module.End (ZMod 3) V) = -1 := by
  ext v
  simpa using h v

end CFSG.OddStandard.SmallF3.Omega
