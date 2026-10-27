module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupCenter
public import CFSG.LocalAnalysis.OddStandard.ChengHeldFrame

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Terms

variable {H K : Type*} [Group H] [Group K]

theorem evalE_map (f : H →* K) (σ : ℕ → H) :
    ∀ τ : Tm, f (evalE σ τ) = evalE (fun i => f (σ i)) τ
  | .var i => rfl
  | .one => map_one f
  | .mul a b => by rw [evalE, evalE, map_mul, evalE_map f σ a, evalE_map f σ b]
  | .inv a => by rw [evalE, evalE, map_inv, evalE_map f σ a]

end Terms

section SInJhat

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

theorem S_isSylowTwoIn : IsSylowTwoIn d.S A := isSylowTwoIn_of_isSylowOf d.S_sylow

theorem S_isPGroup : IsPGroup 2 d.S := d.X_sylow.isPGroup.to_le d.S_le_X

@[expose] noncomputable def jS : ↥d.S →* Jhat A := (jq A).comp (Subgroup.inclusion d.S_le_A)

theorem jS_apply (s : ↥d.S) : jS d s = jq A ⟨s, d.S_le_A s.2⟩ := rfl

theorem jS_injective : Function.Injective (jS d) := by
  intro a b hab
  exact Subtype.ext (eq_of_jq_eq d.S_le_A (S_isPGroup d) a.2 b.2 hab)

@[expose] def cS (y : G) (hy : y ∈ d.X) : ↥d.S ≃* ↥d.S where
  toFun s := ⟨y⁻¹ * s * y, by simpa using d.conj_mem_S (d.X.inv_mem hy) s.2⟩
  invFun s := ⟨y * s * y⁻¹, d.conj_mem_S hy s.2⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem jS_cS (y : G) (hy : y ∈ d.X) (s : ↥d.S) :
    jS d (cS d y hy s) = betaHat A (d.X_sylow.le hy) (jS d s) := by
  rw [jS_apply, jS_apply, betaHat_jq]
  rfl

theorem cj_coe (y : G) (hy : y ∈ d.X) (s : ↥d.S) : cj (s : G) y = ((cS d y hy s : ↥d.S) : G) := rfl

end SInJhat

end CFSG.OddStandard.ChengHeld.M1b
