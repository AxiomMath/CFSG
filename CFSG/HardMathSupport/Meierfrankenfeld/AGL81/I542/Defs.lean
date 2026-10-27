module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def relFix (ρ : Representation (ZMod 2) G W) (B : Subgroup G)
    (Y₀ Y₁ : Submodule (ZMod 2) W) : Submodule (ZMod 2) W where
  carrier := {y | y ∈ Y₁ ∧ ∀ b ∈ B, ρ b y - y ∈ Y₀}
  add_mem' {u v} hu hv := ⟨Y₁.add_mem hu.1 hv.1, fun b hb => by
    have := Y₀.add_mem (hu.2 b hb) (hv.2 b hb)
    simpa [map_add, add_sub_add_comm] using this⟩
  zero_mem' := ⟨Y₁.zero_mem, fun b _ => by simp⟩
  smul_mem' c v hv := ⟨Y₁.smul_mem c hv.1, fun b hb => by
    have := Y₀.smul_mem c (hv.2 b hb)
    simpa [map_smul, smul_sub] using this⟩

@[expose] noncomputable def secCod (ρ : Representation (ZMod 2) G W) (B : Subgroup G)
    (Y₀ Y₁ : Submodule (ZMod 2) W) : ℕ :=
  Module.finrank (ZMod 2) Y₁ - Module.finrank (ZMod 2) (relFix ρ B Y₀ Y₁)

@[expose] noncomputable def kerDim (ρ : Representation (ZMod 2) G W) (f : Polynomial (ZMod 2))
    (x : G) (Y : Submodule (ZMod 2) W) : ℕ :=
  Module.finrank (ZMod 2) ↥(Y ⊓ LinearMap.ker (Polynomial.aeval (ρ x) f))

@[expose] noncomputable def secChi (ρ : Representation (ZMod 2) G W) (f : Polynomial (ZMod 2))
    (x y : G) (Y₀ Y₁ : Submodule (ZMod 2) W) : ℤ :=
  ((kerDim ρ f x Y₁ : ℤ) - kerDim ρ f x Y₀) - ((kerDim ρ f y Y₁ : ℤ) - kerDim ρ f y Y₀)

@[expose] def SecTrivial (ρ : Representation (ZMod 2) G W) (K : Subgroup G)
    (Y₀ Y₁ : Submodule (ZMod 2) W) : Prop :=
  ∀ k ∈ K, ∀ v ∈ Y₁, ρ k v - v ∈ Y₀

@[expose] def IsMinSec (ρ : Representation (ZMod 2) G W) (H : Subgroup G)
    (Y₀ Y₁ : Submodule (ZMod 2) W) : Prop :=
  GeneralFF.IsInvariant ρ H Y₀ ∧ GeneralFF.IsInvariant ρ H Y₁ ∧ Y₀ < Y₁ ∧
    ∀ Z : Submodule (ZMod 2) W, GeneralFF.IsInvariant ρ H Z → Y₀ ≤ Z → Z ≤ Y₁ → Z = Y₀ ∨ Z = Y₁

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
