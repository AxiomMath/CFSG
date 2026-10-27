module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public noncomputable section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise Classical

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

@[expose] def comp (σ : Setting G) (U : Subgroup G) (i : Fin 3) : Set G :=
  {u | u ∈ U ∧ σ.xs i * u = u * σ.xs i ∧ σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹}

@[expose] def R (Δ : Data σ r) (i : Fin 3) : Subgroup G := Δ.Q i ⊔ σ.Ps r i

@[expose] def Rs (Δ : Data σ r) (i : Fin 3) : Subgroup G := Δ.Qs i ⊔ σ.Ps r i

structure OmnibusAt (Δ : Data σ r) (H U : Subgroup G) : Prop where
  part_i_a : ∀ i : Fin 3, U ⊓ σ.Ns i ∈ signalizersPerm H σ.T σ.C r
  part_i_b : ∀ i : Fin 3, ∃ V : Subgroup G, (V : Set G) = comp σ U i ∧
    σ.C ≤ Subgroup.normalizer (V : Set G) ∧ (V ≤ σ.Ps r i ∨ V ≤ R Δ i ∨ V ≤ Rs Δ i)
  part_ii_a : ∃ R₀ : Subgroup G, IsSylowOf r R₀ σ.C ∧ R₀ ≤ U
  part_ii_b : ∃ R₀ : Subgroup G, IsSylowOf r R₀ (oddCoreIn H) ∧ R₀ ≤ U
  part_iii_a : oddCoreIn H ≠ ⊥ → U = pCoreIn r (U ⊔ σ.C) ⊔ (U ⊓ σ.C)
  part_iii_b : oddCoreIn H ≠ ⊥ → ∃ j : Fin 3, U = (U ⊓ oddCoreIn H) ⊔ (U ⊓ σ.Ns j)
  part_iv : oddCoreIn H ≠ ⊥ → ∀ U' ∈ maximals (signalizersPerm H σ.T σ.C r),
    ∃ m ∈ σ.M ⊓ H, conjSub m U' = U
  part_v : CFSG.HasNormalPComplement 2 ↥(U ⊔ σ.C) ∧ Δ.W ≤ oddCoreIn (U ⊔ σ.C)
  part_vi : pCoreIn r (U ⊔ σ.C) ∈ maximals (signalizers H σ.C r) ∧
    ∀ X ∈ signalizers H σ.C r, X ≤ U → X ≤ pCoreIn r (U ⊔ σ.C)

@[expose] def Omnibus (Δ : Data σ r) : Prop :=
  ∀ H : Subgroup G, σ.C ≤ H → ∀ U ∈ maximals (signalizersPerm H σ.T σ.C r), OmnibusAt Δ H U

@[expose] def ConjugateMaximalTC (σ : Setting G) (r : ℕ) : Prop :=
  ∀ U₁ ∈ maximals (signalizersPerm ⊤ σ.T σ.C r), ∀ U₂ ∈ maximals (signalizersPerm ⊤ σ.T σ.C r),
    ∃ m ∈ σ.M, conjSub m U₁ = U₂

@[expose] def NotPGroupP (σ : Setting G) (r : ℕ) : Prop :=
  ¬ IsPGroup r (σ.Ps r 0 ⊔ σ.Ps r 1 ⊔ σ.Ps r 2 : Subgroup G)

@[expose] def Transitivity (σ : Setting G) (r : ℕ) : Prop :=
  ∀ R₁ ∈ maximals (signalizers σ.N σ.C r),
    ∀ U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r), ∀ V ∈ maximals (signalizersPerm ⊤ σ.T σ.C r),
      R₁ ≤ U → R₁ ≤ V →
        (∃ c ∈ σ.C, conjSub c U = V) ∨ σ.Ps r 1 ≤ U ⊓ V ∨ σ.Ps r 2 ≤ U ⊓ V

@[expose] def PGroupR (Δ : Data σ r) : Prop :=
  IsPGroup r (R Δ 0 ⊔ R Δ 2 : Subgroup G)

end CFSG.ABGTheoremB.TotallyInverted
