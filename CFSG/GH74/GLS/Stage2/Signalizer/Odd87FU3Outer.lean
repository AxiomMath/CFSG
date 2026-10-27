module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Real
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3InvType

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank CFSG.GH74.KGroups.L3Eps.Uni
open scoped MatrixGroups commutatorElement

theorem fu3_outer_false {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {σ : MulAut ↥K}
    (hσ : σ * σ = 1) (hout : ¬ ∃ s : ↥K, ∀ k : ↥K, σ k = s * k * s⁻¹) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, σ j = j → (j : A) ∈ normalizer (X : Set A)) : False := by
  classical
  have hud : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hud e
  rcases involution_type_of_three_le hud hℓ2 h3 hθ hσ with
    ⟨A', hAu, hAA, hrel⟩ | ⟨φ, A', hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_conj_of_typeI hud hθ hAu hAA hrel
    exact hout ⟨y, fun k => by rw [← hy]; rfl⟩
  · obtain ⟨D⟩ := outerData_of_typeII hud hℓ2 h3 hθ hφ hAu hAA hrel
    refine fu3_outer_of_data hℓ2 h3 hθ D e hp2 hX hX1 hfaith hJ ?_
    intro ψ n hn hψ hfix
    exact aut_fixing_trivial_unitary hud hℓ2 hθ D.Ψ.range D.centOK
      (fun T hT => D.comm T (fun S => hT (D.Ψ S) ⟨S, rfl⟩))
      (fun τ hτ => D.tr τ (fun S => hτ (D.Ψ S) ⟨S, rfl⟩)) hn hψ hfix

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
