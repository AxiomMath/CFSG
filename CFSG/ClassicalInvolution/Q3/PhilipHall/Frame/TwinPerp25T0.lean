module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUMuRest

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


section Defs

variable {X : Type} [Group X]

@[expose] def NC4Weak (Φ : Set (Subgroup X)) : Prop :=
  ∃ M₁ ∈ Φ, ∃ y ∈ M₁, orderOf y = 4 ∧
    ∃ M₂ ∈ Φ, ∃ s₂ : X, IsUniqueInvolution M₂ s₂ ∧ s₂ ≠ y * y ∧ s₂ * y = y * s₂

@[expose] def AENC4 (n : ℕ) (𝒜 : Set (Finset (Fin n))) : Prop :=
  ∃ (α β : Finset (Fin n)) (hα : α.card = 4) (hβ : β.card = 4), α ∈ 𝒜 ∧ β ∈ 𝒜 ∧ α ≠ β ∧
    ∃ (b : Bool) (y : AE.AEQ n), y ∈ AE.memBar α hα b ∧ y * y = AE.zBar α hα ∧
      y * AE.zBar β hβ = AE.zBar β hβ * y

end Defs

structure TwinSecCtx (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop where
  S : Q8Section X Φ
  trans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  two : ∀ J ∈ Φ, IsPGroup 2 J
  q8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2)
  twin : ∃ K ∈ Φ, ∃ K' ∈ Φ, ∃ z : X, K' ∈ omegaNbr Φ K ∧ IsUniqueInvolution K z ∧
    IsUniqueInvolution K' z ∧ ∀ M ∈ omegaNbr Φ K, M = K'
  nc4 : ¬ NC4Weak Φ
  bad : ∀ z : X, (∀ M ∈ Φ, IsUniqueInvolution M z) → False

namespace TwinSecCtx

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_inv (h : TwinSecCtx X Φ) {M : Subgroup X} (hM : M ∈ Φ) :
    ∃ s : X, IsUniqueInvolution M s :=
  (h.S.hyp.omega1 M hM).1

theorem twinOnly (h : TwinSecCtx X Φ) : TwinOnlyNbr Φ := by
  obtain ⟨K, hK, K', -, z, -, -, -, hnb⟩ := h.twin
  exact twinOnly_of_trans h.S.hyp.conjInvariant h.trans hK hnb

theorem twin_inv (h : TwinSecCtx X Φ) {M N : Subgroup X} (hM : M ∈ Φ) (hN : N ∈ omegaNbr Φ M) {s s' : X}
    (hs : IsUniqueInvolution M s) (hs' : IsUniqueInvolution N s') : s = s' := by
  obtain ⟨K, hK, K', hK', z, hK'nb, hz, hz', hnb⟩ := h.twin
  obtain ⟨g, rfl⟩ := h.trans K hK M hM
  have h1 := omegaNbr_conj h.S.hyp.conjInvariant hN g⁻¹
  rw [conjSub_inv_conjSub] at h1
  have e : conjSub g⁻¹ N = K' := hnb _ h1
  have hN' : N = conjSub g K' := by
    rw [← e, conjSub_conjSub_inv]
  rw [hN'] at hs'
  have e1 : s = g * z * g⁻¹ := hs.eq (hz.conj g)
  have e2 : s' = g * z * g⁻¹ := hs'.eq (hz'.conj g)
  rw [e1, e2]

end TwinSecCtx

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
