module

public import CFSG.GH74.GLS.Stage4.T2Coord
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Ch6TSing {G : Type} [Group G] (p q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) : Prop :=
  ∃ y ∈ K₁, y ∉ Subgroup.zpowers z ∧ ¬ p ∣ orderOf y ∧
    ∀ X : Subgroup G, X ≤ K₂ → IsPGroup p ↥X → Nat.card ↥X = q₂ →
      ∃ R : Subgroup G, IsPGroup p ↥R ∧ X ≤ R ∧ R ≤ centralizer (X : Set G) ∧ Nat.card ↥R = q₂ ^ 3 ∧
        (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧ (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧
        (∀ r ∈ R, z * r * z⁻¹ * r ∈ X) ∧ (∀ r ∈ R, y * r = r * y)

@[expose] def Ch6T2TSing : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ p : ℕ, Ch6NumD p q₁ q₂ →
              Ch6TSing p q₂ z K₁ K₂ ∨ (q₁ = q₂ ∧ Ch6TSing p q₂ z K₂ K₁)

section Swap

variable {G : Type} [Group G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem Ch6Setup.swap (h : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hq : q₁ = q₂) :
    Ch6Setup G Gs q₁ q₂ z K₂ K₁ F₂ F₁ where
  S_iso := h.S_iso
  central := h.central
  one_class := h.one_class
  O2prime := h.O2prime
  finite₁ := h.finite₂
  finite₂ := h.finite₁
  card₁ := h.card₂.trans hq.symm
  card₂ := h.card₁.trans hq
  odd₁ := h.odd₁
  odd₂ := h.odd₂
  le := le_of_eq hq.symm
  five := h.five
  iso₁ := h.iso₂
  iso₂ := h.iso₁
  comm := fun x hx y hy => (h.comm y hy x hx).symm
  inter_card := by rw [inf_comm]; exact h.inter_card
  le_centralizer := by rw [sup_comm]; exact h.le_centralizer
  le_residual := by rw [sup_comm]; exact h.le_residual
  index_two := by rw [sup_comm]; exact h.index_two
  z_mem₁ := h.z_mem₂
  z_mem₂ := h.z_mem₁
  inter_eq := by rw [inf_comm]; exact h.inter_eq
  model := by
    obtain ⟨p, f, F, iF, fF, hp, hp2, hL, hcF, hs₁, hs₂⟩ := h.model
    exact ⟨p, f, F, iF, fF, hp, hp2, hL, hcF, hs₂, hs₁⟩

theorem Ch6Rem.swap {t : G} (h : Ch6Rem z K₁ K₂ F₁ F₂ t) : Ch6Rem z K₂ K₁ F₂ F₁ t where
  comm_z := h.comm_z
  sq := h.sq
  gen := by rw [sup_comm K₂ K₁]; exact h.gen
  diag₁ := h.diag₂
  diag₂ := h.diag₁

end Swap

@[expose] def Ch6T2Sec6' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ (N : T2N3 G) (u : G) (p : ℕ), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
              Ch6NumD p q₁ q₂ → Ch6TSing p q₂ z K₁ K₂ → Ch6Coord N.toT2N2.toT2N1 → Ch6Sec5 N u →
                ∃ P₀ P : Subgroup G, Ch6S6 (T2N4.toCh6 ⟨N, p, P₀, P⟩)

end CFSG.GH74.GLS.Stage4.Rest
