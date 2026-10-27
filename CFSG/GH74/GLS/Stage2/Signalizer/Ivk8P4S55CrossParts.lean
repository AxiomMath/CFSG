module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Hyp89

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

@[expose] def Concl89 (p : ℕ) {Γ : Type} [Group Γ] (K : Subgroup Γ) (r : ℕ) : Prop :=
  r = p ∨ (p = 3 ∧ HasSL2Model ↥K (fun q => q = 5))

@[expose] def Cross89 : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ),
    Hyp89 p ρ K a → ∀ r : ℕ, OddChev r (↥K ⧸ center ↥K) → Concl89 p K r

@[expose] def Cross89Lt (n : ℕ) : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ),
    Hyp89 p ρ K a → Nat.card ↥K < n → ∀ r : ℕ, OddChev r (↥K ⧸ center ↥K) → Concl89 p K r

theorem cross55_of_cross89 (h : Cross89) : Cross55 :=
  fun p Γ _ _ V _ _ _ ρ K a _ hf r hr => h p Γ V ρ K a hf.toHyp89 r hr

@[expose] def OddChevHigh (r : ℕ) (Y : Type) [Group Y] : Prop :=
  r.Prime ∧ r ≠ 2 ∧
    (FL3d r Y ∨ FU3d r Y ∨ FSp4d r Y ∨ FG2d r Y ∨ FD4d r Y ∨ FL4d r Y ∨ FU4d r Y ∨ FReed r Y)

@[expose] def StepL2 : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ),
    Hyp89 p ρ K a → Cross89Lt (Nat.card ↥K) → ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p →
      FL2d r (↥K ⧸ center ↥K) → p = 3 ∧ HasSL2Model ↥K (fun q => q = 5)

@[expose] def StepH3 : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ),
    Hyp89 p ρ K a → Cross89Lt (Nat.card ↥K) → p = 3 → ∀ r : ℕ,
      OddChevHigh r (↥K ⧸ center ↥K) → r ≠ p → False

@[expose] def StepH5 : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ),
    Hyp89 p ρ K a → Cross89Lt (Nat.card ↥K) → 5 ≤ p → ∀ r : ℕ,
      OddChevHigh r (↥K ⧸ center ↥K) → r ≠ p → False

theorem cross89_of_steps (hL : StepL2) (h3 : StepH3) (h5 : StepH5) : Cross89 := by
  have key : ∀ n : ℕ, Cross89Lt n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p Γ _ _ V _ _ _ ρ K a hK hn r hr
      have hIH : Cross89Lt (Nat.card ↥K) := ih _ hn
      by_cases hrp : r = p
      · exact Or.inl hrp
      · obtain ⟨hrpr, hr2, hY⟩ := hr
        by_cases hL2 : FL2d r (↥K ⧸ center ↥K)
        · exact Or.inr (hL p Γ V ρ K a hK hIH r hrpr hr2 hrp hL2)
        · have hH : OddChevHigh r (↥K ⧸ center ↥K) := ⟨hrpr, hr2, hY.resolve_left hL2⟩
          have hp : p = 3 ∨ 5 ≤ p := by
            have h2 := hK.prime.two_le
            have h4 : p ≠ 4 := by
              rintro rfl
              exact absurd hK.prime (by norm_num)
            have h5 := hK.odd
            omega
          rcases hp with hp3 | hp5
          · exact (h3 p Γ V ρ K a hK hIH hp3 r hH hrp).elim
          · exact (h5 p Γ V ρ K a hK hIH hp5 r hH hrp).elim
  intro p Γ _ _ V _ _ _ ρ K a hK r hr
  exact key (Nat.card ↥K + 1) p Γ V ρ K a hK (Nat.lt_succ_self _) r hr

theorem cross55_of_steps (hL : StepL2) (h3 : StepH3) (h5 : StepH5) : Cross55 :=
  cross55_of_cross89 (cross89_of_steps hL h3 h5)

@[expose] def CrossE1 : Prop :=
  ∀ (r : ℕ) (Y : Type) [Group Y] [Finite Y], OddChev r Y → ∀ b : MulAut Y, b ≠ 1 →
    ¬ r ∣ orderOf b → (∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → ∀ x ∈ E, b x = x) →
    ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → E = ⊥

@[expose] def CrossE2 : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ),
    Hyp89 p ρ K a → ∃ k ∈ K, ¬ IsPGroup p ↥(closure ({a, k * a * k⁻¹} : Set Γ)) ∧
      (∀ k' ∈ K, ¬ IsPGroup p ↥(closure ({a, k' * a * k'⁻¹} : Set Γ)) →
        Nat.card ↥(closure ({a, k * a * k⁻¹} : Set Γ)) ≤
          Nat.card ↥(closure ({a, k' * a * k'⁻¹} : Set Γ))) ∧
      ∃ (N : Subgroup ↥(closure ({a, k * a * k⁻¹} : Set Γ))) (_ : N.Normal),
        HasSL2Model (↥(closure ({a, k * a * k⁻¹} : Set Γ)) ⧸ N) (fun q => q = p)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
