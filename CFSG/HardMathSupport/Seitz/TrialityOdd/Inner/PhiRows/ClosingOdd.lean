module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.MaxL
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBPhi3

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

open CFSG.LieType.Steinberg.TwistedD4

section ClosingOdd


theorem longTorusClosing_of_fields
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) : LongTorusClosing σ.toRingHom := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hq3 : 3 ≤ ℓ ^ f := by
    have h3 : ℓ ≠ 2 := hℓ2
    have : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    calc 3 ≤ ℓ := this
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσ'
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at this
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  have hFcard : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    card_fixedField_of_cube σ.toRingHom hq2 hK hσ'
  have ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x : fixedField σ.toRingHom, x = 0 ∨ x = 1 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (hcon (Units.mk0 x hx))
    have : Nat.card (fixedField σ.toRingHom) ≤ 2 := by
      have hsub : (Set.univ : Set (fixedField σ.toRingHom)) ⊆ {0, 1} := fun x _ => by
        rcases hall x with h | h
        · exact Or.inl h
        · exact Or.inr h
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ] at h1
      exact h1.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    omega
  intro H hL hT ⟨y, hy, hyN⟩
  exact eq_top_of_not_normalizes hσ3 h2 ha H hL hT hy hyN

end ClosingOdd

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
