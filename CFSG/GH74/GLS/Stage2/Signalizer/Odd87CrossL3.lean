module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossSL2Grp
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossArith
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

open Subgroup CFSG.GH74.GLS.Stage4.Hex
open scoped commutatorElement IsMulCommutative

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section FalseL3

variable {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

theorem false_of_sl2_psl3 (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A) {X K : Subgroup A} (hXK : X ≤ K)
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) (hnorm : ∀ g, ι g ∈ normalizer (X : Set A))
    (hcomm : ⁅X, zpowers (ι (-1))⁆ = X) (hK : Nat.card K = psl3Order (Nat.card F)) : False := by
  have h1 := le_padicValNat_of_sl2_of_le hp2 hodd hpq ι hXK hX hX1 hnorm hcomm
  have h2 := padicValNat_psl3Order_lt hodd h5 hp2 hpq
  rw [hK] at h1
  omega

theorem false_of_sl2_psu3_of_ne (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F)
    (hexc : ¬ (Nat.card F = 5 ∧ p = 3)) (ι : SL2 F →* A) {X K : Subgroup A} (hXK : X ≤ K)
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) (hnorm : ∀ g, ι g ∈ normalizer (X : Set A))
    (hcomm : ⁅X, zpowers (ι (-1))⁆ = X) (hK : Nat.card K = psu3Order (Nat.card F)) : False := by
  have h1 := le_padicValNat_of_sl2_of_le hp2 hodd hpq ι hXK hX hX1 hnorm hcomm
  rcases padicValNat_psu3Order_lt hodd h5 hp2 hpq with h2 | h2
  · rw [hK] at h1
    omega
  · exact hexc h2

end FalseL3


section Five

theorem sl2U_pow_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5) (c : F) :
    sl2U c ^ 5 = 1 := by
  have h : (5 : ℕ) • c = 0 := by
    rw [← hF]
    exact card_nsmul_eq_zero'
  rw [CFSG.GH74.GLS.Stage4.Rest.sl2U_pow, h, sl2U_zero]

theorem rep_unip_trivial_of_card_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (hdim : Module.finrank (ZMod 3) V = 2)
    (ρ : Representation (ZMod 3) (SL2 F) V) (c : F) : ρ (sl2U c) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Module.Finite (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) (ZMod 3) V := Module.finBasisOfFinrankEq (ZMod 3) V hdim
  let m : (V →ₗ[ZMod 3] V) →* Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom
  let φ : SL2 F →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
    (Units.map m).comp ρ.toHomUnits
  have hpow : φ (sl2U c) ^ 5 = 1 := by rw [← map_pow, sl2U_pow_five hF, map_one]
  have hord : orderOf (φ (sl2U c)) ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    orderOf_dvd_natCard _
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    decide
  have h5 : orderOf (φ (sl2U c)) ∣ 5 := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf (φ (sl2U c)) = 1 := by
    rw [hcard] at hord
    have := Nat.dvd_gcd h5 hord
    simpa using this
  have hone : φ (sl2U c) = 1 := orderOf_eq_one_iff.1 h1
  have hm : m (ρ (sl2U c)) = 1 := by
    have := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) hone
    simpa [φ, m] using this
  exact (LinearMap.toMatrixAlgEquiv b).injective (by simpa [m] using hm)

end Five

section Exceptional

variable {A : Type} [Group A] [Finite A]

theorem false_of_sl2_psu3_five_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    (ι : SL2 F →* A) {X K : Subgroup A} (hXK : X ≤ K) (hX : IsPGroup 3 X) (hX1 : X ≠ ⊥)
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) (hcomm : ⁅X, zpowers (ι (-1))⁆ = X)
    (hK : Nat.card K = psu3Order 5) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 X) := ⟨hX⟩
  have : Nontrivial (Additive (↥X ⧸ frattini ↥X)) := by
    have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hX1
    have hne : frattini ↥X ≠ ⊤ := by
      obtain h | ⟨M, hM, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥X)
      · exact absurd h bot_ne_top
      · intro htop
        exact hM.1 (top_le_iff.mp (htop ▸ frattini_le_coatom hM))
    have : Nontrivial (↥X ⧸ frattini ↥X) := (QuotientGroup.nontrivial_iff (N := frattini ↥X)).2 hne
    infer_instance
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hpq : ¬ 3 ∣ Nat.card F := by rw [hF]; decide
  have hz : ∀ v, frattiniRepOf (p := 3) ι X hnorm (-1) v = -v :=
    frattiniRepOf_neg ι X hnorm neg_one_mul_neg_one_sl2 hcomm
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨h1, -, -⟩ := sl2_neg_dim hp2 hodd hpq (frattiniRepOf (p := 3) ι X hnorm) hz
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive (↥X ⧸ frattini ↥X))
  rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive (↥X ⧸ frattini ↥X) ≃ _)] at hcard
  have hdvd : 3 ^ Module.finrank (ZMod 3) (Additive (↥X ⧸ frattini ↥X)) ∣ Nat.card K := by
    rw [← hcard]
    exact (Subgroup.card_quotient_dvd_card (frattini ↥X)).trans (Subgroup.card_dvd_of_le hXK)
  have hle : Module.finrank (ZMod 3) (Additive (↥X ⧸ frattini ↥X)) ≤ 2 := by
    have := (padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd
    rwa [hK, padicValNat_psu3Order_five_three] at this
  have h2 : Module.finrank (ZMod 3) (Additive (↥X ⧸ frattini ↥X)) = 2 := by
    rw [hF] at h1
    omega
  obtain ⟨c, hc⟩ := unip_nontrivial_of_neg hp2 (frattiniRepOf (p := 3) ι X hnorm) hz
  exact hc (rep_unip_trivial_of_card_five hF h2 _ c)

theorem false_of_sl2_psu3 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A)
    {X K : Subgroup A} (hXK : X ≤ K) (hX : IsPGroup p X) (hX1 : X ≠ ⊥)
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) (hcomm : ⁅X, zpowers (ι (-1))⁆ = X)
    (hK : Nat.card K = psu3Order (Nat.card F)) : False := by
  by_cases hexc : Nat.card F = 5 ∧ p = 3
  · obtain ⟨hF, rfl⟩ := hexc
    rw [hF] at hK
    exact false_of_sl2_psu3_five_three hF ι hXK hX hX1 hnorm hcomm hK
  · exact false_of_sl2_psu3_of_ne hp2 hodd h5 hpq hexc ι hXK hX hX1 hnorm hcomm hK

end Exceptional

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
