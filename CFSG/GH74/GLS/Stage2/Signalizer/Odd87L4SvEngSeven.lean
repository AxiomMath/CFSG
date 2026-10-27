module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sl2Triv

public section

open Subgroup CFSG CFSG.GH74.GLS.Stage4.Hex CFSG.OrderReductions.FrattiniAutomorphisms
  CFSG.RankThree.PartOne.FTL
open scoped commutatorElement IsMulCommutative

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem sl2U_pow_seven {F : Type} [Field F] [Finite F] (hF : Nat.card F = 7) (c : F) :
    sl2U c ^ 7 = 1 := by
  have h : (7 : ℕ) • c = 0 := by
    rw [← hF]
    exact card_nsmul_eq_zero'
  rw [CFSG.GH74.GLS.Stage4.Rest.sl2U_pow, h, sl2U_zero]

theorem not_seven_dvd_card_GL_three {d : ℕ} (hd : d ≤ 4) :
    ¬ 7 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) := by
  rw [Matrix.card_GL_field]
  interval_cases d <;> decide

theorem rep_unip_trivial_of_card_seven {F : Type} [Field F] [Finite F] (hF : Nat.card F = 7)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (hdim : Module.finrank (ZMod 3) V ≤ 4) (ρ : Representation (ZMod 3) (SL2 F) V) (c : F) :
    ρ (sl2U c) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let b : Module.Basis (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) V :=
    Module.finBasisOfFinrankEq (ZMod 3) V rfl
  let m : (V →ₗ[ZMod 3] V) →* Matrix (Fin (Module.finrank (ZMod 3) V)) (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom
  let φ : SL2 F →* Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) :=
    (Units.map m).comp ρ.toHomUnits
  have hpow : φ (sl2U c) ^ 7 = 1 := by rw [← map_pow, sl2U_pow_seven hF, map_one]
  have hord : orderOf (φ (sl2U c)) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) V)) (ZMod 3)) :=
    orderOf_dvd_natCard _
  have h7 : orderOf (φ (sl2U c)) ∣ 7 := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf (φ (sl2U c)) = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h7 with h | h
    · exact h
    · rw [h] at hord
      exact absurd hord (not_seven_dvd_card_GL_three hdim)
  have hone : φ (sl2U c) = 1 := orderOf_eq_one_iff.1 h1
  have hm : m (ρ (sl2U c)) = 1 := by
    have := congrArg (fun x : Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) =>
      (x : Matrix (Fin (Module.finrank (ZMod 3) V)) (Fin (Module.finrank (ZMod 3) V)) (ZMod 3))) hone
    simpa [φ, m] using this
  exact (LinearMap.toMatrixAlgEquiv b).injective (by simpa [m] using hm)


theorem sl2_centralizes_seven_three {A : Type} [Group A] [Finite A] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 7) (ι : SL2 F →* A) {X : Subgroup A} (hX : IsPGroup 3 ↥X)
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) (hle : padicValNat 3 (Nat.card ↥X) ≤ 4) :
    ∀ g, ∀ x ∈ X, ι g * x = x * ι g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : ¬ 3 ∣ Nat.card F := by rw [hF]; decide
  have : Fact (IsPGroup 3 X) := ⟨hX⟩
  by_cases hU : ∃ c : F, frattiniRepOf (p := 3) ι X hnorm (sl2U c) ≠ 1
  · exfalso
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3)
      (V := Additive (↥X ⧸ frattini ↥X))
    rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive (↥X ⧸ frattini ↥X) ≃ _)] at hcard
    have hdvd : 3 ^ Module.finrank (ZMod 3) (Additive (↥X ⧸ frattini ↥X)) ∣ Nat.card X :=
      hcard ▸ Subgroup.card_quotient_dvd_card (frattini ↥X)
    have h2 := (padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd
    obtain ⟨c, hc⟩ := hU
    exact hc (rep_unip_trivial_of_card_seven hF (h2.trans hle) _ c)
  · push Not at hU
    have hL : ∀ c : F, frattiniRepOf (p := 3) ι X hnorm (sl2L c) = 1 := by
      intro c
      rw [sl2L_eq_conj, map_mul, map_mul, hU (-c), mul_one, ← map_mul, mul_inv_cancel, map_one]
    have hpowU : ∀ c : F, sl2U c ^ Nat.card F = 1 := by
      intro c
      rw [CFSG.GH74.GLS.Stage4.Rest.sl2U_pow, card_nsmul_eq_zero', sl2U_zero]
    have hpowL : ∀ c : F, sl2L c ^ Nat.card F = 1 := by
      intro c
      rw [sl2L_pow, card_nsmul_eq_zero', sl2L_zero]
    have hmem := sl2_hom_mem ι (centralizer (X : Set A))
      (fun c => centralizes_of_frattiniRepOf_eq_one hpq ι hnorm (hpowU c) (hU c))
      (fun c => centralizes_of_frattiniRepOf_eq_one hpq ι hnorm (hpowL c) (hL c))
    intro g x hx
    exact ((Subgroup.mem_centralizer_iff.1 (hmem g)) x hx).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
