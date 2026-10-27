module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Fixed

public section

namespace CFSG.LocalAnalysis.ComponentInitial

theorem finite_field_automorphism_fixed_field_cardinality {F : Type*} [Field F] {p n : ℕ}
    (hp : p.Prime) (hn : 1 ≤ n) (hF : Nat.card F = p ^ n) :
    ∃ σ : F ≃+* F, (∀ a, σ a = a ^ p) ∧ orderOf σ = n ∧ Subgroup.zpowers σ = ⊤ ∧
      Nat.card (F ≃+* F) = n ∧
      ∀ A : Subgroup (F ≃+* F), Nat.card A ∣ n ∧
        ∃ S : Subfield F, (S : Set F) = {a | ∀ τ ∈ A, τ a = a} ∧
          Nat.card S = p ^ (n / Nat.card A) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := finite_field_prime_power_characteristic hp hn hF
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact (pow_pos hp.pos n).ne')
  have : Fintype F := Fintype.ofFinite F
  let : Algebra (ZMod p) F := ZMod.algebra F p
  have hfin : Module.finrank (ZMod p) F = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)
    rw [hF, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  have hfix : ∀ (σ : F ≃+* F) (x : ZMod p),
      σ (algebraMap (ZMod p) F x) = algebraMap (ZMod p) F x := fun σ x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((σ : F →+* F).comp (algebraMap (ZMod p) F))
      (algebraMap (ZMod p) F)) x
  let e : Gal(F/ZMod p) ≃* (F ≃+* F) :=
    { toFun := AlgEquiv.toRingEquiv
      invFun := fun σ => AlgEquiv.ofRingEquiv (hfix σ)
      left_inv := fun _ => AlgEquiv.ext fun _ => rfl
      right_inv := fun _ => RingEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcard : Nat.card (F ≃+* F) = n := by
    rw [← Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank, hfin]
  let σ := e (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F)
  have hσ : ∀ a, σ a = a ^ p := fun a => by
    change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F a = a ^ p
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ZMod.card]
  have hord : orderOf σ = n := by
    rw [MulEquiv.orderOf_eq, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hfin]
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  refine ⟨σ, hσ, hord, (Subgroup.card_eq_iff_eq_top _).mp (by rw [Nat.card_zpowers, hord, hcard]),
    hcard, fun A => ?_⟩
  have : Fintype A := Fintype.ofFinite A
  have hA := FixedPoints.finrank_eq_card A F
  have hS : (FixedPoints.subfield A F : Set F) = {a | ∀ τ ∈ A, τ a = a} := by
    ext a
    exact ⟨fun ha τ hτ => ha ⟨τ, hτ⟩, fun ha τ => ha τ τ.2⟩
  have hcardF := Module.natCard_eq_pow_finrank (K := FixedPoints.subfield A F) (V := F)
  rw [hA, hF, ← Nat.card_eq_fintype_card] at hcardF
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hdvd : Nat.card (FixedPoints.subfield A F) ∣ p ^ n :=
    hcardF ▸ dvd_pow_self _ hApos.ne'
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rw [hk, ← pow_mul] at hcardF
  have hnk : n = k * Nat.card A := Nat.pow_right_injective hp.two_le hcardF
  refine ⟨⟨k, by rw [hnk, mul_comm]⟩, FixedPoints.subfield A F, hS, ?_⟩
  rw [hk, Nat.div_eq_of_eq_mul_left hApos hnk]

end CFSG.LocalAnalysis.ComponentInitial
