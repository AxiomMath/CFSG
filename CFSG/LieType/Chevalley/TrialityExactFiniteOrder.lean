module

public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders

section Orientation

variable {K : Type} [Field K]

theorem card_orbitField_D4_orientation {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {r : ℕ} (hr : r = 1 ∨ r = 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ r)) (a : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (orbitField TwistTag.D4 K σ a) = (ℓ ^ f) ^ (TwistTag.D4.orbit a).card := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨σ₁, hσ₁, -, hcard, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 hℓ hf K hK
  have hq3 : ∀ c : K, c ^ ((ℓ ^ f) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have heq : orbitField TwistTag.D4 K σ a = orbitField TwistTag.D4 K σ₁.toRingHom a := by
    ext c
    rw [mem_orbitField, mem_orbitField, pow_apply_eq_pow hσ, pow_apply_eq_pow (σ := σ₁.toRingHom)
      (fun c => hσ₁ c)]
    obtain ⟨n, hn⟩ := a
    have hn' : n < 2 := hn
    interval_cases n
    ·
      have h3 : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
      rw [h3]
      constructor <;> intro _
      · exact hq3 c
      · rcases hr with rfl | rfl
        · rw [pow_one]
          exact hq3 c
        · rw [show ((ℓ ^ f) ^ 2) ^ 3 = (ℓ ^ f) ^ 3 * (ℓ ^ f) ^ 3 by ring, pow_mul, hq3, hq3]
    ·
      have h1 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
      rw [h1, pow_one, pow_one]
      rcases hr with rfl | rfl
      · rw [pow_one]
      · constructor
        · intro h
          calc c ^ ℓ ^ f = (c ^ ((ℓ ^ f) ^ 2)) ^ ℓ ^ f := by rw [h]
            _ = c := by rw [← pow_mul, show (ℓ ^ f) ^ 2 * ℓ ^ f = (ℓ ^ f) ^ 3 by ring, hq3]
        · intro h
          rw [sq, pow_mul, h, h]
  rw [heq]
  exact hcard a

end Orientation

theorem triality_both_orientations_exact_finite_order
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ r)) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ) =
      (ℓ ^ f) ^ 12 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) *
        ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1) ∧
    Nat.card (graphFixedRootTorus TwistTag.D4 K σ) = ((ℓ ^ f) ^ 3 - 1) * (ℓ ^ f - 1) ∧
    Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ) = (ℓ ^ f) ^ 12 := by
  set q := ℓ ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hℓ.pos
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq3 : ∀ c : K, c ^ (q ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcardL := card_orbitField_D4_orientation hℓ hf hK hr hσ
  set σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩ with hσEdef
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσE3 : σE ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    rcases hr with rfl | rfl
    · rw [pow_one, show q * (q * q) = q ^ 3 by ring, hq3]
    · rw [show q ^ 2 * (q ^ 2 * q ^ 2) = q ^ 3 * q ^ 3 by ring, pow_mul, hq3, hq3]
  obtain ⟨-, ⟨e, -⟩, -, hL2, -⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K σE hσE3
  have hk : Nat.card (trialityFixedField K σE.toRingHom) = q := by
    rw [← hL2, hσE, hcardL ⟨1, by decide⟩, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by
      decide, pow_one]
  have hT : Nat.card (graphFixedRootTorus TwistTag.D4 K σ) = (q ^ 3 - 1) * (q - 1) := by
    rw [← hσE, ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_units, Nat.card_units, hK, hk]
  have hq : ∀ a, Nat.card (orbitField TwistTag.D4 K σ a) = q ^ (TwistTag.D4.orbit a).card :=
    hcardL
  have hU : Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ) = q ^ 12 := by
    rw [card_graphFixedPosUnipotent hsurj hq, ncard_posRoots_twistedD4]
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_D4, ncard_posRoots_twistedD4, ← graphFixedRootTorus_eq_compatTorus
    hsurj, hT, ordTrialityD4_eq q hq1, CFSG.Open.ordTrialityD4] at hC
  refine ⟨?_, hT, hU⟩
  rw [hC]
  ring

end CFSG.LieType.Chevalley
