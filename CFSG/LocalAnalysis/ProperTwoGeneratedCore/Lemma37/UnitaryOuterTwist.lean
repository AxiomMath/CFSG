module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

variable {R : Type*} [Group R] [Finite R] {U : Subgroup R}

omit [Finite R] in
@[expose] def twistSubgroup (U : Subgroup R) (hUc : ∀ u ∈ U, ∀ x : R, u * x = x * u)
    (ψ : R →* R) : Subgroup R where
  carrier := {x | x⁻¹ * ψ x ∈ U}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : (a * b)⁻¹ * ψ (a * b) = (a⁻¹ * ψ a) * (b⁻¹ * ψ b) := by
      rw [map_mul, mul_inv_rev]
      calc b⁻¹ * a⁻¹ * (ψ a * ψ b) = b⁻¹ * (a⁻¹ * ψ a) * ψ b := by group
        _ = (a⁻¹ * ψ a) * b⁻¹ * ψ b := by rw [← hUc _ ha b⁻¹]
        _ = (a⁻¹ * ψ a) * (b⁻¹ * ψ b) := by group
    rw [this]
    exact U.mul_mem ha hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have : a⁻¹⁻¹ * ψ a⁻¹ = a * (a⁻¹ * ψ a)⁻¹ * a⁻¹ := by rw [map_inv]; group
    rw [this, ← hUc _ (U.inv_mem ha) a]
    simpa using U.inv_mem ha

theorem card_mul_apply_eq_one (hUc : ∀ u ∈ U, ∀ x : R, u * x = x * u)
    (hsq : ∀ x : R, x ^ 2 ∈ U) (ψ : R →* R) (hψψ : ∀ x, ψ (ψ x) = x)
    (hψU : ∀ u ∈ U, ψ u = u) (hfix : ∀ x, ψ x = x → x ∈ U) {q : ℕ}
    (hR : Nat.card R = q ^ 3) (hU : Nat.card U = q) :
    Nat.card {x : R // x * ψ x = 1} = q ^ 2 := by
  have hq : 0 < q := by rw [← hU]; exact Nat.card_pos
  set Y := twistSubgroup U hUc ψ with hYdef
  let δ : Y →* U :=
    { toFun := fun y => ⟨(y : R)⁻¹ * ψ y, y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((a : R) * b)⁻¹ * ψ ((a : R) * b) = ((a : R)⁻¹ * ψ a) * ((b : R)⁻¹ * ψ b)
        rw [map_mul, mul_inv_rev]
        calc (b : R)⁻¹ * (a : R)⁻¹ * (ψ a * ψ b) = (b : R)⁻¹ * ((a : R)⁻¹ * ψ a) * ψ b := by group
          _ = ((a : R)⁻¹ * ψ a) * (b : R)⁻¹ * ψ b := by rw [← hUc _ a.2 (b : R)⁻¹]
          _ = ((a : R)⁻¹ * ψ a) * ((b : R)⁻¹ * ψ b) := by group }
  have hker : Nat.card δ.ker ≤ q := by
    rw [← hU]
    refine Nat.card_le_card_of_injective (fun y => (⟨y.1.1, hfix _ ?_⟩ : U)) ?_
    · have h := y.2
      rw [MonoidHom.mem_ker] at h
      have h' := congrArg Subtype.val h
      change ((y : Y) : R)⁻¹ * ψ ((y : Y) : R) = 1 at h'
      exact (inv_mul_eq_one.mp h').symm
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  have hrange : Nat.card δ.range ≤ q := by
    rw [← hU]
    exact Nat.card_le_card_of_injective (fun y => (y : U)) Subtype.val_injective
  have hY : Nat.card Y ≤ q ^ 2 := by
    have h := δ.ker.card_mul_index
    rw [Subgroup.index_ker] at h
    rw [← h, pow_two]
    exact Nat.mul_le_mul hker hrange
  have hle : Nat.card {x : R // x * ψ x = 1} ≤ Nat.card Y := by
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1, ?_⟩ : Y)) ?_
    · change x.1⁻¹ * ψ x.1 ∈ U
      rw [show ψ x.1 = x.1⁻¹ from eq_inv_of_mul_eq_one_right x.2, ← mul_inv_rev, ← pow_two]
      exact U.inv_mem (hsq _)
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext h
  have : U.Normal := ⟨fun n hn g => by rw [← hUc n hn g, mul_inv_cancel_right]; exact hn⟩
  let θ : R → {x : R // x * ψ x = 1} := fun y => ⟨y * (ψ y)⁻¹, by
    rw [map_mul, map_inv, hψψ]; group⟩
  have hθ : ∀ a b : R, (QuotientGroup.leftRel U) a b → θ a = θ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    apply Subtype.ext
    change a * (ψ a)⁻¹ = b * (ψ b)⁻¹
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb, map_mul, hψU _ hab]
    group
  let θ' : R ⧸ U → {x : R // x * ψ x = 1} := Quotient.lift θ hθ
  have hθ' : Function.Injective θ' := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have h := congrArg Subtype.val hab
    change a * (ψ a)⁻¹ = b * (ψ b)⁻¹ at h
    refine QuotientGroup.eq.mpr (hfix _ ?_)
    rw [map_mul, map_inv]
    calc (ψ a)⁻¹ * ψ b = a⁻¹ * (a * (ψ a)⁻¹) * ψ b := by group
      _ = a⁻¹ * (b * (ψ b)⁻¹) * ψ b := by rw [h]
      _ = a⁻¹ * b := by group
  have hV : Nat.card (R ⧸ U) = q ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    rw [hR, hU] at h
    have : q ^ 3 = q ^ 2 * q := by ring
    exact Nat.eq_of_mul_eq_mul_right hq (h.symm.trans this)
  have hge : q ^ 2 ≤ Nat.card {x : R // x * ψ x = 1} := by
    rw [← hV]
    exact Nat.card_le_card_of_injective θ' hθ'
  omega

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
