module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2R2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

section Fix

variable {K : Type*} [Group K]

@[expose] def l2opFix (f : MulAut K) : Subgroup K :=
  MonoidHom.eqLocus f.toMonoidHom (MonoidHom.id K)

theorem mem_l2opFix {f : MulAut K} {x : K} : x ∈ l2opFix f ↔ f x = x :=
  Iff.rfl

theorem l2op_glapPrimeCore_eq_bot_of_mulEquiv {p : ℕ} {H H' : Type*} [Group H] [Group H']
    (e : H ≃* H') (h : GLAPPrimeCore p H' = ⊥) : GLAPPrimeCore p H = ⊥ := by
  rw [GLAPPrimeCore, CFSG.pPrimeCore, sSup_eq_bot] at h ⊢
  rintro N ⟨hN, hc⟩
  refine (Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom) e.injective).1
    (h _ ⟨hN.map _ e.surjective, ?_⟩)
  rwa [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem l2op_mul_conj_mul_inv (f : MulAut K) (k : K) :
    f * MulAut.conj k * f⁻¹ = MulAut.conj (f k) := by
  ext x
  simp [MulAut.conj_apply]

theorem l2op_conj_injective (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ : MulAut K => φ x) hab
    simp only [MulAut.conj_apply] at hx
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * b * b⁻¹ * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * b * b⁻¹ * a := by rw [hx]
      _ = b⁻¹ * a * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem l2op_innerAut_inf_centralizer (hZ : Subgroup.center K = ⊥) (f : MulAut K) :
    innerAut K ⊓ Subgroup.centralizer ({f} : Set (MulAut K)) =
      (l2opFix f).map (MulAut.conj : K →* MulAut K) := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨k, rfl⟩, hc⟩
    refine ⟨k, ?_, rfl⟩
    rw [mem_l2opFix]
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    refine l2op_conj_injective hZ ?_
    rw [← l2op_mul_conj_mul_inv, ← hc, mul_inv_cancel_right]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := l2op_mul_conj_mul_inv f k
    rw [mem_l2opFix.1 hk] at h
    calc MulAut.conj k * f = f * MulAut.conj k * f⁻¹ * f := by rw [h]
      _ = f * MulAut.conj k := by group

theorem l2op_isLocallyBalancedAbs_of_fix [Finite K] (hZ : Subgroup.center K = ⊥)
    (h : ∀ D : Subgroup (MulAut K), IsElemAbelian 3 D → Nat.card D = 9 →
      ∃ f ∈ D, f ≠ 1 ∧ GLAPPrimeCore 3 ↥(l2opFix f) = ⊥ ∧
        ∀ y : MulAut K, (∀ x ∈ l2opFix f, y x = x) → Nat.Coprime 3 (orderOf y) → y = 1) :
    IsLocallyBalancedAbs 3 2 K := by
  refine isLocallyBalancedAbs_three_two_of_outer fun D hD hcard => ?_
  obtain ⟨f, hfD, hf1, hi, hii⟩ := h D hD hcard
  refine ⟨f, hfD, hf1, ?_, ?_⟩
  · rw [l2op_innerAut_inf_centralizer hZ f, GLAPPrimeCoreOf,
      Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    exact l2op_glapPrimeCore_eq_bot_of_mulEquiv
      ((l2opFix f).equivMapOfInjective _ (l2op_conj_injective hZ)).symm hi
  · intro y hy hcop
    refine hii y (fun x hx => ?_) hcop
    have hmem : MulAut.conj x ∈ innerAut K ⊓ Subgroup.centralizer ({f} : Set (MulAut K)) := by
      rw [l2op_innerAut_inf_centralizer hZ f]
      exact ⟨x, hx, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.1 hy) _ hmem
    refine l2op_conj_injective hZ ?_
    rw [← l2op_mul_conj_mul_inv, ← hcomm, mul_inv_cancel_right]

theorem l2opFix_conj (c f : MulAut K) :
    l2opFix (c * f * c⁻¹) = (l2opFix f).map c.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨c⁻¹ x, ?_, by simp⟩
    rw [mem_l2opFix] at hx ⊢
    have h1 : c (f (c⁻¹ x)) = x := hx
    calc f (c⁻¹ x) = c⁻¹ (c (f (c⁻¹ x))) := by simp
      _ = c⁻¹ x := by rw [h1]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_l2opFix] at hz ⊢
    simp [MulAut.mul_apply, hz]

theorem l2op_fix_conditions_conj (c f : MulAut K)
    (hi : GLAPPrimeCore 3 ↥(l2opFix f) = ⊥)
    (hii : ∀ y : MulAut K, (∀ x ∈ l2opFix f, y x = x) → Nat.Coprime 3 (orderOf y) → y = 1) :
    GLAPPrimeCore 3 ↥(l2opFix (c * f * c⁻¹)) = ⊥ ∧
      ∀ y : MulAut K, (∀ x ∈ l2opFix (c * f * c⁻¹), y x = x) →
        Nat.Coprime 3 (orderOf y) → y = 1 := by
  refine ⟨?_, fun y hy hcop => ?_⟩
  · rw [l2opFix_conj]
    exact l2op_glapPrimeCore_eq_bot_of_mulEquiv
      ((l2opFix f).equivMapOfInjective _ c.injective).symm hi
  · have h1 : c⁻¹ * y * c = 1 := by
      refine hii _ (fun x hx => ?_) ?_
      · have hcx : c x ∈ l2opFix (c * f * c⁻¹) := by
          rw [l2opFix_conj]
          exact ⟨x, hx, rfl⟩
        have := hy _ hcx
        simp [MulAut.mul_apply, this]
      · have h := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) y
        rw [MulAut.conj_apply, inv_inv] at h
        rwa [h]
    calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

end Fix

end CFSG.HardMathSupport.Solomon.Coordinator
