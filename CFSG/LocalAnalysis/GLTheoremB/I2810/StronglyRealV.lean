module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LieType.ChevTwo.Inversion

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

theorem strongly_real_small_comm {V : Type} [CommGroup V]
    [Finite V] (h2 : ∀ v : V, v * v = 1)
    {τ y : MulAut V} (hτ : τ * τ = 1) (hinv : τ * y * τ⁻¹ = y⁻¹)
    (hy : Odd (orderOf y)) (hidx : (fixV' (Subgroup.zpowers τ)).index ≤ 4) :
    orderOf y = 1 ∨ orderOf y = 3 ∨ orderOf y = 5 := by
  classical
  have hV : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    have := h2 (Additive.toMul x)
    rw [two_nsmul]
    exact this
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule hV
  haveI : Finite (Additive V) := inferInstanceAs (Finite V)
  let Φ : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun e => (MulEquiv.toAdditive e).toLinearEquiv fun c x =>
        ZMod.map_smul (MulEquiv.toAdditive e) c x
      map_one' := LinearEquiv.ext fun w => rfl
      map_mul' := fun σ τ => LinearEquiv.ext fun w => rfl }
  have hΦapp : ∀ (e : MulAut V) (v : V), Φ e (Additive.ofMul v) = Additive.ofMul (e v) :=
    fun e v => rfl
  have hΦinj : Function.Injective Φ := by
    intro e e' h
    ext v
    have := congrArg (fun f : Additive V ≃ₗ[ZMod 2] Additive V => f (Additive.ofMul v)) h
    exact Additive.ofMul.injective this
  have hτ' : (Φ τ) ^ 2 = 1 := by rw [pow_two, ← map_mul, hτ, map_one]
  have hinv' : Φ τ * Φ y * (Φ τ)⁻¹ = (Φ y)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, hinv]
  have hord : orderOf (Φ y) = orderOf y := orderOf_injective Φ hΦinj y
  have hodd : Odd (orderOf (Φ y)) := hord ▸ hy
  have hfixmem : ∀ v : V, v ∈ fixV' (Subgroup.zpowers τ) ↔ τ v = v := by
    intro v
    constructor
    · intro hv
      exact hv τ (Subgroup.mem_zpowers τ)
    · intro hv x hx
      have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer (MulAut V) v :=
        (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hv)
      have := hle hx
      rwa [MulAction.mem_stabilizer_iff] at this
  have hkermem : ∀ w : Additive V,
      w ∈ LinearMap.ker (((Φ τ : Additive V ≃ₗ[ZMod 2] Additive V) : Additive V →ₗ[ZMod 2] Additive V) -
        LinearMap.id) ↔ τ (Additive.toMul w) = Additive.toMul w := by
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => Additive.toMul.injective h⟩
  have hcard : Nat.card (LinearMap.ker (((Φ τ : Additive V ≃ₗ[ZMod 2] Additive V) :
      Additive V →ₗ[ZMod 2] Additive V) - LinearMap.id)) = Nat.card (fixV' (Subgroup.zpowers τ)) :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun w => (hkermem w).trans (hfixmem _).symm)
  have hoff : Nat.card (Additive V) ≤ 4 * Nat.card (LinearMap.ker
      (((Φ τ : Additive V ≃ₗ[ZMod 2] Additive V) : Additive V →ₗ[ZMod 2] Additive V) -
        LinearMap.id)) := by
    rw [hcard]
    have h1 : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
    have h2' := Subgroup.card_mul_index (fixV' (Subgroup.zpowers τ))
    rw [h1, ← h2']
    calc Nat.card (fixV' (Subgroup.zpowers τ)) * (fixV' (Subgroup.zpowers τ)).index
        ≤ Nat.card (fixV' (Subgroup.zpowers τ)) * 4 := Nat.mul_le_mul_left _ hidx
      _ = 4 * Nat.card (fixV' (Subgroup.zpowers τ)) := Nat.mul_comm _ _
  have key := CFSG.LieType.ChevTwo.odd_inverted_of_offender (Φ τ) (Φ y) hτ' hinv' hodd hoff
  rwa [hord] at key

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
