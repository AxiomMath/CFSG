module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Local.FrobeniusGroupIndicatorRelation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {k A V : Type*} [Field k] [Group A] [AddCommGroup V] [Module k V]
variable {U W : Subgroup A}

theorem invariants_comp_subtype_eq_bot_iff (ρ : Representation k A V) (B : Subgroup A) :
    Representation.invariants (ρ.comp B.subtype) = ⊥ ↔ ∀ v : V, (∀ b ∈ B, ρ b v = v) → v = 0 := by
  rw [Submodule.eq_bot_iff]
  exact ⟨fun h v hv => h v ((Representation.mem_invariants _ v).2 fun b => hv b b.2),
    fun h v hv => h v fun b hb => (Representation.mem_invariants _ v).1 hv ⟨b, hb⟩⟩

theorem invariants_comp_subtype_conj_eq_bot (ρ : Representation k A V)
    (hV : Representation.invariants (ρ.comp W.subtype) = ⊥) (u : A) :
    Representation.invariants (ρ.comp (MulAut.conj u⁻¹ • W : Subgroup A).subtype) = ⊥ := by
  rw [invariants_comp_subtype_eq_bot_iff] at hV ⊢
  intro v hv
  have hz : ρ u v = 0 := by
    refine hV _ fun w hw => ?_
    have hmem : u⁻¹ * w * u ∈ (MulAut.conj u⁻¹ • W : Subgroup A) := by
      simpa using Subgroup.smul_mem_pointwise_smul w (MulAut.conj u⁻¹) W hw
    calc ρ w (ρ u v) = ρ (u * (u⁻¹ * w * u)) v := by
          rw [← Module.End.mul_apply, ← map_mul]; group
      _ = ρ u (ρ (u⁻¹ * w * u) v) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ u v := by rw [hv _ hmem]
  have h2 := congrArg (ρ u⁻¹) hz
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_zero] at h2

theorem invariants_comp_subtype_top_eq_bot (ρ : Representation k A V)
    (hV : Representation.invariants (ρ.comp W.subtype) = ⊥) :
    Representation.invariants (ρ.comp (⊤ : Subgroup A).subtype) = ⊥ := by
  rw [invariants_comp_subtype_eq_bot_iff] at hV ⊢
  exact fun v hv => hV v fun w _ => hv w (Subgroup.mem_top w)

private theorem indicator_mul_left {B : Subgroup A} {b : A} (hb : b ∈ B) (a : A) :
    (B : Set A).indicator (1 : A → ℕ) (b * a) = (B : Set A).indicator (1 : A → ℕ) a := by
  by_cases h : a ∈ B
  · rw [Set.indicator_of_mem (show b * a ∈ (B : Set A) from B.mul_mem hb h),
      Set.indicator_of_mem (show a ∈ (B : Set A) from h), Pi.one_apply, Pi.one_apply]
  · have hba : b * a ∉ B := fun hc => h ((B.mul_mem_cancel_left hb).mp hc)
    rw [Set.indicator_of_notMem hba, Set.indicator_of_notMem h]

section Fintype

variable [Fintype A]

private noncomputable def repSum (ρ : Representation k A V) : (A → ℕ) →+ (V →ₗ[k] V) :=
  AddMonoidHom.mk' (fun f => ∑ a : A, (f a : k) • ρ a) fun f g => by
    simp only [Pi.add_apply, Nat.cast_add, add_smul]
    exact Finset.sum_add_distrib

private theorem repSum_apply (ρ : Representation k A V) (f : A → ℕ) :
    repSum ρ f = ∑ a : A, (f a : k) • ρ a := (rfl)

private theorem repSum_apply_apply (ρ : Representation k A V) (f : A → ℕ) (v : V) :
    repSum ρ f v = ∑ a : A, (f a : k) • ρ a v := by
  rw [repSum_apply]; simp [LinearMap.sum_apply]

private theorem apply_repSum_indicator (ρ : Representation k A V) {B : Subgroup A} {b : A}
    (hb : b ∈ B) (v : V) :
    ρ b (repSum ρ ((B : Set A).indicator (1 : A → ℕ)) v)
      = repSum ρ ((B : Set A).indicator (1 : A → ℕ)) v := by
  rw [repSum_apply_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ fun a => ?_
  rw [map_smul, Equiv.coe_mulLeft, indicator_mul_left hb, ← Module.End.mul_apply, ← map_mul]

private theorem repSum_indicator_eq_zero (ρ : Representation k A V) {B : Subgroup A}
    (h : Representation.invariants (ρ.comp B.subtype) = ⊥) :
    repSum ρ ((B : Set A).indicator (1 : A → ℕ)) = 0 := by
  ext v
  rw [Submodule.eq_bot_iff] at h
  exact h _ ((Representation.mem_invariants _ _).2 fun b => apply_repSum_indicator ρ b.2 v)

private theorem repSum_indicator_singleton_one (ρ : Representation k A V) :
    repSum ρ (({(1 : A)} : Set A).indicator (1 : A → ℕ)) = 1 := by
  rw [repSum_apply, Finset.sum_eq_single (1 : A)]
  · rw [Set.indicator_of_mem (Set.mem_singleton (1 : A)), Pi.one_apply, Nat.cast_one, one_smul,
      map_one]
  · intro a _ ha
    rw [Set.indicator_of_notMem (by simpa using ha), Nat.cast_zero, zero_smul]
  · simp

private theorem repSum_indicator_coe_eq_natCard_smul (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (ρ : Representation k A V)
    (hV : Representation.invariants (ρ.comp W.subtype) = ⊥) :
    repSum ρ ((U : Set A).indicator (1 : A → ℕ)) = Nat.card U • (1 : V →ₗ[k] V) := by
  classical
  have _inst := Fintype.ofFinite U
  have key : Nat.card U • (({(1 : A)} : Set A).indicator (1 : A → ℕ))
        + ((⊤ : Subgroup A) : Set A).indicator (1 : A → ℕ)
      = (U : Set A).indicator (1 : A → ℕ)
        + ∑ u : U, ((MulAut.conj (u : A)⁻¹ • W : Subgroup A) : Set A).indicator (1 : A → ℕ) := by
    funext a
    have h := natCard_mul_indicator_one_add_indicator_top hU hUW hC a
    rw [finsum_eq_sum_of_fintype] at h
    simpa [Finset.sum_apply, smul_eq_mul] using h
  have hzero : ∑ u : U, repSum ρ
      (((MulAut.conj (u : A)⁻¹ • W : Subgroup A) : Set A).indicator (1 : A → ℕ))
      = (0 : V →ₗ[k] V) :=
    Finset.sum_eq_zero fun u _ =>
      repSum_indicator_eq_zero ρ (invariants_comp_subtype_conj_eq_bot ρ hV (u : A))
  have h2 := congrArg (repSum ρ) key
  rw [map_add, map_add, map_nsmul, map_sum, repSum_indicator_singleton_one,
    repSum_indicator_eq_zero ρ (invariants_comp_subtype_top_eq_bot ρ hV), add_zero, hzero,
    add_zero] at h2
  exact h2.symm

end Fintype

variable [Finite A]

theorem eq_one_of_invariants_comp_subtype_eq_bot (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hk : (Nat.card U : k) ≠ 0) (ρ : Representation k A V)
    (hV : Representation.invariants (ρ.comp W.subtype) = ⊥) {u : A} (hu : u ∈ U) :
    ρ u = 1 := by
  classical
  have _inst := Fintype.ofFinite A
  ext v
  have h := apply_repSum_indicator ρ hu v
  rw [repSum_indicator_coe_eq_natCard_smul hU hUW hC ρ hV] at h
  simp only [LinearMap.smul_apply, Module.End.one_apply] at h
  rw [← Nat.cast_smul_eq_nsmul k, map_smul] at h
  exact smul_right_injective V hk h

theorem eq_one_of_generalLinearGroup_of_forall_eq_zero (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    (hchar : ringChar k = 0 ∨ ¬ ringChar k ∣ Nat.card U)
    (ρ : A →* LinearMap.GeneralLinearGroup k V)
    (hV : ∀ v : V, (∀ w ∈ W, (ρ w : V →ₗ[k] V) v = v) → v = 0) {u : A} (hu : u ∈ U) :
    ρ u = 1 := by
  have hk : (Nat.card U : k) ≠ 0 := by
    rcases hchar with h | h
    · intro hc
      have hd := ringChar.dvd (R := k) hc
      rw [h, zero_dvd_iff] at hd
      exact absurd hd Nat.card_pos.ne'
    · exact fun hc => h (ringChar.dvd hc)
  refine Units.ext ?_
  refine eq_one_of_invariants_comp_subtype_eq_bot hU hUW hC hk
    ((Units.coeHom (V →ₗ[k] V)).comp ρ) ?_ hu
  rw [invariants_comp_subtype_eq_bot_iff]
  exact hV

end CFSG.FeitThompson
