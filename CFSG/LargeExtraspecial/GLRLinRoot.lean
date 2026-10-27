module

public import CFSG.LargeExtraspecial.GLRLinPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem mem_span_singleton_iff {x v : S.Qt} :
    v ∈ Submodule.span (ZMod 2) ({x} : Set S.Qt) ↔ v = 0 ∨ v = x := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · left; exact zero_smul _ _
    · right; exact one_smul _ _
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem apply_conj (p r : S.O) (v : S.Qt) :
    ((p * r * p⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((p : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (p : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, show p * r * p⁻¹ * p = p * r by group,
    Subgroup.coe_mul, LinearEquiv.mul_apply]

@[expose] noncomputable def rootGroup (A : Submodule (ZMod 2) S.Qt) (α : S.Qt) : Subgroup S.O where
  carrier := {e | (e : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α ∧
    ∀ a ∈ A, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a ∈ Submodule.span (ZMod 2) ({α} : Set S.Qt)}
  mul_mem' := by
    rintro x y ⟨hxα, hx⟩ ⟨hyα, hy⟩
    refine ⟨by rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hyα, hxα], fun a ha => ?_⟩
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) a) - a =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) +
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) := by rw [map_sub]; abel
    rw [e]
    refine Submodule.add_mem _ ?_ (hx a ha)
    rcases mem_span_singleton_iff.mp (hy a ha) with h | h <;> rw [h]
    · rw [map_zero]; exact Submodule.zero_mem _
    · rw [hxα]; exact Submodule.mem_span_singleton_self _
  one_mem' := ⟨rfl, fun a _ => by
    change a - a ∈ _
    rw [sub_self]; exact Submodule.zero_mem _⟩
  inv_mem' := by
    rintro x ⟨hxα, hx⟩
    have hinv : ∀ v, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
      fun v => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    have hα : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α := by
      conv_lhs => rw [← hxα]
      exact hinv α
    refine ⟨hα, fun a ha => ?_⟩
    have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a =
        -((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) := by
      rw [map_sub, hinv]; abel
    rw [e]
    refine Submodule.neg_mem _ ?_
    rcases mem_span_singleton_iff.mp (hx a ha) with h | h <;> rw [h]
    · rw [map_zero]; exact Submodule.zero_mem _
    · rw [hα]; exact Submodule.mem_span_singleton_self _

namespace Pair

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

theorem conj_mem_rootGroup (h : Pair S X A B) {α : S.Qt} {p r : S.O} (hp : p ∈ X)
    (hpα : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α) (hr : r ∈ rootGroup A α ⊓ X) :
    p * r * p⁻¹ ∈ rootGroup A α ⊓ X := by
  obtain ⟨⟨hrα, hrA⟩, hrX⟩ := hr
  refine ⟨⟨?_, fun a ha => ?_⟩, X.mul_mem (X.mul_mem hp hrX) (X.inv_mem hp)⟩
  · conv_lhs => rw [← hpα]
    rw [apply_conj, hrα, hpα]
  · obtain ⟨a', ha', rfl⟩ := h.exists_apply_eq hp ha
    rw [apply_conj, ← map_sub]
    rcases mem_span_singleton_iff.mp (hrA a' ha') with e | e <;> rw [e]
    · rw [map_zero]; exact Submodule.zero_mem _
    · rw [hpα]; exact Submodule.mem_span_singleton_self _

theorem rootGroup_injOn (h : Pair S X A B) {α b₀ : S.Qt}
    (hαb : polar S.q α b₀ = 1) {e e' : S.O} (he : e ∈ rootGroup A α ⊓ X)
    (he' : e' ∈ rootGroup A α ⊓ X)
    (hee : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) b₀ = (e' : S.Qt ≃ₗ[ZMod 2] S.Qt) b₀) : e = e' := by
  have hd : e'⁻¹ * e ∈ rootGroup A α ⊓ X := (rootGroup A α ⊓ X).mul_mem
    ((rootGroup A α ⊓ X).inv_mem he') he
  have hinv : ∀ v, ((e'⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((e' : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
    fun v => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hdb : ((e'⁻¹ * e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) b₀ = b₀ := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hee, hinv]
  have hfix : ∀ a ∈ A, ((e'⁻¹ * e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    intro a ha
    have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (e'⁻¹ * e).2 a b₀
    rw [hdb] at hpol
    rcases mem_span_singleton_iff.mp (hd.1.2 a ha) with e1 | e1
    · exact sub_eq_zero.mp e1
    · exfalso
      rw [sub_eq_iff_eq_add.mp e1, polar_add_left, hαb] at hpol
      have : (1 : ZMod 2) = 0 := by
        have h2 := congrArg (· - polar S.q a b₀) hpol
        simp only [add_sub_cancel_right, sub_self] at h2
        exact h2
      exact one_ne_zero this
  have h1 := h.ext_of_eqOn hd.2 X.one_mem fun a ha => (hfix a ha).trans rfl
  calc e = e' * (e'⁻¹ * e) := by group
    _ = e' := by rw [h1, mul_one]

theorem card_rootGroup_le (h : Pair S X A B) {α : S.Qt} (hα : α ∈ A) (hα0 : α ≠ 0) :
    Nat.card (rootGroup A α ⊓ X : Subgroup S.O) ≤ 2 ^ (S.width - 1) := by
  obtain ⟨b₀, hb₀, hb₀α⟩ := h.symm.exists_polar_eq_one hα hα0
  have hαb : polar S.q α b₀ = 1 := by rw [polar_comm]; exact hb₀α
  set Bα : Submodule (ZMod 2) S.Qt := B ⊓ LinearMap.ker (S.q.polarBilin α)
  have hmem : ∀ e ∈ rootGroup A α ⊓ X, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) b₀ - b₀ ∈ Bα := by
    rintro e ⟨⟨heα, -⟩, heX⟩
    refine ⟨B.sub_mem (h.apply_B e heX b₀ hb₀) hb₀, ?_⟩
    change polar S.q α ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) b₀ - b₀) = 0
    conv_lhs => rw [← heα]
    rw [polar_sub_right, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup e.2, heα,
      sub_self]
  let φ : (rootGroup A α ⊓ X : Subgroup S.O) → Bα := fun e => ⟨_, hmem e e.2⟩
  have hφ : Function.Injective φ := by
    intro e e' hee
    have := congrArg (fun v : Bα => (v : S.Qt)) hee
    simp only [φ, sub_left_inj] at this
    exact Subtype.ext (h.rootGroup_injOn hαb e.2 e'.2 this)
  have hlt : Bα < B := by
    refine lt_of_le_of_ne inf_le_left fun e => ?_
    have : b₀ ∈ Bα := e ▸ hb₀
    have h0 : polar S.q α b₀ = 0 := this.2
    rw [hαb] at h0
    exact one_ne_zero h0
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  rw [h.finrank_B] at hdim
  calc Nat.card (rootGroup A α ⊓ X : Subgroup S.O) ≤ Nat.card Bα :=
        Nat.card_le_card_of_injective φ hφ
    _ = 2 ^ finrank (ZMod 2) Bα := S.card_submodule Bα
    _ ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_rootGroup_inf_le (h : Pair S X A B) {α β : S.Qt} (hα : α ∈ A) (hα0 : α ≠ 0) :
    Nat.card (rootGroup A α ⊓ rootGroup B β ⊓ X : Subgroup S.O) ≤ 2 := by
  obtain ⟨b₀, hb₀, hb₀α⟩ := h.symm.exists_polar_eq_one hα hα0
  have hαb : polar S.q α b₀ = 1 := by rw [polar_comm]; exact hb₀α
  set P : Submodule (ZMod 2) S.Qt := Submodule.span (ZMod 2) ({β} : Set S.Qt)
  let φ : (rootGroup A α ⊓ rootGroup B β ⊓ X : Subgroup S.O) → P :=
    fun e => ⟨_, e.2.1.2.2 b₀ hb₀⟩
  have hφ : Function.Injective φ := by
    intro e e' hee
    have := congrArg (fun v : P => (v : S.Qt)) hee
    simp only [φ, sub_left_inj] at this
    exact Subtype.ext (h.rootGroup_injOn hαb ⟨e.2.1.1, e.2.2⟩ ⟨e'.2.1.1, e'.2.2⟩ this)
  have hdim : finrank (ZMod 2) P ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({β} : Set S.Qt)
    simpa using this
  calc Nat.card (rootGroup A α ⊓ rootGroup B β ⊓ X : Subgroup S.O) ≤ Nat.card P :=
        Nat.card_le_card_of_injective φ hφ
    _ = 2 ^ finrank (ZMod 2) P := S.card_submodule P
    _ ≤ 2 := by
      calc 2 ^ finrank (ZMod 2) P ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hdim
        _ = 2 := by norm_num

end Pair

end CFSG.LargeExtraspecial.GLR
