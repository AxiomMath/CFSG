module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

@[expose] noncomputable def barAct (K : Subgroup X) [K.Normal] : X →* MulAut (K ⧸ center K) where
  toFun x := QuotientGroup.congr (center K) (center K) (MulAut.conjNormal x : MulAut K)
    (Subgroup.map_center_eq _)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H k => simp
  map_mul' a b := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H k => simp

theorem barAct_mk (K : Subgroup X) [K.Normal] (x : X) (k : K) :
    barAct K x (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal x k) :=
  rfl

theorem barAct_eq_one_of_commute {K : Subgroup X} [K.Normal] {x : X}
    (hx : ∀ k ∈ K, x * k = k * x) : barAct K x = 1 := by
  ext y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAct_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, hx k k.2, mul_inv_cancel_right]

theorem barAct_of_mem (K : Subgroup X) [K.Normal] (k : K) :
    barAct K (k : X) = MulAut.conj (QuotientGroup.mk k : K ⧸ center K) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAct_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1

theorem commutator_mul_central {G : Type*} [Group G] (x y z₁ z₂ : G)
    (h₁ : ∀ g : G, g * z₁ = z₁ * g) (h₂ : ∀ g : G, g * z₂ = z₂ * g) :
    ⁅x * z₁, y * z₂⁆ = ⁅x, y⁆ := by
  have e1 : z₁ * z₂ * z₁⁻¹ = z₂ := by
    calc z₁ * z₂ * z₁⁻¹ = (z₂ * z₁) * z₁⁻¹ := by rw [← h₂ z₁]
      _ = z₂ := by group
  simp only [commutatorElement_def]
  calc x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹
      = x * (z₁ * y) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * (y * z₁) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [← h₁ y]
    _ = x * y * (z₁ * z₂ * z₁⁻¹) * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * z₂ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [e1]
    _ = x * y * (z₂ * x⁻¹) * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z₂) * z₂⁻¹ * y⁻¹ := by rw [← h₂ x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commute_of_barAct_eq_one {K : Subgroup X} [K.Normal] (hperf : commutator ↥K = ⊤) {x : X}
    (hx : barAct K x = 1) : ∀ k ∈ K, x * k = k * x := by
  set φ : MulAut ↥K := MulAut.conjNormal x with hφ
  have hz : ∀ k : ↥K, ∃ z ∈ center ↥K, φ k = k * z := by
    intro k
    have h1 : barAct K x (QuotientGroup.mk k) = QuotientGroup.mk k := by
      rw [hx]
      rfl
    rw [barAct_mk] at h1
    exact ⟨k⁻¹ * φ k, (QuotientGroup.eq (s := center ↥K)).1 h1.symm, by simp⟩
  have hfix : ∀ a b : ↥K, φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨z₁, hz₁, h₁⟩ := hz a
    obtain ⟨z₂, hz₂, h₂⟩ := hz b
    rw [map_commutatorElement, h₁, h₂]
    exact commutator_mul_central a b z₁ z₂ (Subgroup.mem_center_iff.mp hz₁)
      (Subgroup.mem_center_iff.mp hz₂)
  have hle : commutator ↥K ≤ MonoidHom.eqLocus (φ : ↥K →* ↥K) (MonoidHom.id ↥K) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hfix a b
  rw [hperf] at hle
  intro k hk
  have h3 : φ ⟨k, hk⟩ = ⟨k, hk⟩ := hle (Subgroup.mem_top _)
  have h4 : x * k * x⁻¹ = k := congrArg Subtype.val h3
  calc x * k = x * k * x⁻¹ * x := by group
    _ = k * x := by rw [h4]

theorem exists_fixed_lift {K : Subgroup X} [K.Normal] [Finite K] {p : ℕ} [Fact p.Prime]
    (hZ : ¬ p ∣ Nat.card (center ↥K)) {a : X} (ha : a ^ p = 1) {kb : K ⧸ center K}
    (hfix : barAct K a kb = kb) :
    ∃ k : K, (QuotientGroup.mk k : K ⧸ center K) = kb ∧ MulAut.conjNormal a k = k := by
  classical
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
  let S : Type _ := {k : K // (QuotientGroup.mk k : K ⧸ center K) = QuotientGroup.mk k₀}
  have hmem : ∀ (x : X) (s : S), barAct K x (QuotientGroup.mk k₀) = QuotientGroup.mk k₀ →
      (QuotientGroup.mk (MulAut.conjNormal x s.1) : K ⧸ center K) = QuotientGroup.mk k₀ := by
    intro x s hx
    rw [← barAct_mk, s.2, hx]
  have hinv : barAct K a⁻¹ (QuotientGroup.mk k₀) = QuotientGroup.mk k₀ := by
    rw [map_inv, MulAut.inv_apply]
    exact (MulEquiv.symm_apply_eq _).2 hfix.symm
  let σ : Equiv.Perm S :=
    { toFun := fun s => ⟨MulAut.conjNormal a s.1, hmem a s hfix⟩
      invFun := fun s => ⟨MulAut.conjNormal a⁻¹ s.1, hmem a⁻¹ s hinv⟩
      left_inv := fun s => by
        apply Subtype.ext
        change MulAut.conjNormal a⁻¹ (MulAut.conjNormal a s.1) = s.1
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun s => by
        apply Subtype.ext
        change MulAut.conjNormal a (MulAut.conjNormal a⁻¹ s.1) = s.1
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  have hσ : ∀ n : ℕ, ∀ s : S, ((σ ^ n) s).1 = MulAut.conjNormal (a ^ n) s.1 := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ s)]
      change MulAut.conjNormal (a ^ n) (MulAut.conjNormal a s.1) = _
      rw [← MulAut.mul_apply, ← map_mul, ← pow_succ]
  have hσp : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext s
    rw [hσ p s, ha]
    simp
  haveI : Finite S := inferInstance
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card S = Nat.card (center ↥K) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun s => ⟨k₀⁻¹ * s.1, ?_⟩
        invFun := fun z => ⟨k₀ * z.1, ?_⟩
        left_inv := fun s => by simp
        right_inv := fun z => by simp }
    · exact (QuotientGroup.eq (s := center ↥K)).1 s.2.symm
    · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z.1).2 z.2, mul_one]
  have hnd : ¬ p ∣ Fintype.card S := by
    rw [hcard]
    exact hZ
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσp
  exact ⟨s.1, s.2, congrArg Subtype.val hs⟩

theorem eq_top_of_sup_center {Q : Type*} [Group Q] (hperf : commutator Q = ⊤) {W : Subgroup Q}
    (h : W ⊔ center Q = ⊤) : W = ⊤ := by
  rw [eq_top_iff, ← hperf, _root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have h1 : g₁ ∈ W ⊔ center Q := h ▸ Subgroup.mem_top g₁
  have h2 : g₂ ∈ W ⊔ center Q := h ▸ Subgroup.mem_top g₂
  obtain ⟨w₁, hw₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 h1
  obtain ⟨w₂, hw₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 h2
  rw [commutator_mul_central _ _ _ _ (Subgroup.mem_center_iff.mp hz₁)
    (Subgroup.mem_center_iff.mp hz₂), commutatorElement_def]
  exact W.mul_mem (W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)) (W.inv_mem hw₂)

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration
