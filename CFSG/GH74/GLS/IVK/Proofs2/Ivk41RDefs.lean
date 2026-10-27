module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41R

open Subgroup
open scoped commutatorElement

@[expose] def RGood (p n : ℕ) {J : Type} [Group J] (z : J) (X : Subgroup J) : Prop :=
  ∃ R : Subgroup J, R = CFSG.Open.pCoreOf p (centralizer (X : Set J)) ∧ IsPGroup p ↥R ∧ X ≤ R ∧
    R ≤ centralizer (X : Set J) ∧ Nat.card ↥R = (p ^ n) ^ 3 ∧
    (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧ (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧
    (∀ r ∈ R, z * r * z⁻¹ * r ∈ X)

theorem centralizer_map_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (X : Subgroup J) :
    centralizer ((X.map e.toMonoidHom : Subgroup J') : Set J') =
      (centralizer (X : Set J)).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    show e.symm y ∈ centralizer (X : Set J)
    rw [mem_centralizer_iff]
    intro x hx
    have := mem_centralizer_iff.mp hy (e x) ⟨x, hx, rfl⟩
    apply e.injective
    simpa using this
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have := mem_centralizer_iff.mp hx s hs
    show e s * e x = e x * e s
    rw [← map_mul, ← map_mul, this]

theorem map_map_symm_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (E : Subgroup A) :
    (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by ext x; simp
  rw [this, Subgroup.map_id]

theorem RGood.map {J J' : Type} [Group J] [Group J'] (e : J ≃* J') {p n : ℕ} {z : J}
    {X : Subgroup J} (h : RGood p n z X) : RGood p n (e z) (X.map e.toMonoidHom) := by
  obtain ⟨R, hR, hRp, hXR, hRC, hRcard, hZ, hXc, hcomm, hz⟩ := h
  have hC := centralizer_map_mulEquiv e X
  refine ⟨R.map e.toMonoidHom, ?_, hRp.map _, Subgroup.map_mono hXR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv, ← hR]
  · rw [hC]
    exact Subgroup.map_mono hRC
  · rw [Subgroup.card_map_of_injective e.injective, hRcard]
  · rintro _ ⟨r, hr, rfl⟩ hc
    refine ⟨r, hZ r hr fun s hs => e.injective ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hc (e s) ⟨s, hs, rfl⟩
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hXc
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    have := hcomm r hr s hs
    refine ⟨_, this, ?_⟩
    simp
  · rintro _ ⟨r, hr, rfl⟩
    refine ⟨_, hz r hr, ?_⟩
    simp

theorem RGood.congr {J J' : Type} [Group J] [Group J'] (e : J ≃* J') {p n : ℕ} {z : J} {z' : J'}
    {X : Subgroup J} {X' : Subgroup J'} (hz : e z = z') (hX : X.map e.toMonoidHom = X')
    (h : RGood p n z X) : RGood p n z' X' := by
  subst hz hX
  exact h.map e

theorem rgood_transport {J J' : Type} [Group J] [Group J'] (E : J ≃* J') {p n : ℕ}
    (h : ∀ (z' : J') (X' : Subgroup J'), orderOf z' = 2 → X' ≤ centralizer ({z'} : Set J') →
      IsPGroup p ↥X' → Nat.card ↥X' = p ^ n → RGood p n z' X')
    {z : J} (hz : orderOf z = 2) {X : Subgroup J} (hXz : X ≤ centralizer ({z} : Set J))
    (hXp : IsPGroup p ↥X) (hXc : Nat.card ↥X = p ^ n) : RGood p n z X := by
  have hle : X.map E.toMonoidHom ≤ centralizer ({E z} : Set J') := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.mp (hXz hx)
    show E x * E z = E z * E x
    rw [← map_mul, ← map_mul, this]
  have h1 := h (E z) (X.map E.toMonoidHom) (by rw [MulEquiv.orderOf_eq]; exact hz) hle
    (hXp.map _) (by rw [Subgroup.card_map_of_injective E.injective]; exact hXc)
  exact RGood.congr E.symm (MulEquiv.symm_apply_apply E z) (map_map_symm_mulEquiv E X) h1

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41R
