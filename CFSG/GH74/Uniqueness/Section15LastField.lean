module

public import CFSG.GH74.Uniqueness.Section15LastAct
public import CFSG.GH74.Uniqueness.Section15Field

public section

namespace CFSG.GH74.Uniqueness.Section15Last

open Subgroup

variable {X : Type} [Group X] [Finite X] {M V R₀ Mo D K : Subgroup X} {u : X} {n : ℕ}

namespace FinalHyp

@[expose] def conjMoHom (h : FinalHyp M V R₀ Mo D K u n) : ↥M →* MulAut ↥Mo where
  toFun g :=
    { toFun := fun y => ⟨(g : X) * y * (g : X)⁻¹, h.Mo_norm g g.2 y y.2⟩
      invFun := fun y => ⟨(g : X)⁻¹ * y * (g : X), by
        have := h.Mo_norm (g : X)⁻¹ (M.inv_mem g.2) y y.2
        rwa [inv_inv] at this⟩
      left_inv := fun y => Subtype.ext (by
        show (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * g = y
        group)
      right_inv := fun y => Subtype.ext (by
        show (g : X) * ((g : X)⁻¹ * y * g) * (g : X)⁻¹ = y
        group)
      map_mul' := fun a b => Subtype.ext (by
        show (g : X) * ((a : X) * b) * (g : X)⁻¹ =
          ((g : X) * a * (g : X)⁻¹) * ((g : X) * b * (g : X)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun y => Subtype.ext (by
    show ((1 : ↥M) : X) * y * ((1 : ↥M) : X)⁻¹ = y
    simp)
  map_mul' g k := MulEquiv.ext fun y => Subtype.ext (by
    show ((g * k : ↥M) : X) * y * ((g * k : ↥M) : X)⁻¹ =
      (g : X) * ((k : X) * y * (k : X)⁻¹) * (g : X)⁻¹
    rw [Subgroup.coe_mul]
    group)

omit [Finite X] in
theorem conjMoHom_apply (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) (y : ↥Mo) :
    (h.conjMoHom g y : X) = (g : X) * y * (g : X)⁻¹ := rfl

omit [Finite X] in
theorem conjMoHom_V (h : FinalHyp M V R₀ Mo D K u n) {v : ↥M} (hv : (v : X) ∈ V) :
    h.conjMoHom v = 1 :=
  MulEquiv.ext fun y => Subtype.ext (by
    rw [conjMoHom_apply]
    have h1 := h.V_comm_Mo hv y.2
    calc (v : X) * y * (v : X)⁻¹ = (y : X) * v * (v : X)⁻¹ := by rw [h1]
      _ = y := by group)

theorem exists_conjMoHom_eq (h : FinalHyp M V R₀ Mo D K u n) {g : ↥M} (hg : tt u g = 1) :
    ∃ d : ↥M, (d : X) ∈ D ∧ h.conjMoHom g = h.conjMoHom d := by
  obtain ⟨v, hv, d, hd, hvd⟩ := h.exists_mul_of_tt_eq_one g hg
  have hvM : v ∈ M := h.V_le hv
  have hdM : d ∈ M := h.D_le hd
  refine ⟨⟨d, hdM⟩, hd, ?_⟩
  have hg' : g = ⟨v, hvM⟩ * ⟨d, hdM⟩ := Subtype.ext hvd
  rw [hg', map_mul, h.conjMoHom_V (v := ⟨v, hvM⟩) hv, one_mul]

@[expose] def autK (h : FinalHyp M V R₀ Mo D K u n) : Subgroup (MulAut ↥Mo) :=
  (K.subgroupOf M).map h.conjMoHom

omit [Finite X] in
theorem mem_autK (h : FinalHyp M V R₀ Mo D K u n) {φ : MulAut ↥Mo} :
    φ ∈ h.autK ↔ ∃ k : ↥M, (k : X) ∈ K ∧ h.conjMoHom k = φ :=
  Iff.rfl

omit [Finite X] in
theorem K_le_M (h : FinalHyp M V R₀ Mo D K u n) : K ≤ M := h.K_le.trans h.D_le

theorem fieldData (h : FinalHyp M V R₀ Mo D K u n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : ↥Mo ≃ F), Nat.card F = 2 ^ n ∧ e 1 = 0 ∧
      (∀ a : Fˣ, ∃ g : ↥M, tt u g = 1 ∧ ∀ y, e (h.smulMo g y) = a * e y) ∧
      (∀ g : ↥M, tt u g = 1 → ∃ (a : Fˣ) (σ : F ≃+* F), ∀ y, e (h.smulMo g y) = a * σ (e y)) := by
  have hcomm : ∀ a b : ↥Mo, a * b = b * a := fun a b => Subtype.ext (h.Mo_comm a.2 b.2)
  have hK : ∀ a ∈ h.autK, ∀ b ∈ h.autK, a * b = b * a := by
    rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
    have hk₁K : (k₁ : X) ∈ K := hk₁
    have hk₂K : (k₂ : X) ∈ K := hk₂
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.K_comm _ hk₁K _ hk₂K)
  have htrans : ∀ x y : ↥Mo, x ≠ 1 → y ≠ 1 → ∃ k ∈ h.autK, k x = y := by
    intro x y hx hy
    obtain ⟨k, hk, hkxy⟩ := h.K_trans x x.2 (fun h1 => hx (Subtype.ext h1)) y y.2
      (fun h1 => hy (Subtype.ext h1))
    exact ⟨h.conjMoHom ⟨k, h.K_le_M hk⟩, ⟨⟨k, h.K_le_M hk⟩, hk, rfl⟩, Subtype.ext hkxy⟩
  have hnt : ∃ x : ↥Mo, x ≠ 1 := by
    have h1 : 1 < Nat.card ↥Mo := by
      rw [h.card_Mo]
      exact Nat.one_lt_two_pow (by have := h.two_le; omega)
    have := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne (1 : ↥Mo)
  obtain ⟨F, hF, hFin, e, hcard, he1, hunits, hsemi⟩ :=
    Section15Field.exists_field_of_regular hcomm h.autK hK htrans hnt
  refine ⟨F, hF, hFin, e, hcard.trans h.card_Mo, he1, ?_, ?_⟩
  · intro a
    obtain ⟨_, ⟨k, hk, rfl⟩, hka⟩ := hunits a
    have hkK : (k : X) ∈ K := hk
    refine ⟨k, h.tt_D (h.K_le hkK), fun y => ?_⟩
    have h1 : h.smulMo k y = h.conjMoHom k y :=
      Subtype.ext (h.smulMo_of_tt_eq_one (h.tt_D (h.K_le hkK)) y)
    rw [h1]
    exact hka y
  · intro g hg
    obtain ⟨d, hd, hgd⟩ := h.exists_conjMoHom_eq hg
    have h1 : ∀ k ∈ h.autK, h.conjMoHom g * k * (h.conjMoHom g)⁻¹ ∈ h.autK := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨d * k * d⁻¹, ?_, ?_⟩
      · have hkK : (k : X) ∈ K := hk
        exact h.K_norm d hd k hkK
      · rw [hgd, map_mul, map_mul, map_inv]
    have h2 : ∀ k ∈ h.autK, (h.conjMoHom g)⁻¹ * k * h.conjMoHom g ∈ h.autK := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨d⁻¹ * k * d, ?_, ?_⟩
      · have hkK : (k : X) ∈ K := hk
        have := h.K_norm (d : X)⁻¹ (D.inv_mem hd) k hkK
        rwa [inv_inv] at this
      · rw [hgd, map_mul, map_mul, map_inv]
    obtain ⟨a, σ, hσ⟩ := hsemi (h.conjMoHom g) h1 h2
    refine ⟨a, σ, fun y => ?_⟩
    have h3 : h.smulMo g y = h.conjMoHom g y :=
      Subtype.ext (h.smulMo_of_tt_eq_one hg y)
    rw [h3]
    exact hσ y

end FinalHyp

end CFSG.GH74.Uniqueness.Section15Last
