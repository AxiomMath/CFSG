module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3

open Module LinearMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

section Fixed

@[expose] def fixedSpace {T : Type*} (τ : T → Module.End (ZMod 2) V) : Submodule (ZMod 2) V where
  carrier := {v | ∀ t, τ t v = v}
  add_mem' := by
    intro a b ha hb t
    rw [map_add, ha t, hb t]
  zero_mem' := by
    intro t
    exact map_zero _
  smul_mem' := by
    intro c a ha t
    rw [map_smul, ha t]

theorem exists_fixed_vector {T : Type*} [Group T] (hT : IsPGroup 2 T)
    (τ : T →* Module.End (ZMod 2) V) (W : Submodule (ZMod 2) V)
    (hW : ∀ t, ∀ w ∈ W, τ t w ∈ W) (hne : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ t, τ t w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction T ↥W :=
    { smul := fun t w => ⟨τ t w, hW t w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show τ 1 (w : V) = w
        rw [map_one]
        rfl)
      mul_smul := fun s t w => Subtype.ext (by
        show τ (s * t) (w : V) = τ s (τ t (w : V))
        rw [map_mul]
        rfl) }
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite ↥W := inferInstance
  have h2 : 2 ∣ Nat.card ↥W := by
    haveI : Fintype ↥W := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥W),
      ZMod.card]
    have : 1 ≤ finrank (ZMod 2) ↥W := Submodule.one_le_finrank_iff.2 hne
    exact dvd_pow_self 2 (by omega)
  have h0 : (0 : ↥W) ∈ MulAction.fixedPoints T ↥W := by
    intro t
    exact Subtype.ext (map_zero (τ t))
  obtain ⟨b, hb, hb0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥W h2 h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun t => ?_⟩
  exact congrArg Subtype.val (hb t)

end Fixed

section Flag

variable {E : Type*} [CommGroup E] [Finite E]
variable (B : LinearMap.BilinForm (ZMod 2) V)

include B in
theorem index_le_of_isotropic (hE3 : ∀ e : E, e ^ 3 = 1) (hB : B.Nondegenerate)
    (hrefl : B.IsRefl) (ρ : E →* Module.End (ZMod 2) V)
    (hρ : ∀ e x y, B (ρ e x) (ρ e y) = B x y) (R : Submodule (ZMod 2) V)
    (hR : ∀ e, ∀ r ∈ R, ρ e r ∈ R) (hiso : ∀ r ∈ R, ∀ r' ∈ R, B r r' = 0) (hne : R ≠ ⊥)
    (heven : Even (finrank (ZMod 2) V)) :
    (fixSub ρ ⊤).index ≤ 3 ^ (finrank (ZMod 2) V / 2 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := B.orthogonal R with hP
  have hPinv : ∀ e, ∀ x ∈ P, ρ e x ∈ P := by
    intro e x hx
    rw [hP, LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro r hr
    have h1 : ρ e (ρ e⁻¹ r) = r := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h2 := hρ e (ρ e⁻¹ r) x
    rw [h1] at h2
    rw [h2]
    exact hx _ (hR e⁻¹ r hr)
  have hRP : R ≤ P := by
    intro r hr
    rw [hP, LinearMap.BilinForm.mem_orthogonal_iff]
    intro r' hr'
    exact hiso r' hr' r hr
  have hK : fixSub ρ P = fixSub ρ ⊤ := by
    apply le_antisymm
    · intro e he
      rw [mem_fixSub] at he ⊢
      intro v _
      set a := ρ e v + v with ha
      have haR : a ∈ B.orthogonal P := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro p hp
        have h1 : ρ e p = p := he p hp
        have h2 := hρ e p v
        rw [h1] at h2
        rw [ha, map_add, h2, add_self_vec]
      rw [hP, LinearMap.BilinForm.orthogonal_orthogonal hB hrefl] at haR
      have haP : a ∈ P := hRP haR
      have h3 : ρ e a = a := he a haP
      have h4 : ρ e (ρ e v) = v := by
        have hv : ρ e v = a + v := by
          rw [ha, add_assoc, add_self_vec, add_zero]
        rw [congrArg (ρ e) hv, map_add, h3]
        have : a + ρ e v = (ρ e v + ρ e v) + v := by rw [ha]; abel
        rw [this, add_self_vec, zero_add]
      have h5 : ρ e (ρ e (ρ e v)) = v := by
        have h : ρ (e ^ 3) = 1 := by rw [hE3 e, map_one]
        have := congrArg (fun f : Module.End (ZMod 2) V => f v) h
        simpa [pow_succ, map_mul, Module.End.mul_apply] using this
      rw [h4] at h5
      exact h5
    · exact fun e he => by
        rw [mem_fixSub] at he ⊢
        intro u hu
        exact he u Submodule.mem_top
  have hidx := index_fixSub_le hE3 ρ (finrank (ZMod 2) P) P rfl hPinv
  rw [← hK]
  refine hidx.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have hfin : finrank (ZMod 2) P = finrank (ZMod 2) V - finrank (ZMod 2) R :=
    LinearMap.BilinForm.finrank_orthogonal hB R
  have hr : 1 ≤ finrank (ZMod 2) R := Submodule.one_le_finrank_iff.2 hne
  obtain ⟨k, hk⟩ := heven
  omega

end Flag

section Main

variable {E : Type*} [CommGroup E] [Finite E] {T : Type*} [Group T]
variable (B : LinearMap.BilinForm (ZMod 2) V)

include B in
theorem orthogonal_invariant (ρ : E →* Module.End (ZMod 2) V)
    (hρ : ∀ e x y, B (ρ e x) (ρ e y) = B x y) (R : Submodule (ZMod 2) V)
    (hR : ∀ e, ∀ r ∈ R, ρ e r ∈ R) : ∀ e, ∀ x ∈ B.orthogonal R, ρ e x ∈ B.orthogonal R := by
  intro e x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  intro r hr
  have h1 : ρ e (ρ e⁻¹ r) = r := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 := hρ e (ρ e⁻¹ r) x
  rw [h1] at h2
  rw [h2]
  exact hx _ (hR e⁻¹ r hr)

include B in
theorem fixed_eq_top_of_full (hE3 : ∀ e : E, e ^ 3 = 1) (hB : B.Nondegenerate)
    (hrefl : B.IsRefl) (ρ : E →* Module.End (ZMod 2) V)
    (hρ : ∀ e x y, B (ρ e x) (ρ e y) = B x y) (hT : IsPGroup 2 T)
    (τ : T →* Module.End (ZMod 2) V) (hτ : ∀ t x y, B (τ t x) (τ t y) = B x y)
    (hinv : ∀ e : E, ∀ x, (∀ t, τ t x = x) → ∀ t, τ t (ρ e x) = ρ e x)
    (heven : Even (finrank (ZMod 2) V))
    (hfull : 3 ^ (finrank (ZMod 2) V / 2) ≤ (fixSub ρ ⊤).index) :
    ∀ t x, τ t x = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, x₀, hx₀⟩ := hcon
  set U := fixedSpace (fun t => τ t) with hU
  have hVne : (⊤ : Submodule (ZMod 2) V) ≠ ⊥ := by
    intro h
    apply hx₀
    have : x₀ ∈ (⊤ : Submodule (ZMod 2) V) := Submodule.mem_top
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]
  have hUinv : ∀ e, ∀ x ∈ U, ρ e x ∈ U := fun e x hx => hinv e x hx
  have hdisj : U ⊓ B.orthogonal U = ⊥ := by
    by_contra hne
    have hiso : ∀ r ∈ U ⊓ B.orthogonal U, ∀ r' ∈ U ⊓ B.orthogonal U, B r r' = 0 := by
      intro r hr r' hr'
      have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.1 (Submodule.mem_inf.1 hr).2) r'
        (Submodule.mem_inf.1 hr').1
      exact hrefl _ _ h1
    have hinvR : ∀ e, ∀ r ∈ U ⊓ B.orthogonal U, ρ e r ∈ U ⊓ B.orthogonal U := fun e r hr =>
      Submodule.mem_inf.2 ⟨hUinv e r (Submodule.mem_inf.1 hr).1,
        orthogonal_invariant B ρ hρ U hUinv e r (Submodule.mem_inf.1 hr).2⟩
    have h1 := index_le_of_isotropic B hE3 hB hrefl ρ hρ _ hinvR hiso hne heven
    have hpos : 1 ≤ finrank (ZMod 2) V / 2 := by
      have : 1 ≤ finrank (ZMod 2) V := by
        rw [← finrank_top (ZMod 2) V]
        exact Submodule.one_le_finrank_iff.2 hVne
      obtain ⟨k, hk⟩ := heven
      omega
    have h2 : 3 ^ (finrank (ZMod 2) V / 2 - 1) < 3 ^ (finrank (ZMod 2) V / 2) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcompl : IsCompl U (B.orthogonal U) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 (disjoint_iff.2 hdisj)
  have hTinv : ∀ t, ∀ x ∈ B.orthogonal U, τ t x ∈ B.orthogonal U := by
    intro t x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro u hu
    have h1 : τ t u = u := hu t
    have h2 := hτ t u x
    rw [h1] at h2
    rw [h2]
    exact hx u hu
  have hperp : B.orthogonal U = ⊥ := by
    by_contra hne
    obtain ⟨w, hw, hw0, hwfix⟩ := exists_fixed_vector hT τ (B.orthogonal U) hTinv hne
    have : w ∈ U ⊓ B.orthogonal U := Submodule.mem_inf.2 ⟨hwfix, hw⟩
    rw [hdisj, Submodule.mem_bot] at this
    exact hw0 this
  have hUtop : U = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hperp, sup_bot_eq] at this
  have hx : x₀ ∈ U := by rw [hUtop]; exact Submodule.mem_top
  exact hx₀ (hx t₀)

end Main

section Group

variable {G₁ : Type*} [Group G₁] [Finite G₁]
variable (B : LinearMap.BilinForm (ZMod 2) V)

include B in
theorem eq_bot_of_full (hB : B.Nondegenerate) (hrefl : B.IsRefl)
    (heven : Even (finrank (ZMod 2) V)) (ρ : G₁ →* Module.End (ZMod 2) V)
    (hρinj : Function.Injective ρ) (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    {E T : Subgroup G₁} (hcomm : ∀ a b : ↥E, a * b = b * a) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hT : IsPGroup 2 ↥T) (hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T)
    (hcard : 3 ^ (finrank (ZMod 2) V / 2) ≤ Nat.card E) : T = ⊥ := by
  letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hcomm }
  let ρE : ↥E →* Module.End (ZMod 2) V := ρ.comp E.subtype
  let τ : ↥T →* Module.End (ZMod 2) V := ρ.comp T.subtype
  have hfix : fixSub ρE ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [mem_fixSub] at he
    have h1 : ρ (e : G₁) = 1 := by
      ext x
      exact he x Submodule.mem_top
    have h2 : (e : G₁) = 1 := hρinj (by rw [h1, map_one])
    exact Subtype.ext h2
  have hfull : 3 ^ (finrank (ZMod 2) V / 2) ≤ (fixSub ρE ⊤).index := by
    rw [hfix, Subgroup.index_bot]
    exact hcard
  have hinv : ∀ e : ↥E, ∀ x, (∀ t, τ t x = x) → ∀ t, τ t (ρE e x) = ρE e x := by
    intro e x hx t
    have ht' : (e : G₁)⁻¹ * (t : G₁) * (e : G₁)⁻¹⁻¹ ∈ T := hN _ (E.inv_mem e.2) _ t.2
    have h1 := hx ⟨_, ht'⟩
    show ρ (t : G₁) (ρ (e : G₁) x) = ρ (e : G₁) x
    rw [← Module.End.mul_apply, ← map_mul]
    have : (t : G₁) * e = e * ((e : G₁)⁻¹ * t * (e : G₁)⁻¹⁻¹) := by group
    rw [this, map_mul, Module.End.mul_apply]
    have h2 : ρ ((e : G₁)⁻¹ * (t : G₁) * (e : G₁)⁻¹⁻¹) x = x := h1
    rw [h2]
  have hmain := fixed_eq_top_of_full (E := ↥E) B (fun e => Subtype.ext (hE3 e e.2)) hB hrefl ρE
    (fun e => hρ e) hT τ (fun t => hρ t) hinv heven hfull
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have h1 : ρ t = 1 := by
    ext x
    exact hmain ⟨t, ht⟩ x
  exact hρinj (by rw [h1, map_one])

end Group

end CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
