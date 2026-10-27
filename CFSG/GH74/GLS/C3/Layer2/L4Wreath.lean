module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4.Wreath

open Equiv Perm

abbrev N4 : Type := Fin 4 → ℤˣ

@[expose] def act (π : Perm (Fin 4)) : MulAut N4 where
  toFun ε := fun i => ε (π.symm i)
  invFun ε := fun i => ε (π i)
  left_inv ε := by ext i; simp
  right_inv ε := by ext i; simp
  map_mul' _ _ := rfl

@[expose] def actHom : Perm (Fin 4) →* MulAut N4 where
  toFun := act
  map_one' := by ext ε i; rfl
  map_mul' π π' := by ext ε i; rfl

abbrev W : Type := N4 ⋊[actHom] Perm (Fin 4)

theorem card_N4 : Nat.card N4 = 16 := by
  rw [Nat.card_pi]
  simp [Nat.card_eq_fintype_card]

theorem card_W : Nat.card W = 384 := by
  rw [SemidirectProduct.card, card_N4, Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem act_mulSingle (π : Perm (Fin 4)) (i : Fin 4) (u : ℤˣ) :
    act π (Pi.mulSingle i u) = Pi.mulSingle (π i) u := by
  ext j
  simp only [act, MulEquiv.coe_mk, Equiv.coe_fn_mk, Pi.mulSingle_apply]
  by_cases h : j = π i
  · subst h; simp
  · have : π.symm j ≠ i := fun h' => h (by rw [← h']; simp)
    simp [h, this]

@[expose] def prodHom : N4 →* ℤˣ where
  toFun ε := ∏ i, ε i
  map_one' := by simp
  map_mul' ε ε' := by simp [Finset.prod_mul_distrib]

theorem prodHom_act (π : Perm (Fin 4)) (ε : N4) : prodHom (act π ε) = prodHom ε := by
  simp only [prodHom, MonoidHom.coe_mk, OneHom.coe_mk, act, MulEquiv.coe_mk, Equiv.coe_fn_mk]
  exact Equiv.prod_comp π.symm (fun i => ε i)

section Recognition

variable {C : Type*} [Group C]

@[expose] def unitsHom (c : C) (hc : c * c = 1) : ℤˣ →* C where
  toFun u := if u = 1 then 1 else c
  map_one' := by simp
  map_mul' u v := by
    have h1 : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [hc, h1]

theorem unitsHom_neg_one (c : C) (hc : c * c = 1) : unitsHom c hc (-1) = c := by
  have h1 : (-1 : ℤˣ) ≠ 1 := by decide
  simp [unitsHom, h1]

theorem unitsHom_one (c : C) (hc : c * c = 1) : unitsHom c hc 1 = 1 := map_one _

theorem unitsHom_cases (c : C) (hc : c * c = 1) (u : ℤˣ) :
    unitsHom c hc u = 1 ∨ unitsHom c hc u = c := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl (unitsHom_one c hc)
  · exact Or.inr (unitsHom_neg_one c hc)

theorem bHom_pairwise (b : Fin 4 → C) (hcomm : ∀ i j, b i * b j = b j * b i)
    (hsq : ∀ i, b i * b i = 1) :
    Pairwise fun i j => ∀ (x y : ℤˣ),
      Commute (unitsHom (b i) (hsq i) x) (unitsHom (b j) (hsq j) y) := by
  intro i j _ x y
  rcases unitsHom_cases (b i) (hsq i) x with h | h
  · rw [h]; exact Commute.one_left _
  · rcases unitsHom_cases (b j) (hsq j) y with h' | h'
    · rw [h']; exact Commute.one_right _
    · rw [h, h']; exact hcomm i j

@[expose] def bHom (b : Fin 4 → C) (hcomm : ∀ i j, b i * b j = b j * b i)
    (hsq : ∀ i, b i * b i = 1) : N4 →* C :=
  MonoidHom.noncommPiCoprod (fun i => unitsHom (b i) (hsq i)) (bHom_pairwise b hcomm hsq)

theorem bHom_mulSingle (b : Fin 4 → C) (hcomm : ∀ i j, b i * b j = b j * b i)
    (hsq : ∀ i, b i * b i = 1) (i : Fin 4) (u : ℤˣ) :
    bHom b hcomm hsq (Pi.mulSingle i u) = unitsHom (b i) (hsq i) u :=
  MonoidHom.noncommPiCoprod_mulSingle (fun i => unitsHom (b i) (hsq i)) i u

theorem bHom_range (b : Fin 4 → C) (hcomm : ∀ i j, b i * b j = b j * b i)
    (hsq : ∀ i, b i * b i = 1) : (bHom b hcomm hsq).range = Subgroup.closure (Set.range b) := by
  unfold bHom
  rw [MonoidHom.noncommPiCoprod_range]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rintro _ ⟨u, rfl⟩
    rcases unitsHom_cases (b i) (hsq i) u with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.subset_closure ⟨i, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_iSup_of_mem i ⟨-1, unitsHom_neg_one _ _⟩

theorem bHom_injective (b : Fin 4 → C) (hcomm : ∀ i j, b i * b j = b j * b i)
    (hsq : ∀ i, b i * b i = 1) (hcard : Nat.card (Subgroup.closure (Set.range b)) = 16) :
    Function.Injective (bHom b hcomm hsq) := by
  have hsurj : Function.Surjective (bHom b hcomm hsq).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hc : Nat.card (bHom b hcomm hsq).range = 16 := by
    rw [bHom_range]; exact hcard
  have hbij : Function.Bijective (bHom b hcomm hsq).rangeRestrict := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hc, card_N4]
  intro x y hxy
  apply hbij.1
  exact Subtype.ext hxy

theorem bHom_compat (b : Fin 4 → C) (hcomm : ∀ i j, b i * b j = b j * b i)
    (hsq : ∀ i, b i * b i = 1) (s : Perm (Fin 4) →* C)
    (hs : ∀ π i, s π * b i * (s π)⁻¹ = b (π i)) (π : Perm (Fin 4)) :
    (bHom b hcomm hsq).comp (MulEquiv.toMonoidHom (actHom π)) =
      (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp (bHom b hcomm hsq) := by
  apply MonoidHom.pi_ext
  intro i u
  have e1 : (actHom π) (Pi.mulSingle i u) = Pi.mulSingle (π i) u := act_mulSingle π i u
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e1, bHom_mulSingle, MulAut.conj_apply]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [unitsHom_neg_one, unitsHom_neg_one, hs]

theorem lift_injective (θ : N4 →* C) (hθ : Function.Injective θ) (s : Perm (Fin 4) →* C)
    (hcompat : ∀ π, θ.comp (MulEquiv.toMonoidHom (actHom π)) =
      (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp θ) :
    Function.Injective (SemidirectProduct.lift θ s hcompat) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  obtain ⟨ε, π⟩ := g
  have hg' : θ ε * s π = 1 := by
    have : SemidirectProduct.lift θ s hcompat ⟨ε, π⟩ = θ ε * s π := by
      rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul]
      simp only [SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
    rw [← this]; exact hg
  have h1 : s π = (θ ε)⁻¹ := eq_inv_of_mul_eq_one_right hg'
  have hπ : π = 1 := by
    refine Equiv.ext fun j => ?_
    have h2 : θ (act π (Pi.mulSingle j (-1 : ℤˣ))) = θ (Pi.mulSingle j (-1 : ℤˣ)) := by
      have hc := congrArg (fun f => f (Pi.mulSingle j (-1 : ℤˣ))) (hcompat π)
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
      have hcomm : θ (Pi.mulSingle j (-1 : ℤˣ)) * θ ε = θ ε * θ (Pi.mulSingle j (-1 : ℤˣ)) := by
        rw [← map_mul, ← map_mul, mul_comm]
      have : (actHom π) (Pi.mulSingle j (-1 : ℤˣ)) = act π (Pi.mulSingle j (-1 : ℤˣ)) := rfl
      rw [this] at hc
      rw [hc, h1]
      calc (θ ε)⁻¹ * θ (Pi.mulSingle j (-1 : ℤˣ)) * ((θ ε)⁻¹)⁻¹
          = (θ ε)⁻¹ * (θ (Pi.mulSingle j (-1 : ℤˣ)) * θ ε) := by group
        _ = (θ ε)⁻¹ * (θ ε * θ (Pi.mulSingle j (-1 : ℤˣ))) := by rw [hcomm]
        _ = θ (Pi.mulSingle j (-1 : ℤˣ)) := by group
    have h3 := hθ h2
    rw [act_mulSingle] at h3
    by_contra hne
    have h4 := congrFun h3 (π j)
    simp only [Pi.mulSingle_apply] at h4
    have hne' : π j ≠ j := hne
    simp [hne'] at h4
  subst hπ
  rw [map_one, mul_one] at hg'
  have hε : ε = 1 := hθ (by rw [hg', map_one])
  subst hε
  exact Subgroup.mem_bot.2 rfl

theorem exists_mulEquiv_W' [Finite C] (θ : N4 →* C) (hθ : Function.Injective θ)
    (s : Perm (Fin 4) →* C)
    (hcompat : ∀ π, θ.comp (MulEquiv.toMonoidHom (actHom π)) =
      (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp θ)
    (hC : Nat.card C = 384) : Nonempty (W ≃* C) :=
  ⟨MulEquiv.ofBijective _ ((lift_injective θ hθ s hcompat).bijective_of_nat_card_le
    (by rw [card_W, hC]))⟩

end Recognition

abbrev Z3 : Type := Multiplicative (ZMod 3)

@[expose] def invAut : MulAut Z3 := MulEquiv.inv Z3

theorem invAut_apply (x : Z3) : invAut x = x⁻¹ := rfl

theorem invAut_sq : invAut * invAut = 1 := by
  refine MulEquiv.ext fun x => ?_
  exact inv_inv x

@[expose] def prodW : W →* ℤˣ :=
  SemidirectProduct.lift prodHom 1 (fun π => by
    ext ε
    simp [prodHom_act, actHom])

theorem prodW_mk (ε : N4) (π : Perm (Fin 4)) : prodW ⟨ε, π⟩ = prodHom ε := by
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul]
  simp [prodW]

@[expose] def chiW : W →* MulAut Z3 := (unitsHom invAut invAut_sq).comp prodW

abbrev W7 : Type := Z3 ⋊[chiW] W

theorem card_W7 : Nat.card W7 = 1152 := by
  rw [SemidirectProduct.card, card_W, Nat.card_eq_fintype_card]
  simp

section Recognition7

variable {C : Type*} [Group C]

theorem pow_mod_three (w : C) (hw : w ^ 3 = 1) (x : ℕ) : w ^ (x % 3) = w ^ x := by
  conv_rhs => rw [← Nat.mod_add_div x 3, pow_add, pow_mul, hw, one_pow, mul_one]

@[expose] def wHom (w : C) (hw : w ^ 3 = 1) : Z3 →* C where
  toFun z := w ^ (Multiplicative.toAdd z).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add, pow_mod_three w hw, pow_add]

theorem wHom_apply (w : C) (hw : w ^ 3 = 1) (z : Z3) :
    wHom w hw z = w ^ (Multiplicative.toAdd z).val := rfl

theorem wHom_eq_one (w : C) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) (z : Z3) (h : wHom w hw z = 1) :
    z = 1 := by
  rw [wHom_apply] at h
  have hv : (Multiplicative.toAdd z).val < 3 := ZMod.val_lt _
  have h0 : (Multiplicative.toAdd z).val = 0 := by
    by_contra hne
    have : (Multiplicative.toAdd z).val = 1 ∨ (Multiplicative.toAdd z).val = 2 := by omega
    rcases this with h1 | h2
    · rw [h1, pow_one] at h; exact hw1 h
    · rw [h2] at h
      apply hw1
      calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
        _ = 1 := by rw [hw, h]; simp
  have : Multiplicative.toAdd z = 0 := (ZMod.val_eq_zero _).1 h0
  exact this

theorem exists_mulEquiv_W7 [Finite C] (θ : N4 →* C) (hθ : Function.Injective θ)
    (s : Perm (Fin 4) →* C)
    (hcompat : ∀ π, θ.comp (MulEquiv.toMonoidHom (actHom π)) =
      (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp θ)
    (w : C) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hθw : ∀ ε, θ ε * w * (θ ε)⁻¹ = if prodHom ε = 1 then w else w⁻¹)
    (hsw : ∀ π, s π * w * (s π)⁻¹ = w)
    (hdisj : ∀ ε π, θ ε * s π ∈ Subgroup.zpowers w → θ ε * s π = 1)
    (hC : Nat.card C = 1152) : Nonempty (W7 ≃* C) := by
  let Φ : W →* C := SemidirectProduct.lift θ s hcompat
  have hΦ : ∀ ε π, Φ ⟨ε, π⟩ = θ ε * s π := by
    intro ε π
    rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul]
    simp only [Φ, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  have hΦw : ∀ g : W, Φ g * w * (Φ g)⁻¹ = if prodW g = 1 then w else w⁻¹ := by
    rintro ⟨ε, π⟩
    rw [hΦ, prodW_mk, ← hθw ε]
    have := hsw π
    calc θ ε * s π * w * (θ ε * s π)⁻¹ = θ ε * (s π * w * (s π)⁻¹) * (θ ε)⁻¹ := by group
      _ = θ ε * w * (θ ε)⁻¹ := by rw [this]
  have hcompat7 : ∀ g : W, (wHom w hw3).comp (MulEquiv.toMonoidHom (chiW g)) =
      (MulEquiv.toMonoidHom (MulAut.conj (Φ g))).comp (wHom w hw3) := by
    intro g
    refine MonoidHom.ext fun z => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hcg : chiW g z = if prodW g = 1 then z else z⁻¹ := by
      show (unitsHom invAut invAut_sq (prodW g)) z = _
      by_cases h : prodW g = 1
      · simp [unitsHom, h]
      · simp [unitsHom, h, invAut_apply]
    have hw' := hΦw g
    have hpow : Φ g * wHom w hw3 z * (Φ g)⁻¹ =
        (Φ g * w * (Φ g)⁻¹) ^ (Multiplicative.toAdd z).val := by
      rw [wHom_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
    rw [hpow, hw', hcg]
    by_cases h : prodW g = 1
    · simp [h, wHom_apply]
    · simp only [h, ↓reduceIte]
      exact (map_inv (wHom w hw3) z).trans (by rw [wHom_apply, inv_pow])
  let Φ7 : W7 →* C := SemidirectProduct.lift (wHom w hw3) Φ hcompat7
  have hΦ7 : ∀ z g, Φ7 ⟨z, g⟩ = wHom w hw3 z * Φ g := by
    intro z g
    rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul]
    simp only [Φ7, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  have hinj : Function.Injective Φ7 := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨z, ⟨ε, π⟩⟩ hg
    rw [MonoidHom.mem_ker, hΦ7] at hg
    have h1 : Φ ⟨ε, π⟩ = (wHom w hw3 z)⁻¹ := eq_inv_of_mul_eq_one_right hg
    have h2 : θ ε * s π ∈ Subgroup.zpowers w := by
      rw [← hΦ, h1, wHom_apply]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _)
    have h3 : Φ ⟨ε, π⟩ = 1 := by rw [hΦ]; exact hdisj ε π h2
    have hg1 : (⟨ε, π⟩ : W) = 1 :=
      lift_injective θ hθ s hcompat (by rw [map_one]; exact h3)
    have hz : wHom w hw3 z = 1 := by
      rw [h3] at h1
      exact inv_eq_one.1 h1.symm
    have hz1 : z = 1 := wHom_eq_one w hw3 hw1 z hz
    rw [Subgroup.mem_bot]
    subst hz1
    rw [hg1]
    rfl
  have hbij : Function.Bijective Φ7 :=
    hinj.bijective_of_nat_card_le (by rw [card_W7, hC])
  exact ⟨MulEquiv.ofBijective Φ7 hbij⟩

end Recognition7

end CFSG.GH74.GLS.C3.Layer2.L4.Wreath
