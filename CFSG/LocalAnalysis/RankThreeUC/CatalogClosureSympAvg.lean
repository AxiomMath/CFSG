module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSympIsom

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace SpClosure

open Subgroup

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

@[expose] def repOf (E : Subgroup (isom B)) : Representation K E V where
  toFun e := ((e : isom B) : V ≃ₗ[K] V).toLinearMap
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem repOf_apply (E : Subgroup (isom B)) (e : E) (x : V) :
    repOf E e x = (e : isom B) • x := rfl

theorem exists_invariant_compl [CharP K 2] (E : Subgroup (isom B)) [Finite E]
    (hE : Odd (Nat.card E)) (W : Submodule K V) (hW : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) :
    ∃ W' : Submodule K V, IsCompl W W' ∧ ∀ e ∈ E, ∀ x ∈ W', e • x ∈ W' := by
  have : NeZero (Nat.card E : K) := ⟨by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 (Nat.card E)).1 h
    exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 this)⟩
  let σ : Subrepresentation (repOf E) := ⟨W, fun g v hv => by
    rw [repOf_apply]; exact hW g g.2 v hv⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl σ
  refine ⟨σ'.toSubmodule, ⟨?_, ?_⟩, fun e he x hx => ?_⟩
  · have h := hσ'.1
    rw [disjoint_iff] at h ⊢
    have := congrArg Subrepresentation.toSubmodule h
    rw [Subrepresentation.toSubmodule_inf] at this
    exact this
  · have h := hσ'.2
    rw [codisjoint_iff] at h ⊢
    have := congrArg Subrepresentation.toSubmodule h
    rw [Subrepresentation.toSubmodule_sup] at this
    exact this
  · have := σ'.apply_mem_toSubmodule ⟨e, he⟩ hx
    rwa [repOf_apply] at this

section Average

variable (β₀ : LinearMap.BilinForm K V) (E : Subgroup (isom B)) [Fintype E]

@[expose] def sumForm : LinearMap.BilinForm K V :=
  ∑ e : E, β₀.compl₁₂ (((e : isom B)⁻¹ : isom B) : V ≃ₗ[K] V).toLinearMap
    (((e : isom B)⁻¹ : isom B) : V ≃ₗ[K] V).toLinearMap

theorem sumForm_apply (x y : V) :
    sumForm β₀ E x y = ∑ e : E, β₀ ((e : isom B)⁻¹ • x) ((e : isom B)⁻¹ • y) := by
  simp [sumForm, LinearMap.sum_apply]
  rfl

theorem sumForm_smul (f : E) (x y : V) :
    sumForm β₀ E ((f : isom B) • x) ((f : isom B) • y) = sumForm β₀ E x y := by
  rw [sumForm_apply, sumForm_apply]
  refine Fintype.sum_equiv (Equiv.mulLeft f⁻¹) _ _ (fun e => ?_)
  simp [mul_smul]

theorem sumForm_swap (hβ₀ : ∀ x y, β₀ x y + β₀ y x = B x y) (x y : V) :
    sumForm β₀ E x y + sumForm β₀ E y x = (Fintype.card E : K) * B x y := by
  rw [sumForm_apply, sumForm_apply, ← Finset.sum_add_distrib]
  have : ∀ e : E, β₀ ((e : isom B)⁻¹ • x) ((e : isom B)⁻¹ • y) +
      β₀ ((e : isom B)⁻¹ • y) ((e : isom B)⁻¹ • x) = B x y := fun e => by
    rw [hβ₀, B_smul]
  simp [this]

end Average

theorem eq_of_B_eq (hnd : B.Nondegenerate) {u u' : V} (h : ∀ y, B u y = B u' y) : u = u' := by
  have := hnd.1 (u - u') (fun y => by rw [map_sub, LinearMap.sub_apply, h y, sub_self])
  exact sub_eq_zero.1 this

section Complement

variable [CharP K 2] [FiniteDimensional K V]

theorem exists_isotropic_compl (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (β₀ : LinearMap.BilinForm K V) (hβ₀ : ∀ x y, β₀ x y + β₀ y x = B x y)
    (E : Subgroup (isom B)) [Finite E] (hE : Odd (Nat.card E))
    {W : Submodule K V} (hW : W ≤ B.orthogonal W) (hWE : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) :
    ∃ X : Submodule K V, IsCompl X (B.orthogonal W) ∧ X ≤ B.orthogonal X ∧
      ∀ e ∈ E, ∀ x ∈ X, e • x ∈ X := by
  classical
  have := Fintype.ofFinite E
  set Y := B.orthogonal W with hY
  have hYE : ∀ e ∈ E, ∀ x ∈ Y, e • x ∈ Y := fun e he x hx =>
    (smul_mem_orth_iff (le_stab_of_invariant hWE he) x).2 hx
  obtain ⟨X, hXc, hXE⟩ := exists_invariant_compl E hE Y hYE
  have hc : IsCompl X Y := hXc.symm
  set π : V →ₗ[K] V := X.subtype ∘ₗ X.projectionOnto Y hc with hπ
  have hπX : ∀ x, π x ∈ X := fun x => (X.projectionOnto Y hc x).2
  have hπ_X : ∀ x ∈ X, π x = x := fun x hx => by
    have := Submodule.projectionOnto_apply_left hc ⟨x, hx⟩
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val this
  have hπ_Y : ∀ a ∈ Y, π a = 0 := fun a ha => by
    have := Submodule.projectionOnto_apply_right hc ⟨a, ha⟩
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]; rfl
  have hπ_sub : ∀ x, x - π x ∈ Y := fun x => by
    rw [← Submodule.ker_projectionOnto hc, LinearMap.mem_ker, map_sub]
    have := Submodule.projectionOnto_apply_left hc (X.projectionOnto Y hc x)
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this, sub_self]
  have hπ_smul : ∀ e ∈ E, ∀ x, π (e • x) = e • π x := fun e he x => by
    have h1 : e • x = e • π x + e • (x - π x) := by rw [← smul_add]; congr 1; abel
    rw [h1, map_add, hπ_X _ (hXE e he _ (hπX x)), hπ_Y _ (hYE e he _ (hπ_sub x)), add_zero]
  set β : LinearMap.BilinForm K V := (Nat.card E : K)⁻¹ • sumForm β₀ E with hβ
  have hcard : (Fintype.card E : K) = Nat.card E := by rw [Nat.card_eq_fintype_card]
  have hne : (Nat.card E : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 (Nat.card E)).1 h
    exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 this)
  have hβ_apply : ∀ x y, β x y = (Nat.card E : K)⁻¹ * sumForm β₀ E x y := by
    intro x y; simp [hβ]
  have hβ_inv : ∀ e ∈ E, ∀ x y, β (e • x) (e • y) = β x y := fun e he x y => by
    rw [hβ_apply, hβ_apply]
    congr 1
    exact sumForm_smul β₀ E ⟨e, he⟩ x y
  have hβ_sw : ∀ x y, β x y + β y x = B x y := fun x y => by
    rw [hβ_apply, hβ_apply, ← mul_add, sumForm_swap β₀ E hβ₀, hcard, ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]
  set N : V →ₗ[K] V := (B.toDual hnd).symm.toLinearMap ∘ₗ (β.compl₂ π) with hN
  have hBN : ∀ x y, B (N x) y = β x (π y) := fun x y => by
    have h1 : B.toDual hnd (N x) = β.compl₂ π x := (B.toDual hnd).apply_symm_apply _
    have h2 := congrArg (fun f : Module.Dual K V => f y) h1
    simpa [LinearMap.BilinForm.toDual_def] using h2
  have hNW : ∀ x, N x ∈ W := fun x => by
    have : W = B.orthogonal Y := (LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl W).symm
    rw [this]
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 (fun a ha => ?_)
    rw [← LinearMap.IsAlt.neg hB (N x) a, hBN, hπ_Y a ha, map_zero, neg_zero]
  have hN_smul : ∀ e ∈ E, ∀ x, N (e • x) = e • N x := fun e he x => by
    refine eq_of_B_eq hnd (fun y => ?_)
    have h1 : B (e • N x) y = B (N x) (e⁻¹ • y) := by simpa using B_inv_smul e⁻¹ (N x) y
    rw [hBN, h1, hBN, hπ_smul e⁻¹ (E.inv_mem he), ← hβ_inv e he x (e⁻¹ • π y), smul_inv_smul]
  refine ⟨X.map (LinearMap.id + N), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := (Submodule.mem_inf).1 hz
    obtain ⟨x, hx, rfl⟩ := hz1
    simp only [LinearMap.add_apply, LinearMap.id_apply] at hz2 ⊢
    have hxY : x ∈ Y := by
      have := Y.sub_mem hz2 (hW (hNW x))
      simpa using this
    have : x ∈ X ⊓ Y := ⟨hx, hxY⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    subst this
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ X ⊔ Y := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.mem_sup.2 ⟨x + N x, ⟨x, hx, rfl⟩, a - N x, Y.sub_mem ha (hW (hNW x)),
      by abel⟩
  · intro y hy
    obtain ⟨x', hx', rfl⟩ := hy
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn => ?_)
    obtain ⟨x, hx, rfl⟩ := hn
    simp only [LinearMap.add_apply, LinearMap.id_apply]
    have e1 : B (N x) x' = β x x' := by rw [hBN, hπ_X x' hx']
    have e2 : B x (N x') = - β x' x := by
      rw [← LinearMap.IsAlt.neg hB (N x') x, hBN, hπ_X x hx]
    have e3 : B (N x) (N x') = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.1 (hW (hNW x')) (N x) (hNW x)
    have hsum : B (x + N x) (x' + N x') = B x x' + B x (N x') + B (N x) x' + B (N x) (N x') := by
      simp only [map_add, LinearMap.add_apply]; ring
    rw [hsum, e1, e2, e3, ← hβ_sw x x']
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (β x x') * h2
  · intro e he y hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨e • x, hXE e he x hx, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply, smul_add, hN_smul e he x]

end Complement

end SpClosure

end CFSG.LocalAnalysis.RankThreeUC
