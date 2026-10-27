module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace LinClosure

open Subgroup QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Γ : Subgroup (V ≃ₗ[K] V)}

@[expose] def repG (E : Subgroup Γ) : Representation K E V where
  toFun e := ((e : Γ) : V ≃ₗ[K] V).toLinearMap
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem repG_apply (E : Subgroup Γ) (e : E) (x : V) : repG E e x = (e : Γ) • x := rfl

theorem exists_invariant_complG [CharP K 2] (E : Subgroup Γ) [Finite E]
    (hE : Odd (Nat.card E)) (W : Submodule K V) (hW : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) :
    ∃ W' : Submodule K V, IsCompl W W' ∧ ∀ e ∈ E, ∀ x ∈ W', e • x ∈ W' := by
  have : NeZero (Nat.card E : K) := ⟨by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 (Nat.card E)).1 h
    exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 this)⟩
  let σ : Subrepresentation (repG E) := ⟨W, fun g v hv => by
    rw [repG_apply]; exact hW g g.2 v hv⟩
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
    rwa [repG_apply] at this

section Average

variable (β₀ : LinearMap.BilinForm K V) (E : Subgroup Γ) [Fintype E]

@[expose] def sumFormG : LinearMap.BilinForm K V :=
  ∑ e : E, β₀.compl₁₂ (((e : Γ)⁻¹ : Γ) : V ≃ₗ[K] V).toLinearMap
    (((e : Γ)⁻¹ : Γ) : V ≃ₗ[K] V).toLinearMap

theorem sumFormG_apply (x y : V) :
    sumFormG β₀ E x y = ∑ e : E, β₀ ((e : Γ)⁻¹ • x) ((e : Γ)⁻¹ • y) := by
  simp [sumFormG, LinearMap.sum_apply]
  rfl

theorem sumFormG_smul (f : E) (x y : V) :
    sumFormG β₀ E ((f : Γ) • x) ((f : Γ) • y) = sumFormG β₀ E x y := by
  rw [sumFormG_apply, sumFormG_apply]
  refine Fintype.sum_equiv (Equiv.mulLeft f⁻¹) _ _ (fun e => ?_)
  simp [mul_smul]

end Average

theorem eq_of_pair_eq {B : LinearMap.BilinForm K V} (hnd : B.Nondegenerate) {u u' : V}
    (h : ∀ y, B u y = B u' y) : u = u' := by
  have := hnd.1 (u - u') (fun y => by rw [map_sub, LinearMap.sub_apply, h y, sub_self])
  exact sub_eq_zero.1 this

section Complement

variable [CharP K 2] [FiniteDimensional K V]

theorem exists_singular_compl (Q : QuadraticForm K V) (hnd : (polarBilin Q).Nondegenerate)
    (β₀ : LinearMap.BilinForm K V) (hβ₀ : ∀ x, β₀ x x = Q x)
    (hΓ : ∀ g : Γ, ∀ x, Q (g • x) = Q x)
    (E : Subgroup Γ) [Finite E] (hE : Odd (Nat.card E))
    {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) (hWE : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) :
    ∃ X : Submodule K V, IsCompl X (LinearMap.BilinForm.orthogonal (polarBilin Q) W) ∧
      (∀ x ∈ X, Q x = 0) ∧ ∀ e ∈ E, ∀ x ∈ X, e • x ∈ X := by
  classical
  have := Fintype.ofFinite E
  set B : LinearMap.BilinForm K V := polarBilin Q with hB
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hBxy : ∀ x y, B x y = polar Q x y := fun x y => rfl
  have hBsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [hBxy, hBxy, polar_comm]
  have hBalt : B.IsAlt := fun x => by
    rw [hBxy, polar_self, nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul]
  have hBinv : ∀ g : Γ, ∀ x y, B (g • x) (g • y) = B x y := fun g x y => by
    rw [hBxy, hBxy, polar, polar, ← smul_add, hΓ, hΓ, hΓ]
  have hBinv' : ∀ g : Γ, ∀ x y, B (g⁻¹ • x) y = B x (g • y) := fun g x y => by
    rw [← hBinv g (g⁻¹ • x) y, smul_inv_smul]
  set Y := B.orthogonal W with hY
  have hYE : ∀ e ∈ E, ∀ x ∈ Y, e • x ∈ Y := by
    intro e he y hy
    rw [hY, LinearMap.BilinForm.mem_orthogonal_iff] at hy ⊢
    intro n hn
    have hn' : e⁻¹ • n ∈ W := hWE _ (E.inv_mem he) n hn
    have := hy _ hn'
    rwa [hBinv'] at this
  obtain ⟨X, hXc, hXE⟩ := exists_invariant_complG E hE Y hYE
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
  set β : LinearMap.BilinForm K V := (Nat.card E : K)⁻¹ • sumFormG β₀ E with hβ
  have hcard : (Fintype.card E : K) = Nat.card E := by rw [Nat.card_eq_fintype_card]
  have hne : (Nat.card E : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 (Nat.card E)).1 h
    exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 this)
  have hβ_apply : ∀ x y, β x y = (Nat.card E : K)⁻¹ * sumFormG β₀ E x y := by
    intro x y; simp [hβ]
  have hβ_inv : ∀ e ∈ E, ∀ x y, β (e • x) (e • y) = β x y := fun e he x y => by
    rw [hβ_apply, hβ_apply]
    congr 1
    exact sumFormG_smul β₀ E ⟨e, he⟩ x y
  have hβ_diag : ∀ x, β x x = Q x := fun x => by
    rw [hβ_apply, sumFormG_apply]
    have : ∀ e : E, β₀ ((e : Γ)⁻¹ • x) ((e : Γ)⁻¹ • x) = Q x := fun e => by
      rw [hβ₀, hΓ]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  set N : V →ₗ[K] V := (B.toDual hnd).symm.toLinearMap ∘ₗ (β.compl₂ π) with hN
  have hBN : ∀ x y, B (N x) y = β x (π y) := fun x y => by
    have h1 : B.toDual hnd (N x) = β.compl₂ π x := (B.toDual hnd).apply_symm_apply _
    have h2 := congrArg (fun f : Module.Dual K V => f y) h1
    simpa [LinearMap.BilinForm.toDual_def] using h2
  have hNW : ∀ x, N x ∈ W := fun x => by
    have : W = B.orthogonal Y :=
      (LinearMap.BilinForm.orthogonal_orthogonal hnd hBalt.isRefl W).symm
    rw [this]
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 (fun a ha => ?_)
    rw [hBsymm, hBN, hπ_Y a ha, map_zero]
  have hN_smul : ∀ e ∈ E, ∀ x, N (e • x) = e • N x := fun e he x => by
    refine eq_of_pair_eq hnd (fun y => ?_)
    have h1 : B (e • N x) y = B (N x) (e⁻¹ • y) := by
      simpa using hBinv' e⁻¹ (N x) y
    rw [hBN, h1, hBN, hπ_smul e⁻¹ (E.inv_mem he), ← hβ_inv e he x (e⁻¹ • π y), smul_inv_smul]
  have hWY : W ≤ Y := fun w hw => LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn => by
    rw [hBxy]
    have := hW (n + w) (W.add_mem hn hw)
    simp only [polar, this, hW n hn, hW w hw, sub_zero])
  refine ⟨X.map (LinearMap.id + N), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := (Submodule.mem_inf).1 hz
    obtain ⟨x, hx, rfl⟩ := hz1
    simp only [LinearMap.add_apply, LinearMap.id_apply] at hz2 ⊢
    have hxY : x ∈ Y := by
      have := Y.sub_mem hz2 (hWY (hNW x))
      simpa using this
    have : x ∈ X ⊓ Y := ⟨hx, hxY⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    subst this
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ X ⊔ Y := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.mem_sup.2 ⟨x + N x, ⟨x, hx, rfl⟩, a - N x, Y.sub_mem ha (hWY (hNW x)),
      by abel⟩
  · rintro y ⟨x, hx, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply]
    have h1 : polar Q x (N x) = Q x := by
      rw [← hBxy, hBsymm, hBN, hπ_X x hx, hβ_diag]
    rw [QuadraticMap.map_add Q, hW _ (hNW x), add_zero, h1, ← two_mul, h2, zero_mul]
  · intro e he y hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨e • x, hXE e he x hx, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply, smul_add, hN_smul e he x]

end Complement

end LinClosure

end CFSG.LocalAnalysis.RankThreeUC
