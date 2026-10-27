module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsForm
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}

section Proj

variable (ρ : Representation K A V)

@[expose] noncomputable def projI (I : Finset (Hyperplane A p)) : V →ₗ[K] V :=
  ∑ H ∈ I, ρ.asAlgebraHom (eps K A p (some H))

theorem projI_apply (I : Finset (Hyperplane A p)) (v : V) :
    projI ρ I v = ∑ H ∈ I, ρ.asAlgebraHom (eps K A p (some H)) v := by
  rw [projI, LinearMap.sum_apply]

variable [Finite A] (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem projI_apply_of_mem {I : Finset (Hyperplane A p)} {H : Hyperplane A p} (hH : H ∈ I)
    {v : V} (hv : v ∈ weightSpace ρ H.1) : projI ρ I v = v := by
  classical
  rw [projI_apply, Finset.sum_eq_single H]
  · exact eps_apply_of_mem ρ hp hA hpK (some H) hv
  · intro H' _ hne
    exact eps_apply_of_mem_ne ρ hp hA hpK (fun h => hne (Option.some_injective _ h)) hv
  · intro h
    exact absurd hH h

theorem projI_apply_of_not_mem {I : Finset (Hyperplane A p)} {i : Option (Hyperplane A p)}
    (hi : ∀ H ∈ I, i ≠ some H) {v : V} (hv : v ∈ weightFamily (p := p) ρ i) :
    projI ρ I v = 0 := by
  rw [projI_apply]
  exact Finset.sum_eq_zero fun H hH => eps_apply_of_mem_ne ρ hp hA hpK (hi H hH).symm hv

theorem projI_projI (I : Finset (Hyperplane A p)) (v : V) :
    projI ρ I (projI ρ I v) = projI ρ I v := by
  conv_lhs => rw [projI_apply ρ I v, map_sum]
  rw [projI_apply ρ I v]
  exact Finset.sum_congr rfl fun H hH => projI_apply_of_mem ρ hp hA hpK hH ⟨v, rfl⟩

theorem projI_comm_of_preserves (I : Finset (Hyperplane A p)) (f : V →+ V)
    (hf : ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, f v ∈ weightFamily (p := p) ρ i) (v : V) :
    projI ρ I (f v) = f (projI ρ I v) := by
  rw [projI_apply, projI_apply, map_sum]
  exact Finset.sum_congr rfl fun H _ => eps_comm_of_preserves ρ hp hA hpK f hf (some H) v

theorem range_projI (I : Finset (Hyperplane A p)) :
    LinearMap.range (projI ρ I) = ⨆ H ∈ I, weightSpace ρ H.1 := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [projI_apply]
    exact Submodule.sum_mem _ fun H hH =>
      Submodule.mem_iSup_of_mem H (Submodule.mem_iSup_of_mem hH ⟨v, rfl⟩)
  · exact iSup₂_le fun H hH v hv => ⟨v, projI_apply_of_mem ρ hp hA hpK hH hv⟩

theorem finrank_range_projI [FiniteDimensional K V] (I : Finset (Hyperplane A p)) :
    Module.finrank K (LinearMap.range (projI ρ I)) =
      ∑ H ∈ I, Module.finrank K (weightSpace ρ H.1) := by
  classical
  rw [range_projI ρ hp hA hpK]
  have hS : iSupIndep (weightFamily (p := p) ρ ∘ some) :=
    (iSupIndep_weightFamily ρ hp hA hpK).comp (Option.some_injective _)
  induction I using Finset.induction_on with
  | empty => simp
  | insert H I hHI ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hHI, ← ih]
    have hdis := hS.disjoint_biSup (show H ∉ (↑I : Set (Hyperplane A p)) from hHI)
    simp only [Function.comp_apply, weightFamily_some, Finset.mem_coe] at hdis
    have h := Submodule.finrank_sup_add_finrank_inf_eq (weightSpace ρ H.1)
      (⨆ H' ∈ I, weightSpace ρ H'.1)
    rw [hdis.eq_bot, finrank_bot, add_zero] at h
    exact h

variable (β : V →ₗ[K] V →ₛₗ[σ] K) (hρ : IsIsomRep β ρ)

omit hp hA hpK in
include hρ in
theorem projI_left (I : Finset (Hyperplane A p)) (x y : V) :
    β (projI ρ I x) y = β x (projI ρ I y) := by
  rw [projI_apply, projI_apply, map_sum, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun H _ => eps_left β ρ hρ (some H) x y

end Proj

section Invol

variable (ρ : Representation K A V) [Finite A]
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

@[expose] noncomputable def involLin (I : Finset (Hyperplane A p)) : V →ₗ[K] V :=
  LinearMap.id - (2 : K) • projI ρ I

theorem involLin_apply (I : Finset (Hyperplane A p)) (v : V) :
    involLin ρ I v = v - (2 : K) • projI ρ I v :=
  rfl

include hp hA hpK

theorem involLin_involLin (I : Finset (Hyperplane A p)) (v : V) :
    involLin ρ I (involLin ρ I v) = v := by
  rw [involLin_apply, involLin_apply, map_sub, map_smul, projI_projI ρ hp hA hpK]
  module

@[expose] noncomputable def invol (I : Finset (Hyperplane A p)) : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (involLin ρ I) (involLin_involLin ρ hp hA hpK I)

theorem invol_apply (I : Finset (Hyperplane A p)) (v : V) :
    invol ρ hp hA hpK I v = v - (2 : K) • projI ρ I v :=
  rfl

theorem invol_invol (I : Finset (Hyperplane A p)) (v : V) :
    invol ρ hp hA hpK I (invol ρ hp hA hpK I v) = v :=
  involLin_involLin ρ hp hA hpK I v

theorem invol_apply_of_mem {I : Finset (Hyperplane A p)} {H : Hyperplane A p} (hH : H ∈ I)
    {v : V} (hv : v ∈ weightSpace ρ H.1) : invol ρ hp hA hpK I v = -v := by
  rw [invol_apply, projI_apply_of_mem ρ hp hA hpK hH hv]
  module

theorem invol_apply_of_not_mem {I : Finset (Hyperplane A p)} {i : Option (Hyperplane A p)}
    (hi : ∀ H ∈ I, i ≠ some H) {v : V} (hv : v ∈ weightFamily (p := p) ρ i) :
    invol ρ hp hA hpK I v = v := by
  rw [invol_apply, projI_apply_of_not_mem ρ hp hA hpK hi hv, smul_zero, sub_zero]

theorem invol_comm (I : Finset (Hyperplane A p)) (f : V →+ V)
    (hf : ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, f v ∈ weightFamily (p := p) ρ i) (v : V) :
    invol ρ hp hA hpK I (f v) = f (invol ρ hp hA hpK I v) := by
  rw [invol_apply, invol_apply, projI_comm_of_preserves ρ hp hA hpK I f hf, two_smul, two_smul,
    map_sub, map_add]

variable (β : V →ₗ[K] V →ₛₗ[σ] K) (hρ : IsIsomRep β ρ)

include hρ in
theorem invol_isometry (I : Finset (Hyperplane A p)) (x y : V) :
    β (invol ρ hp hA hpK I x) (invol ρ hp hA hpK I y) = β x y := by
  have h1 : β (projI ρ I x) y = β x (projI ρ I y) := projI_left ρ β hρ I x y
  have h2 : β (projI ρ I x) (projI ρ I y) = β x (projI ρ I y) := by
    rw [projI_left ρ β hρ, projI_projI ρ hp hA hpK]
  have hσ : σ 2 = 2 := map_ofNat σ 2
  rw [invol_apply, invol_apply]
  simp only [map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, hσ,
    smul_eq_mul]
  ring

include hρ in
theorem exists_involution (I : Finset (Hyperplane A p)) :
    ∃ z : V ≃ₗ[K] V, (∀ x y, β (z x) (z y) = β x y) ∧ (∀ v, z (z v) = v) ∧
      (∀ H ∈ I, ∀ v ∈ weightSpace ρ H.1, z v = -v) ∧
      (∀ i : Option (Hyperplane A p), (∀ H ∈ I, i ≠ some H) →
        ∀ v ∈ weightFamily (p := p) ρ i, z v = v) ∧
      ∀ f : V →+ V, (∀ i, ∀ v ∈ weightFamily (p := p) ρ i, f v ∈ weightFamily (p := p) ρ i) →
        ∀ v, z (f v) = f (z v) :=
  ⟨invol ρ hp hA hpK I, invol_isometry ρ hp hA hpK β hρ I, invol_invol ρ hp hA hpK I,
    fun _ hH _ hv => invol_apply_of_mem ρ hp hA hpK hH hv,
    fun _ hi _ hv => invol_apply_of_not_mem ρ hp hA hpK hi hv,
    fun f hf v => invol_comm ρ hp hA hpK I f hf v⟩

omit hρ β

theorem det_invol [FiniteDimensional K V] (I : Finset (Hyperplane A p)) :
    LinearMap.det (invol ρ hp hA hpK I : V →ₗ[K] V) =
      (-1) ^ ∑ H ∈ I, Module.finrank K (weightSpace ρ H.1) := by
  have hP := projI_projI ρ hp hA hpK I
  have hproj : LinearMap.IsProj (LinearMap.range (projI ρ I)) (projI ρ I) :=
    ⟨fun x => LinearMap.mem_range_self _ x, fun x hx => by obtain ⟨y, rfl⟩ := hx; exact hP y⟩
  have hC := hproj.isCompl
  set e := Submodule.prodEquivOfIsCompl _ _ hC
  have hconj : e.symm.toLinearMap ∘ₗ (invol ρ hp hA hpK I).toLinearMap ∘ₗ e.toLinearMap =
      LinearMap.prodMap (-LinearMap.id) LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, w⟩ := x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.prodMap_apply,
      LinearMap.neg_apply, LinearMap.id_apply]
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', invol_apply, map_add]
    have hu : projI ρ I u = u := hproj.2 u u.2
    have hw : projI ρ I w = 0 := w.2
    rw [hu, hw, add_zero, Submodule.coe_neg]
    module
  have h := LinearMap.det_conj (invol ρ hp hA hpK I : V →ₗ[K] V) e.symm
  rw [LinearEquiv.symm_symm, hconj, LinearMap.det_prodMap, LinearMap.det_id, mul_one,
    ← neg_one_smul K LinearMap.id, LinearMap.det_smul, LinearMap.det_id, mul_one,
    finrank_range_projI ρ hp hA hpK I] at h
  exact h.symm

theorem det_invol_pair [FiniteDimensional K V] [DecidableEq (Hyperplane A p)]
    {H H' : Hyperplane A p} (hne : H ≠ H') :
    LinearMap.det (invol ρ hp hA hpK {H, H'} : V →ₗ[K] V) =
      (-1) ^ (Module.finrank K (weightSpace ρ H.1) + Module.finrank K (weightSpace ρ H'.1)) := by
  rw [det_invol, Finset.sum_pair hne]

end Invol

theorem exists_pair_eq_of_three_le {ι γ : Type*} [DecidableEq γ] (T : Finset ι) (f : ι → γ)
    (C : Finset γ) (hC : C.card ≤ 2) (hf : ∀ i ∈ T, f i ∈ C) (h3 : 3 ≤ T.card) :
    ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ f i = f j :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by omega) hf

theorem exists_pair_even_finrank (ρ : Representation K A V) (T : Finset (Hyperplane A p))
    (h3 : 3 ≤ T.card) :
    ∃ H ∈ T, ∃ H' ∈ T, H ≠ H' ∧
      Even (Module.finrank K (weightSpace ρ H.1) + Module.finrank K (weightSpace ρ H'.1)) := by
  classical
  obtain ⟨H, hH, H', hH', hne, heq⟩ := exists_pair_eq_of_three_le T
    (fun H : Hyperplane A p => decide (Even (Module.finrank K (weightSpace ρ H.1))))
    Finset.univ (by simp) (fun _ _ => Finset.mem_univ _) h3
  refine ⟨H, hH, H', hH', hne, ?_⟩
  rw [Nat.even_add]
  simpa using heq

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
