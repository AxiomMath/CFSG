module

public import CFSG.Fischer.Rec23
public import CFSG.Sporadic.Fi23.Rigid

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Rec23

theorem nativeFi23_complete
    (ψ : MulAut Blueprint.NativeSporadic.Fi23) :
    ∃ y : Blueprint.NativeSporadic.Fi23, ∀ k, ψ k = y * k * y⁻¹ := by
  obtain ⟨g, hg⟩ := Sporadic.Fi23.fi23_complete polarFacts hyperovalFacts
    (Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts)
    ((Sporadic.Fi23.fi23EquivJ.symm.trans ψ).trans Sporadic.Fi23.fi23EquivJ)
  refine ⟨Sporadic.Fi23.fi23EquivJ.symm g, fun k => Sporadic.Fi23.fi23EquivJ.injective ?_⟩
  have h := congrArg (fun φ : MulAut Sporadic.Fi23.J => φ (Sporadic.Fi23.fi23EquivJ k)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

variable {X : Type} [Group X] {D : Set X}

theorem normal_closure_of_conj (hcls : ∀ g : X, ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    (Subgroup.closure D).Normal where
  conj_mem n hn g := by
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hcls g x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx

end Rec23

theorem fi23_of_localPoints_full
    {X : Type} [Group X] [Finite X] (D : Set X)
    (hcls : ∀ g : X, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : X, g * d * g⁻¹ = e)
    (hne : D.Nonempty)
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hloc : ∀ d ∈ D, Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) D d))
    (hZ : ∀ d ∈ D, ∀ g : X, (∀ f ∈ insert d (LocalClass D d), g * f = f * g) → g = 1 ∨ g = d) :
    (commGraph D).Connected ∧ Subgroup.closure D = ⊤ ∧
      ∃ φ : X ≃* CFSG.Blueprint.NativeSporadic.Fi23,
        ∀ y : X, y ∈ D ↔ IsConj CFSG.Sporadic.Fi23.dFi23 (φ y) := by
  obtain ⟨hconn, φ, hφ⟩ := fi23_of_localPoints D hcls htr hne hinv hprod hloc hZ
  have hN : (Subgroup.closure D).Normal := Rec23.normal_closure_of_conj hcls
  have hstar : ∀ d ∈ D, ∃ f, f ∈ LocalClass D d := fun d hd => by
    obtain ⟨L⟩ := hloc d hd
    exact Rec23.exists_mem_localClass_of_localPoints L
  have hZ0 : Rec23.HasZ D := hZ
  have htop : Subgroup.closure D = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let ψ : MulAut CFSG.Blueprint.NativeSporadic.Fi23 :=
      (φ.symm.trans (MulAut.conjNormal x)).trans φ
    obtain ⟨y, hy⟩ := Rec23.nativeFi23_complete ψ
    let h : Subgroup.closure D := φ.symm y
    have key : ∀ k : Subgroup.closure D, x * (k : X) * x⁻¹ = (h : X) * k * (h : X)⁻¹ := by
      intro k
      have h1 : φ (MulAut.conjNormal x k) = y * φ k * y⁻¹ := by
        have := hy (φ k)
        simpa [ψ] using this
      have h2 : MulAut.conjNormal x k = h * k * h⁻¹ := by
        apply φ.injective
        rw [h1, map_mul, map_mul, map_inv]
        simp [h]
      have h3 := congrArg Subtype.val h2
      rwa [MulAut.conjNormal_apply] at h3
    have hcomm : ∀ d ∈ D, ((h : X)⁻¹ * x) * d = d * ((h : X)⁻¹ * x) := by
      intro d hd
      have := key ⟨d, Subgroup.subset_closure hd⟩
      calc (h : X)⁻¹ * x * d = (h : X)⁻¹ * (x * d * x⁻¹) * x := by group
        _ = (h : X)⁻¹ * ((h : X) * d * (h : X)⁻¹) * x := by rw [this]
        _ = d * ((h : X)⁻¹ * x) := by group
    have hx1 : (h : X)⁻¹ * x = 1 := hZ0.eq_one_of_forall_commute hne hstar hcomm
    have : x = (h : X) := by
      calc x = (h : X) * ((h : X)⁻¹ * x) := by group
        _ = h := by rw [hx1, mul_one]
    rw [this]
    exact h.2
  refine ⟨hconn, htop, ?_⟩
  refine ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ, fun y => ?_⟩
  exact hφ ⟨y, htop.symm ▸ Subgroup.mem_top y⟩

end CFSG.Fischer
