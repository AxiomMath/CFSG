module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitMaschke

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem exists_equivariant_left_inv [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (A₁ D' : Submodule F V) (hA₁ : ∀ r ∈ Rh, ∀ v ∈ A₁, r v ∈ A₁)
    (hD' : ∀ r ∈ Rh, ∀ v ∈ D', r v ∈ D')
    (f : V →ₗ[F] V) (hfc : ∀ r ∈ Rh, ∀ v, r (f v) = f (r v))
    (hfinj : ∀ a ∈ A₁, f a = 0 → a = 0) (hdisj : Disjoint D' (A₁.map f)) :
    ∃ g : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) ∧ (∀ v, g v ∈ A₁) ∧
      (∀ v ∈ D', g v = 0) ∧ ∀ a ∈ A₁, g (f a) = a := by
  classical
  set B₁ : Submodule F V := A₁.map f with hB₁
  have hB₁inv : ∀ r ∈ Rh, ∀ v ∈ B₁, r v ∈ B₁ := by
    rintro r hr _ ⟨a, ha, rfl⟩
    exact ⟨r a, hA₁ r hr a ha, (hfc r hr a).symm⟩
  have hW'inv : ∀ r ∈ Rh, ∀ v ∈ B₁ ⊔ D', r v ∈ B₁ ⊔ D' := by
    intro r hr v hv
    obtain ⟨b, hb, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
    rw [semilin_map_add (hs hr)]
    exact Submodule.add_mem_sup (hB₁inv r hr b hb) (hD' r hr d hd)
  obtain ⟨C', hC', hC'inv⟩ := exists_invariant_compl p hp2 Rh hs hR (B₁ ⊔ D') hW'inv
  set E : Submodule F V := D' ⊔ C' with hE
  have hEinv : ∀ r ∈ Rh, ∀ v ∈ E, r v ∈ E := by
    intro r hr v hv
    obtain ⟨d, hd, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    rw [semilin_map_add (hs hr)]
    exact Submodule.add_mem_sup (hD' r hr d hd) (hC'inv r hr c hc)
  have hBE : IsCompl B₁ E := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxB hxE
      obtain ⟨d, hd, c, hc, rfl⟩ := Submodule.mem_sup.mp hxE
      have hcW : c ∈ B₁ ⊔ D' := by
        have : c = (d + c) - d := by abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hxB) (Submodule.mem_sup_right hd)
      have hc0 : c = 0 := Submodule.disjoint_def.mp hC'.disjoint c hcW hc
      subst hc0
      rw [add_zero] at hxB ⊢
      exact Submodule.disjoint_def.mp hdisj d hd hxB
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have h1 : v ∈ (B₁ ⊔ D') ⊔ C' := by rw [hC'.sup_eq_top]; trivial
      rwa [hE, ← sup_assoc]
  set P : V →ₗ[F] V := B₁.projection E hBE with hP
  have hPmem : ∀ v, P v ∈ B₁ := fun v => Submodule.projection_apply_mem hBE v
  have hPleft : ∀ v ∈ B₁, P v = v := fun v hv => Submodule.projection_apply_of_mem_left hBE hv
  have hPright : ∀ v ∈ E, P v = 0 := fun v hv => Submodule.projection_apply_of_mem_right hBE hv
  have hPsub : ∀ v, v - P v ∈ E := fun v => Submodule.sub_projection_mem hBE v
  have hPeq : ∀ r ∈ Rh, ∀ v, P (r v) = r (P v) := by
    intro r hr v
    have h1 : r v = r (P v) + r (v - P v) := by
      rw [← semilin_map_add (hs hr)]
      congr 1
      abel
    rw [h1, map_add, hPleft _ (hB₁inv r hr _ (hPmem v)),
      hPright _ (hEinv r hr _ (hPsub v)), add_zero]
  let f₁ : A₁ →ₗ[F] B₁ := f.restrict (fun x hx => Submodule.mem_map_of_mem hx)
  have hf₁apply : ∀ a : A₁, (f₁ a : V) = f a := fun a => rfl
  have hf₁inj : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero f₁).2 fun a ha => ?_
    refine Subtype.ext (hfinj a a.2 ?_)
    exact congrArg Subtype.val ha
  have hf₁surj : Function.Surjective f₁ := by
    rintro ⟨b, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩
  let e1 : A₁ ≃ₗ[F] B₁ := LinearEquiv.ofBijective f₁ ⟨hf₁inj, hf₁surj⟩
  have he1 : ∀ a : A₁, (e1 a : V) = f a := fun a => rfl
  let Pr : V →ₗ[F] B₁ := B₁.projectionOnto E hBE
  have hPr : ∀ v, (Pr v : V) = P v := fun v => rfl
  refine ⟨A₁.subtype ∘ₗ (e1.symm : B₁ →ₗ[F] A₁) ∘ₗ Pr, ?_, ?_, ?_, ?_⟩
  · intro r hr v
    set a : A₁ := e1.symm (Pr v) with ha
    have hfa : f a = P v := by
      have h1 : e1 a = Pr v := e1.apply_symm_apply (Pr v)
      rw [← he1, h1, hPr]
    have hra : e1 ⟨r a, hA₁ r hr a a.2⟩ = Pr (r v) := by
      refine Subtype.ext ?_
      rw [he1, hPr, hPeq r hr v, ← hfa]
      exact (hfc r hr a).symm
    have : e1.symm (Pr (r v)) = ⟨r a, hA₁ r hr a a.2⟩ := by
      rw [← hra]; exact e1.symm_apply_apply _
    show r (a : V) = ((e1.symm (Pr (r v)) : A₁) : V)
    rw [this]
  · intro v
    exact (e1.symm (Pr v)).2
  · intro v hv
    have : Pr v = 0 := by
      refine Subtype.ext ?_
      rw [hPr]
      exact hPright v (Submodule.mem_sup_left hv)
    show ((e1.symm (Pr v) : A₁) : V) = 0
    rw [this]
    simp
  · intro a ha
    have hfa : f a ∈ B₁ := Submodule.mem_map_of_mem ha
    have h1 : Pr (f a) = ⟨f a, hfa⟩ := Submodule.projectionOnto_apply_of_mem_left hBE hfa
    have h2 : e1.symm ⟨f a, hfa⟩ = ⟨a, ha⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    show ((e1.symm (Pr (f a)) : A₁) : V) = a
    rw [h1, h2]

end CFSG.LieType.ChevTwo.OppCl.TK
