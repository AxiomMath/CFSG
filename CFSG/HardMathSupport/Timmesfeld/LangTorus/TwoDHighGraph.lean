module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighStable
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut

set_option linter.unusedSectionVars false

theorem simplyLaced_of_five_le_rank {τ : Tag} (h : 5 ≤ τ.rank) :
    τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  cases τ <;> simp_all [Tag.rank]

section Linear

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem LangSetup.rho_add (x y : Fin τ.rank → ℤ) : S.ρ (x + y) = S.ρ x + S.ρ y := by
  have h : ∀ z, iform (S.ρ (x + y) - S.ρ x - S.ρ y) (S.ρ z) = 0 := by
    intro z
    rw [iform_sub_left, iform_sub_left, iform_rho, iform_rho, iform_rho, iform_add_left]
    ring
  have h0 := h (S.ρ.symm (S.ρ (x + y) - S.ρ x - S.ρ y))
  rw [Equiv.apply_symm_apply] at h0
  have h1 := eq_zero_of_iform_self_eq_zero h0
  rw [sub_sub, sub_eq_zero] at h1
  exact h1

@[expose] noncomputable def LangSetup.rhoHom : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
  AddMonoidHom.mk' S.ρ S.rho_add

@[expose] noncomputable def LangSetup.rhoTwist (v : WeylGroup τ) :
    (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
  (DistribSMul.toAddMonoidHom (Fin τ.rank → ℤ) v).comp S.rhoHom

theorem LangSetup.rhoTwist_apply (v : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    S.rhoTwist v x = v • S.ρ x :=
  rfl

theorem LangSetup.iform_rhoTwist (v : WeylGroup τ) (x y : Fin τ.rank → ℤ) :
    iform (S.rhoTwist v x) (S.rhoTwist v y) = iform x y := by
  rw [S.rhoTwist_apply, S.rhoTwist_apply, iform_smul, iform_rho]

end Linear

section Graph

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem LangSetup.exists_isGraphTwistT
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ v ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
      (∀ γ ∈ componentRoots (rootCharHom a) i,
        S.rhoTwist v γ ∈ componentRoots (rootCharHom a) i) ∧
      (∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
        S.rhoTwist v γ ∈ posRoots (componentRoots (rootCharHom a) i)) ∧
      IsGraphTwist (componentRoots (rootCharHom a) i) (S.rhoTwist v) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨hni, hcard⟩ := S.twoD_factsT hT i hkind h5
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ := S.image_componentRoots_eq_of_five_leT hT i h5
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  have hρsΨ : ∀ γ ∈ Ψ, S.ρ.symm γ ∈ Ψ := fun γ hγ => by
    rw [← hst] at hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    rwa [Equiv.symm_apply_apply]
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry Ψ S.ρ.symm := by
    refine ⟨⟨hρsΨ, S.ρ.symm.injective.injOn, fun γ hγ => ⟨S.ρ γ, hρΨ γ hγ,
      S.ρ.symm_apply_apply γ⟩⟩, fun γ _ δ _ => ?_, fun γ _ => ?_⟩
    · have h := iform_rho S (S.ρ.symm γ) (S.ρ.symm δ)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    · apply S.ρ.injective
      rw [Equiv.apply_symm_apply, S.frob.neg_eq, Equiv.apply_symm_apply]
  obtain ⟨u, hu, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hg := hf.comp_smul hΨ hu
  have hv : u⁻¹ ∈ componentWeylGroup Ψ := inv_mem hu
  have hδg : ∀ γ, S.rhoTwist u⁻¹ (S.ρ.symm (u • γ)) = γ := fun γ => by
    rw [S.rhoTwist_apply, Equiv.apply_symm_apply, inv_smul_smul]
  have hmaps : ∀ γ ∈ Ψ, S.rhoTwist u⁻¹ γ ∈ Ψ := fun γ hγ =>
    smul_mem_of_mem_componentWeylGroup hΨ hv _ (hρΨ γ hγ)
  have hposδ : ∀ γ ∈ posRoots Ψ, S.rhoTwist u⁻¹ γ ∈ posRoots Ψ := by
    intro γ hγ
    obtain ⟨b, hb, rfl⟩ := hg.exists_posRoots hΨ hpos hγ
    rw [hδg]
    exact hb
  have hiso := S.iform_rhoTwist u⁻¹
  have hinj := injective_of_iform _ hiso
  have hfδ : IsIsometry Ψ (S.rhoTwist u⁻¹) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ _ => hiso γ δ,
      fun γ _ => map_neg _ γ⟩
  have hne : ∃ β ∈ simpleRoots Ψ, S.rhoTwist u⁻¹ β ≠ β := by
    by_contra h
    push Not at h
    apply hni
    refine ⟨u, componentWeylGroup_le Ψ hu, fun γ hγ => ?_⟩
    have h1 := hfδ.eq_self_of_simpleRoots hΨ h hγ
    rw [S.rhoTwist_apply] at h1
    calc S.ρ γ = u • (u⁻¹ • S.ρ γ) := by rw [smul_inv_smul]
      _ = u • γ := by rw [h1]
  have hτ := simplyLaced_of_five_le_rank (le_trans h5 (compRank_le Ψ))
  have hsl : ∀ β ∈ Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  exact ⟨u⁻¹, hv, hmaps, hposδ,
    isGraphTwist_of_twoD hΨ hsl h5 hcard _ hiso hmaps hposδ hne⟩

end Graph

end CFSG.HardMathSupport.Timmesfeld.LangTorus
