module

public import CFSG.CharacterTheory.Blocks.InnerProduct

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

@[expose] def centralInvolutionSection {G : Type*} [Group G] (t : G) : Set G :=
  {x | x ∈ Subgroup.centralizer ({t} : Set G) ∧ Even (orderOf x) ∧ x ^ (orderOf x / 2) = t}

theorem mem_centralizer_of_conj_mem_centralInvolutionSection {G : Type*} [Group G]
    {t x c : G} (hx : x ∈ centralInvolutionSection t)
    (hc : c⁻¹ * x * c ∈ centralInvolutionSection t) :
    c ∈ Subgroup.centralizer ({t} : Set G) := by
  have horder : orderOf (c⁻¹ * x * c) = orderOf x := by
    have h := (MulAut.conj c⁻¹).orderOf_eq x
    rwa [MulAut.conj_apply, inv_inv] at h
  have hpow : (c⁻¹ * x * c) ^ (orderOf x / 2) = c⁻¹ * x ^ (orderOf x / 2) * c := by
    have h := conj_pow (a := c⁻¹) (b := x) (i := orderOf x / 2)
    rwa [inv_inv] at h
  have hconj : c⁻¹ * t * c = t := by
    have h := hc.2.2
    rw [horder, hpow, hx.2.2] at h
    exact h
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  calc y * c = c * (c⁻¹ * y * c) := by group
    _ = c * y := by rw [hconj]

theorem central_involution_section_induction_isometry {G : Type} [Group G] [Fintype G]
    (t : G) :
    (∀ α : Subgroup.centralizer ({t} : Set G) → ℂ, BlocksIsClassFunction α →
      (∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∉ centralInvolutionSection t → α x = 0) →
      (∀ x : Subgroup.centralizer ({t} : Set G), (x : G) ∈ centralInvolutionSection t →
        inducedFunction (Subgroup.centralizer ({t} : Set G)) α x = α x) ∧
      (∀ x : G, x ∉ (⋃ g : G, (fun y => g * y * g⁻¹) '' centralInvolutionSection t) →
        inducedFunction (Subgroup.centralizer ({t} : Set G)) α x = 0) ∧
      BlocksInnerProduct (inducedFunction (Subgroup.centralizer ({t} : Set G)) α) 1 =
        BlocksInnerProduct α 1 ∧
      (α ∈ BlocksVChar (Subgroup.centralizer ({t} : Set G)) →
        inducedFunction (Subgroup.centralizer ({t} : Set G)) α ∈ BlocksVChar G)) ∧
    (∀ α β : Subgroup.centralizer ({t} : Set G) → ℂ,
      BlocksIsClassFunction α →
      (∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∉ centralInvolutionSection t → α x = 0) →
      BlocksIsClassFunction β →
      (∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∉ centralInvolutionSection t → β x = 0) →
      BlocksInnerProduct (inducedFunction (Subgroup.centralizer ({t} : Set G)) α)
          (inducedFunction (Subgroup.centralizer ({t} : Set G)) β) =
        BlocksInnerProduct α β) ∧
    Set.InjOn (inducedFunction (Subgroup.centralizer ({t} : Set G)))
      {α | BlocksIsClassFunction α ∧ ∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∉ centralInvolutionSection t → α x = 0} := by
  set C := Subgroup.centralizer ({t} : Set G)
  have hTI : ∀ x ∈ centralInvolutionSection t, ∀ c : G, c ∉ C →
      c⁻¹ * x * c ∉ centralInvolutionSection t :=
    fun x hx c hc hmem => hc (mem_centralizer_of_conj_mem_centralInvolutionSection hx hmem)
  have hon : ∀ α : C → ℂ, BlocksIsClassFunction α →
      (∀ x : C, (x : G) ∉ centralInvolutionSection t → α x = 0) →
      ∀ x : C, (x : G) ∈ centralInvolutionSection t → inducedFunction C α x = α x :=
    fun α hα hsupport x hx => inducedFunction_eq_on_trivial_intersection_support C
      (centralInvolutionSection t) α (fun element conjugator => hα element conjugator)
      hsupport hTI x hx
  refine ⟨fun α hα hsupport => ⟨hon α hα hsupport, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    apply inducedFunction_eq_zero_of_support_avoids_conjugates C (centralInvolutionSection t) α
      hsupport x
    intro c hc
    apply hx
    exact Set.mem_iUnion.mpr ⟨c, c⁻¹ * x * c, hc, by group⟩
  · exact blocksInnerProduct_inducedFunction_left C α 1 (fun _ _ => rfl)
  · intro hvirtual
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hvirtual ⊢
    exact inducedFunction_mem_virtualCharacters C hvirtual
  · intro α β _ hαsupport hβ hβsupport
    rw [blocksInnerProduct_inducedFunction_left C α _
      (fun element conjugator => inducedFunction_conjugate C β element conjugator)]
    unfold BlocksInnerProduct
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    by_cases hx : (x : G) ∈ centralInvolutionSection t
    · rw [hon β hβ hβsupport x hx]
    · rw [hαsupport x hx, zero_mul, zero_mul]
  · intro α hα β hβ hequal
    funext x
    by_cases hx : (x : G) ∈ centralInvolutionSection t
    · rw [← hon α hα.1 hα.2 x hx, ← hon β hβ.1 hβ.2 x hx, hequal]
    · rw [hα.2 x hx, hβ.2 x hx]

end CFSG.Semidihedral.Principal
