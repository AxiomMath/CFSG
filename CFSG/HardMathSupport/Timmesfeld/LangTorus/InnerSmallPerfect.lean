module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Root

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false



section Perfect

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem isQuasisimple_componentRootSpan_of_perfect (i : KernelComponent χ)
    (hperf : Group.IsPerfect (componentRootSpan K χ i)) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  obtain ⟨⟨α, hαk⟩, rfl⟩ := Quotient.exists_rep i
  have hα : α ∈ componentRoots χ ⟦⟨α, hαk⟩⟧ := ⟨hαk, rfl⟩
  have : Nontrivial (componentRootSpan K χ ⟦⟨α, hαk⟩⟧) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => ?_
    have h1 : pinnedX τ K α 1 ∈ componentRootSpan K χ ⟦⟨α, hαk⟩⟧ := pinnedX_mem_rootSpan hα 1
    rw [h, Subgroup.mem_bot, ← pinnedX_zero τ K α] at h1
    exact one_ne_zero (pinnedX_injective τ K α h1)
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun N hN => ?_
  by_cases hZ : N ≤ Subgroup.center (componentRootSpan K χ ⟦⟨α, hαk⟩⟧)
  · exact Or.inl hZ
  · exact Or.inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf
      isSolvable_componentBorel_subgroupOf (sup_componentBorel_eq_top hN hZ))

theorem isPerfect_componentRootSpan_of_forall (i : KernelComponent χ)
    (h : ∀ α ∈ componentRoots χ i, ∀ t : K,
      pinnedX τ K α t ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :
    Group.IsPerfect (componentRootSpan K χ i) := by
  refine Subgroup.isPerfect_iff.2 (le_antisymm (Subgroup.commutator_le_self _) ?_)
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact h α hα c

theorem exists_nonorth_partner {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hbig : ∃ α ∈ Ψ, ∃ δ ∈ Ψ, δ ≠ α ∧ δ ≠ -α) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ) :
    ∃ δ ∈ Ψ, δ ≠ α ∧ δ ≠ -α ∧ iform α δ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hS : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hα
    · exact hΨ.neg_mem α hα
  have horth : ∀ a ∈ ({α, -α} : Set (Fin τ.rank → ℤ)), ∀ b ∈ Ψ,
      b ∉ ({α, -α} : Set (Fin τ.rank → ℤ)) → iform a b = 0 := by
    intro a ha b hb hbS
    have hb1 : b ≠ α := fun e => hbS (Or.inl e)
    have hb2 : b ≠ -α := fun e => hbS (Or.inr e)
    have h0 : iform α b = 0 := hcon b hb hb1 hb2
    rcases ha with rfl | rfl
    · exact h0
    · rw [iform_comm, ← neg_one_smul ℤ α, iform_smul_right, iform_comm, h0]
      ring
  rcases hΨ.irreducible _ hS horth with h | h
  · exact absurd (h ▸ Or.inl rfl : α ∈ (∅ : Set (Fin τ.rank → ℤ))) (Set.notMem_empty α)
  · obtain ⟨α0, h0, δ0, hδ0, n1, n2⟩ := hbig
    rw [← h] at h0 hδ0
    rcases h0 with rfl | rfl <;> rcases hδ0 with rfl | rfl
    · exact n1 rfl
    · exact n2 rfl
    · exact n2 (by simp)
    · exact n1 rfl

end Perfect

theorem iform_neg_right_eq {τ : Tag} (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]; ring

theorem iform_neg_left_eq {τ : Tag} (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]; ring

section SimplyLaced

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem iform_self_simplyLaced (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have : τ.symmetrizer j j = 1 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer]
  omega

theorem pinnedX_mem_commutator_simplyLaced (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (i : KernelComponent χ)
    (hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α)
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (t : K) :
    pinnedX τ K α t ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hαr : IsRoot τ α := hΨ.isRoot α hα
  obtain ⟨δ, hδΨ, hne1, hne2, hne0⟩ := exists_nonorth_partner hΨ hbig hα
  obtain ⟨δ', hδ'Ψ, hne1', hne2', hneg⟩ : ∃ δ' ∈ componentRoots χ i, δ' ≠ α ∧ δ' ≠ -α ∧
      iform α δ' < 0 := by
    rcases lt_or_gt_of_ne hne0 with h | h
    · exact ⟨δ, hδΨ, hne1, hne2, h⟩
    · refine ⟨-δ, hΨ.neg_mem δ hδΨ, fun e => hne2 (by rw [← neg_neg δ, e]),
        fun e => hne1 (by rw [← neg_neg δ, e, neg_neg]), ?_⟩
      rw [iform_neg_right_eq]; omega
  have hδ'r : IsRoot τ δ' := hΨ.isRoot δ' hδ'Ψ
  have h2α := iform_self_simplyLaced hτ hαr
  have h2δ := iform_self_simplyLaced hτ hδ'r
  have hsq := iform_sq_lt hαr hδ'r hne1'.symm (fun e => hne2' (by rw [e, neg_neg]))
  have hm1 : iform α δ' = -1 := by
    rw [h2α, h2δ] at hsq
    nlinarith
  have hsumr : IsRoot τ (α + δ') :=
    isRoot_add_of_iform_neg hαr hδ'r (fun e => hne2' (by rw [e, neg_neg])) hneg
  have hβΨ : α + δ' ∈ componentRoots χ i := hΨ.add_mem α hα δ' hδ'Ψ hsumr
  have hγΨ : -δ' ∈ componentRoots χ i := hΨ.neg_mem δ' hδ'Ψ
  have hβr : IsRoot τ (α + δ') := hsumr
  have hγr : IsRoot τ (-δ') := IsRoot.neg hδ'r
  have hne : α + δ' ≠ -δ' := by
    intro e
    have := congrArg (fun x => iform x δ') e
    simp only [iform_add_left, iform_neg_left_eq, hm1, h2δ] at this
    omega
  have hne' : α + δ' ≠ -(-δ') := by
    intro e
    rw [neg_neg] at e
    exact hαr.ne_zero (by simpa using e)
  have hsum : IsRoot τ (α + δ' + -δ') := by simpa using hαr
  obtain ⟨hεc, hform'⟩ := (simply_laced_root_commutator_unit.{0} τ hτ hβr hγr hne hne').1 hsum
  set ε := commConst τ (α + δ') (-δ') (1, 1) with hεdef
  have hε2 : ((ε : K)) * (ε : K) = 1 := by
    rcases hεc with h | h <;> rw [h] <;> simp
  have e := hform' K ((ε : K) * t) 1
  simp only [add_neg_cancel_right] at e
  have e2 : (ε : K) * ((ε : K) * t) * 1 = t := by
    rw [← mul_assoc, hε2, one_mul, mul_one]
  rw [e2] at e
  rw [← e]
  exact Subgroup.commutator_mem_commutator (pinnedX_mem_rootSpan hβΨ _) (pinnedX_mem_rootSpan hγΨ _)

theorem isPerfect_componentRootSpan_simplyLaced
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : KernelComponent χ)
    (hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α) :
    Group.IsPerfect (componentRootSpan K χ i) :=
  isPerfect_componentRootSpan_of_forall i fun α hα t =>
    pinnedX_mem_commutator_simplyLaced hτ i hbig hα t

end SimplyLaced

section NegPartner

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exists_neg_partner {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hbig : ∃ α ∈ Ψ, ∃ δ ∈ Ψ, δ ≠ α ∧ δ ≠ -α) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ) :
    ∃ δ ∈ Ψ, δ ≠ α ∧ δ ≠ -α ∧ iform α δ < 0 := by
  obtain ⟨δ, hδΨ, hne1, hne2, hne0⟩ := exists_nonorth_partner hΨ hbig hα
  rcases lt_or_gt_of_ne hne0 with h | h
  · exact ⟨δ, hδΨ, hne1, hne2, h⟩
  · refine ⟨-δ, hΨ.neg_mem δ hδΨ, fun e => hne2 (by rw [← neg_neg δ, e]),
      fun e => hne1 (by rw [← neg_neg δ, e, neg_neg]), ?_⟩
    rw [iform_neg_right_eq]; omega

end NegPartner

section Formula

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem pinnedX_mem_commutator_of_formula (i : KernelComponent χ)
    {β γ δ : Fin τ.rank → ℤ} (hβ : β ∈ componentRoots χ i) (hγ : γ ∈ componentRoots χ i)
    {C : K} (hC : C ≠ 0)
    (hform : ∀ c d : K, ⁅pinnedX τ K β c, pinnedX τ K γ d⁆ = pinnedX τ K δ (C * c * d)) (t : K) :
    pinnedX τ K δ t ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have e := hform (C⁻¹ * t) 1
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hC, one_mul] at e
  rw [← e]
  exact Subgroup.commutator_mem_commutator (pinnedX_mem_rootSpan hβ _) (pinnedX_mem_rootSpan hγ _)

end Formula

end CFSG.HardMathSupport.Timmesfeld.LangTorus
