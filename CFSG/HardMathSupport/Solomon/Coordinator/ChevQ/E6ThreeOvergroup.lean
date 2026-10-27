module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCellConj
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.PairLemma

open CFSG.LieType.SeitzGeneration
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.CTP

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three



section Overgroup

variable {τ : Tag} {K : Type} [Field K]

theorem mem_subfieldGroup_of_entries_of_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    [Finite K] (σ : K ≃+* K) (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {R : Subgroup ↥(adjointGroup τ K)} (hRσ : R ≤ subfieldGroup τ σ)
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hall : ∀ r ∈ R, ∀ r' ∈ R,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ) :
    g ∈ subfieldGroup τ σ := by
  classical
  have h3 : 3 ≤ Nat.card (fixSubfield σ) := three_le_card_fixSubfield σ hD
  set g₂ : ↥(adjointGroup τ K) := entrywiseAdjointAut τ σ g with hg₂
  have hRfix : ∀ r ∈ R, entrywiseAdjointAut τ σ r = r := fun r hr =>
    mem_fixedSubgroup.1 (hRσ hr)
  have hent : ∀ r ∈ R, ∀ r' ∈ R, entry (r * g₂ * r') (negLabel hθ.1) (rootLabel hθ.1) =
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : r * g₂ * r' = entrywiseAdjointAut τ σ (r * g * r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    exact (mem_fixSubfield σ).1 (hall r hr r' hr')
  set Z := vanishSub R (negLabel hθ.1) with hZ
  have hDmem : ∀ r' ∈ R, (endHom K g₂ - endHom K g) (endHom K r' (rootVec τ K θ)) ∈ Z := by
    intro r' hr'
    refine mem_vanishSub.2 fun r hr => ?_
    have hv : rootVec τ K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply,
      ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hspan := span_orbit_eq_top hτ h3 hrat hθ
  have hle : Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} ≤
      Z.comap (endHom K g₂ - endHom K g) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    exact hDmem r' hr'
  rw [hspan] at hle
  have hDV : ∀ v, (endHom K g₂ - endHom K g) v ∈ Z := fun v =>
    hle (Submodule.mem_top (x := v))
  have hx : ∀ v : RootModule τ K, endHom K (g₂ * g⁻¹) v - v ∈ Z := by
    intro v
    have h1 := hDV (endHom K g⁻¹ v)
    have e1 : endHom K g (endHom K g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact h1
  have h1 := eq_one_of_sub_mem_vanishSub hτ h3 hrat hθ (g₂ * g⁻¹) hx
  have h2 : g₂ = g := mul_inv_eq_one.1 h1
  exact mem_fixedSubgroup.2 h2

theorem exists_bad_entry_of_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K]
    (σ : K ≃+* K) (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {R : Subgroup ↥(adjointGroup τ K)} (hRσ : R ≤ subfieldGroup τ σ)
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hg : g ∉ subfieldGroup τ σ) :
    ∃ r ∈ R, ∃ r' ∈ R, entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield σ := by
  by_contra h
  push Not at h
  exact hg (mem_subfieldGroup_of_entries_of_le hτ σ hD hRσ hrat hθ g h)

theorem exists_irrational_rootElt_of_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {R : Subgroup ↥(adjointGroup τ K)} (hRσ : R ≤ subfieldGroup τ σ)
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ R)
    (g : ↥(adjointGroup τ K)) (hg : g ∉ subfieldGroup τ σ) :
    ∃ r ∈ R, ∃ r' ∈ R, ∃ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ) (t : K), t ∉ fixSubfield σ ∧
      xPar (rootOperatorFamily τ) γ t ∈ Subgroup.closure ((R : Set ↥(adjointGroup τ K)) ∪
        (R.map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K))) := by
  classical
  have hτ4 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with h | h | h <;> simp [h]
  obtain ⟨θ, hθ⟩ := exists_maxHeightRoot τ
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_of_le hτ4 σ hD hRσ hrat hθ g hg
  have hne0 : entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 := fun h =>
    hbad (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμ, hψ⟩ := bigCell' hτ4 hθ (r * g * r') hne0
  have hu : ∀ c ∈ fixSubfield σ, ψ (u2 (μ₁ * c)) ∈ Subgroup.closure
      ((R : Set ↥(adjointGroup τ K)) ∪
        (R.map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K))) :=
    fun c hc => by
      rw [(hψ c).1]
      exact Subgroup.subset_closure (Or.inl (hrat θ hθ.1 c hc))
  have hl : ∀ c ∈ fixSubfield σ, ψ (l2 (μ₂ * c)) ∈ Subgroup.closure
      ((R : Set ↥(adjointGroup τ K)) ∪
        (R.map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K))) :=
    fun c hc => by
      rw [(hψ c).2]
      exact Subgroup.subset_closure (Or.inr ⟨xPar (rootOperatorFamily τ) θ c,
        hrat θ hθ.1 c hc, by simp [MulAut.conj_apply, mul_assoc]⟩)
  have hlam : μ₁ * μ₂ ∉ fixSubfield σ := by
    rcases hμ with h | h
    · rw [h]; exact hbad
    · rw [h]; exact fun hm => hbad (by simpa using (fixSubfield σ).neg_mem hm)
  have hfull := sl2_hom_mem_of_pair σ hp hp2 hσ hD ψ μ₁ μ₂ hμ₁ hlam hu hl
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    have := hp.one_lt
    omega
  obtain ⟨t, ht⟩ : ∃ t : K, σ t ≠ t := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext fun x => by simpa using h x)
  refine ⟨r, hr, r', hr', θ, hθ.1, t, fun h' => ht ((mem_fixSubfield σ).1 h'), ?_⟩
  rw [← (hψ t).1]
  exact hfull t

theorem le_subfieldGroup_or_eq_top_of_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hk2 : Nat.card (fixSubfield σ) ≠ 2) {R : Subgroup ↥(adjointGroup τ K)}
    (hRσ : R ≤ subfieldGroup τ σ)
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ R)
    (M : Subgroup ↥(adjointGroup τ K)) (hRM : R ≤ M) : M ≤ subfieldGroup τ σ ∨ M = ⊤ := by
  have hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ) := by
    by_cases h2 : ringChar K = 2
    · exact Or.inr ((card_fixSubfield_eq_two_or_four_dvd σ h2).resolve_left hk2)
    · exact Or.inl h2
  by_cases hM : M ≤ subfieldGroup τ σ
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ subfieldGroup τ σ := by
    by_contra h
    push Not at h
    exact hM fun g hg => h g hg
  obtain ⟨r, hr, r', hr', γ, hγ, t, ht, hmem⟩ :=
    exists_irrational_rootElt_of_le hτ σ hp hp2 hσ hD hRσ hrat g hgR
  have hgg : r * g * r' ∈ M := mul_mem (mul_mem (hRM hr) hgM) (hRM hr')
  have hHM : Subgroup.closure ((R : Set ↥(adjointGroup τ K)) ∪
      (R.map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K))) ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hRM hx
    · exact M.mul_mem (M.mul_mem hgg (hRM hy)) (M.inv_mem hgg)
  have hRH : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ Subgroup.closure ((R : Set ↥(adjointGroup τ K)) ∪
        (R.map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K))) :=
    fun γ hγ c hc => Subgroup.subset_closure (Or.inl (hrat γ hγ c hc))
  have hHtop := eq_top_of_irrational_rootElt hτ (fixSubfield σ)
    (fun F hF => subfield_eq_or_top σ hp hσ F hF) _ hRH γ hγ t ht hmem
  exact eq_top_iff.2 (hHtop.ge.trans hHM)

end Overgroup

section RootGenerated

variable (τ : Tag) {K : Type} [Field K]

theorem fixedFieldImage_subgroupOf_le_subfieldGroup (σ : K ≃+* K) :
    (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≤ subfieldGroup τ σ := by
  intro g hg
  have h := (mem_entrywiseFixedGroup.1 (fixedFieldImage_le (Subgroup.mem_subgroupOf.1 hg))).2
  exact mem_fixedSubgroup.2 (Subtype.ext ((coe_entrywiseAdjointAut τ σ g).trans h))

theorem xPar_mem_fixedFieldImage_subgroupOf (σ : K ≃+* K) (γ : Fin τ.rank → ℤ) {c : K}
    (hc : c ∈ fixSubfield σ) :
    xPar (rootOperatorFamily τ) γ c ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
  by_cases hγ : IsRoot τ γ
  · rw [Subgroup.mem_subgroupOf]
    have h := (rootOperatorFamily τ).pinnedX_eq_eltUnit K hγ
      (((rootOperatorFamily τ).pinnedFamilySign γ : K) * c)
    rw [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self K γ, one_mul] at h
    have e : ((xPar (rootOperatorFamily τ) γ c : adjointGroup τ K) : ModGL τ K) =
        pinnedX τ K γ (((rootOperatorFamily τ).pinnedFamilySign γ : K) * c) := by
      rw [xPar_of_isRoot hγ, h]
      rfl
    rw [e]
    refine pinnedX_mem_fixedFieldImage γ ?_
    rw [map_mul, map_intCast, (mem_fixSubfield σ).1 hc]
  · rw [xPar_of_not_isRoot hγ]
    exact one_mem _

variable {τ}

theorem le_subfieldGroup_or_eq_top_of_fixedFieldImage_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hk2 : Nat.card (fixSubfield σ) ≠ 2) (M : Subgroup ↥(adjointGroup τ K))
    (hJM : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≤ M) :
    M ≤ subfieldGroup τ σ ∨ M = ⊤ :=
  le_subfieldGroup_or_eq_top_of_le hτ σ hp hp2 hσ hk2
    (fixedFieldImage_subgroupOf_le_subfieldGroup τ σ)
    (fun γ _ _ hc => xPar_mem_fixedFieldImage_subgroupOf τ σ γ hc) M hJM

end RootGenerated

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
