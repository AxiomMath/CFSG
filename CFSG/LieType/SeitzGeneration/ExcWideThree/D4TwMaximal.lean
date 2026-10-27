module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxClose
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxEntry
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxBigCell
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldPlanes

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement

section TwMax


theorem sigma_cube_of_orderOf {K : Type} [Field K] {σ : K ≃+* K} (hσ : orderOf σ = 3) (c : K) :
    σ (σ (σ c)) = c := by
  have h3 : σ ^ 3 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  have h : σ * σ * σ = 1 := by
    rw [← pow_three']
    exact h3
  have h2 : (σ * σ * σ) c = c := by
    rw [h]
    rfl
  exact h2

theorem exists_sigma_ne_self {K : Type} [Field K] {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ x : K, σ x ≠ x := by
  by_contra h
  push Not at h
  have h1 : σ = 1 := RingEquiv.ext fun x => by simpa using h x
  rw [h1, orderOf_one] at hσ
  norm_num at hσ

theorem exists_irrational_rootElt_twD4 {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (hσ : orderOf σ = 3)
    (hk3 : 3 ≤ Nat.card (fixSubfield σ))
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {g : adjointGroup Tag.D4 K} (hg : g ∉ fixedSubgroup (d4Twist 1 σ)) :
    ∃ r ∈ fixedSubgroup (d4Twist 1 σ), ∃ r' ∈ fixedSubgroup (d4Twist 1 σ),
      ∃ t : K, t ∉ fixSubfield σ ∧
        xPar (rootOperatorFamily Tag.D4) (d4Root 22) t ∈
          Subgroup.closure ((fixedSubgroup (d4Twist 1 σ) : Set (adjointGroup Tag.D4 K)) ∪
            ((fixedSubgroup (d4Twist 1 σ)).map (MulAut.conj (r * g * r')).toMonoidHom :
              Set (adjointGroup Tag.D4 K))) := by
  classical
  have hσ1 := exists_sigma_ne_self hσ
  have hF : ∀ c ∈ fixSubfield σ, σ c = c := fun c hc => (mem_fixSubfield σ).1 hc
  have hbad : ∃ r ∈ fixedSubgroup (d4Twist 1 σ), ∃ r' ∈ fixedSubgroup (d4Twist 1 σ),
      entry (r * g * r') (negLabel isMaxHeightRoot_d4Root_22.1)
        (rootLabel isMaxHeightRoot_d4Root_22.1) ∉ fixSubfield σ := by
    by_contra h
    push Not at h
    exact hg (mem_fixedSubgroup_of_entries_twD4 hσ3 hσ1 hk3 h)
  obtain ⟨r, hr, r', hr', hbadE⟩ := hbad
  have hne0 : entry (r * g * r') (negLabel isMaxHeightRoot_d4Root_22.1)
      (rootLabel isMaxHeightRoot_d4Root_22.1) ≠ 0 :=
    fun h => hbadE (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμ, hψ⟩ := bigCell'_all isMaxHeightRoot_d4Root_22 (r * g * r') hne0
  set H := Subgroup.closure ((fixedSubgroup (d4Twist 1 σ) : Set (adjointGroup Tag.D4 K)) ∪
      ((fixedSubgroup (d4Twist 1 σ)).map (MulAut.conj (r * g * r')).toMonoidHom :
        Set (adjointGroup Tag.D4 K))) with hH
  have hu : ∀ c ∈ fixSubfield σ, ψ (u2 (μ₁ * c)) ∈ H := fun c hc => by
    rw [(hψ c).1]
    exact Subgroup.subset_closure (Or.inl (xPar_theta_mem_fixed hσ3 (hF c hc)))
  have hl : ∀ c ∈ fixSubfield σ, ψ (l2 (μ₂ * c)) ∈ H := fun c hc => by
    rw [(hψ c).2]
    exact Subgroup.subset_closure (Or.inr ⟨xPar (rootOperatorFamily Tag.D4) (d4Root 22) c,
      xPar_theta_mem_fixed hσ3 (hF c hc), by simp [MulAut.conj_apply, mul_assoc]⟩)
  have hlam : μ₁ * μ₂ ∉ fixSubfield σ := by
    rcases hμ with h | h
    · rw [h]
      exact hbadE
    · rw [h]
      exact fun hm => hbadE (by simpa using (fixSubfield σ).neg_mem hm)
  have hfull := sl2_hom_mem_of_pair σ (p := 3) Nat.prime_three (by norm_num) hσ hD ψ μ₁ μ₂
    hμ₁ hlam hu hl
  have hθH : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (d4Root 22) c ∈ H := fun c => by
    rw [← (hψ c).1]
    exact hfull c
  obtain ⟨t, ht⟩ : ∃ t : K, t ∉ fixSubfield σ := by
    obtain ⟨x, hx⟩ := hσ1
    exact ⟨x, fun h => hx ((mem_fixSubfield σ).1 h)⟩
  exact ⟨r, hr, r', hr', t, ht, hθH t⟩

theorem twD4_maximal_of_card_ge_three {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (hk3 : 3 ≤ Nat.card (fixSubfield σ))
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    (M : Subgroup (adjointGroup Tag.D4 K)) (hΓM : fixedSubgroup (d4Twist 1 σ) ≤ M) :
    M = fixedSubgroup (d4Twist 1 σ) ∨ M = ⊤ := by
  classical
  by_cases hM : M ≤ fixedSubgroup (d4Twist 1 σ)
  · exact Or.inl (le_antisymm hM hΓM)
  right
  obtain ⟨g, hgM, hg⟩ : ∃ g ∈ M, g ∉ fixedSubgroup (d4Twist 1 σ) := by
    by_contra h
    push Not at h
    exact hM h
  have hσ3 := sigma_cube_of_orderOf hσ
  obtain ⟨r, hr, r', hr', t, ht, hmem⟩ :=
    exists_irrational_rootElt_twD4 hσ3 hσ hk3 hD hg
  set H := Subgroup.closure ((fixedSubgroup (d4Twist 1 σ) : Set (adjointGroup Tag.D4 K)) ∪
      ((fixedSubgroup (d4Twist 1 σ)).map (MulAut.conj (r * g * r')).toMonoidHom :
        Set (adjointGroup Tag.D4 K))) with hH
  have hrgr : r * g * r' ∈ M := M.mul_mem (M.mul_mem (hΓM hr) hgM) (hΓM hr')
  have hHM : H ≤ M := by
    rw [hH]
    refine (Subgroup.closure_le M).2 ?_
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hΓM hx
    · have e : (MulAut.conj (r * g * r')).toMonoidHom y = (r * g * r') * y * (r * g * r')⁻¹ :=
        rfl
      rw [e]
      exact M.mul_mem (M.mul_mem hrgr (hΓM hy)) (M.inv_mem hrgr)
  have hΓH : fixedSubgroup (d4Twist 1 σ) ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hH_top : H = ⊤ := eq_top_of_theta_twD4 hσ3 hσ hD hΓH ht hmem
  have hMtop : (⊤ : Subgroup (adjointGroup Tag.D4 K)) ≤ M := by
    rw [← hH_top]
    exact hHM
  exact eq_top_iff.2 hMtop

@[expose] def D4TwistedF2Case : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), orderOf σ = 3 →
    Nat.card (fixSubfield σ) = 2 →
    ∀ M : Subgroup (adjointGroup Tag.D4 K), fixedSubgroup (d4Twist 1 σ) ≤ M →
      M = fixedSubgroup (d4Twist 1 σ) ∨ M = ⊤

theorem D4TwistedSubfieldMaximal_of_F2 (hF2 : D4TwistedF2Case) : D4TwistedSubfieldMaximal := by
  intro K _ _ _ σ hσ M hM
  by_cases h2 : Nat.card (fixSubfield σ) = 2
  · exact hF2 K σ hσ h2 M hM
  · have h1 : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
    have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by omega
    have hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ) := by
      by_cases hc : ringChar K = 2
      · exact Or.inr ((card_fixSubfield_eq_two_or_four_dvd σ hc).resolve_left h2)
      · exact Or.inl hc
    exact twD4_maximal_of_card_ge_three hσ hk3 hD M hM

end TwMax

end CFSG.LieType.SeitzGeneration.ExcWideThree
