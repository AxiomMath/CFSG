module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A2
public import CFSG.Monster.B.E6.StdF4FiberRoots
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Kind

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.Monster.B.E6.StdF4 CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2

section Conns


theorem twE6D5_eq_rootsOf :
    twE6D5 = kacE6.rootsOf (↑sD5a : Set (Option (Fin Tag.E6.rank))) := by
  have hmem : ∀ j : Fin Tag.E6.rank, (some j : Option (Fin Tag.E6.rank)) ∉ sD5a → j = 0 := by
    intro j hj
    by_contra hj0
    fin_cases j
    · exact absurd rfl hj0
    all_goals exact hj (by decide)
  have htest : ∀ γ : Fin Tag.E6.rank → ℤ, kacTest kacE6.θ sD5a γ ↔ γ 0 = 0 := by
    intro γ
    rw [kacTest]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h 0 (by decide)
      · exact absurd h (by decide)
    · intro h0
      left
      intro j hj
      rw [hmem j hj]
      exact h0
  ext γ
  rw [mem_rootsOf_iff kacE6 facts_E6 (C := sD5a) ⟨none, by decide⟩, htest]
  rfl

theorem twE6D5_compRank : compRank twE6D5 = 5 := by
  rw [twE6D5_eq_rootsOf, compRank_rootsOf (K := kacE6) (C := sD5a) facts_E6 ⟨none, by decide⟩]
  exact card_sD5.1

@[expose] def twE6D5List : List (Fin Tag.E6.rank → ℤ) := rootList.filter (fun α => α 0 == 0)

set_option maxRecDepth 400000 in
theorem twE6D5_conn :
    ∀ α ∈ twE6D5List, ∀ β ∈ twE6D5List,
      iform (τ := Tag.E6) α β ≠ 0 ∨ ∃ γ ∈ twE6D5List, iform (τ := Tag.E6) α γ ≠ 0 ∧
        iform (τ := Tag.E6) γ β ≠ 0 := by
  decide +kernel

theorem twE6D5_conn' :
    ∀ α ∈ rootList, ∀ β ∈ rootList, α 0 = 0 → β 0 = 0 →
      iform (τ := Tag.E6) α β ≠ 0 ∨ ∃ γ ∈ rootList, γ 0 = 0 ∧ iform (τ := Tag.E6) α γ ≠ 0 ∧
        iform (τ := Tag.E6) γ β ≠ 0 := by
  intro α hα β hβ hα0 hβ0
  have hα' : α ∈ twE6D5List := List.mem_filter.2 ⟨hα, by rw [beq_iff_eq]; exact hα0⟩
  have hβ' : β ∈ twE6D5List := List.mem_filter.2 ⟨hβ, by rw [beq_iff_eq]; exact hβ0⟩
  rcases twE6D5_conn α hα' β hβ' with h | ⟨γ, hγ, h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨γ, (List.mem_filter.1 hγ).1, ?_, h1, h2⟩
    have h0 := (List.mem_filter.1 hγ).2
    rw [beq_iff_eq] at h0
    exact h0

theorem twE6D5_mk_eq {K : Type} [Field K]
    {a : Fin Tag.E6.rank → Kˣ} (hker : kernelRoots (rootCharHom a) = twE6D5)
    {α β : kernelRoots (rootCharHom a)} :
    (⟦α⟧ : KernelComponent (rootCharHom a)) = ⟦β⟧ := by
  classical
  have hαD : (α : Fin Tag.E6.rank → ℤ) ∈ twE6D5 := by rw [← hker]; exact α.2
  have hβD : (β : Fin Tag.E6.rank → ℤ) ∈ twE6D5 := by rw [← hker]; exact β.2
  rcases twE6D5_conn' α.1 (mem_rootList α.2.1) β.1 (mem_rootList β.2.1) hαD.2 hβD.2 with
    h | ⟨γ, hγ, hγ0, h1, h2⟩
  · exact mk_eq_of_iform_ne_zero h
  · have hγk : γ ∈ kernelRoots (rootCharHom a) := by
      rw [hker]; exact ⟨isRoot_of_mem_rootList hγ, hγ0⟩
    exact (mk_eq_of_iform_ne_zero (α := α) (β := ⟨γ, hγk⟩) h1).trans
      (mk_eq_of_iform_ne_zero (α := ⟨γ, hγk⟩) (β := β) h2)

theorem componentRoots_eq_twE6D5 {K : Type} [Field K]
    {a : Fin Tag.E6.rank → Kˣ} (hker : kernelRoots (rootCharHom a) = twE6D5)
    (i : KernelComponent (rootCharHom a)) :
    componentRoots (rootCharHom a) i = twE6D5 := by
  classical
  ext γ
  constructor
  · rintro ⟨hγ, -⟩
    rw [← hker]; exact hγ
  · intro hγ
    have hγk : γ ∈ kernelRoots (rootCharHom a) := by rw [hker]; exact hγ
    refine ⟨hγk, ?_⟩
    obtain ⟨β, rfl⟩ := Quotient.exists_rep i
    exact twE6D5_mk_eq hker (α := ⟨γ, hγk⟩) (β := β)

theorem twE6D5_no_neg :
    ¬ ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ twE6D5, s = rootReflection γ},
      ∀ γ ∈ twE6D5, w • γ = -γ := by
  have h := not_exists_neg_D5 (C := sD5a) (Or.inl rfl) (1 : WeylGroup Tag.E6)
  simpa [twE6D5_eq_rootsOf, one_smul] using h

end Conns

section Kind


theorem twistKind_ennola_D5 {K : Type} [Field K] {q : ℕ}
    (hq : q.Prime) {ζ : Kˣ} (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → ρ γ = -γ)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    twistKind ρ (rootCharHom (twE6omega1Tuple ζ)) i = .twoD := by
  classical
  have hker : kernelRoots (rootCharHom (twE6omega1Tuple ζ)) = twE6D5 :=
    kernelRoots_omega1 hq hζq hζ1
  have hΨ : componentRoots (rootCharHom (twE6omega1Tuple ζ)) i = twE6D5 :=
    componentRoots_eq_twE6D5 hker i
  have hfin : (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hstab : ∀ γ ∈ componentRoots (rootCharHom (twE6omega1Tuple ζ)) i,
      ρ γ ∈ componentRoots (rootCharHom (twE6omega1Tuple ζ)) i := by
    intro γ hγ
    rw [hΨ] at hγ ⊢
    have hγ' : IsRoot Tag.E6 γ ∧ γ 0 = 0 := hγ
    rw [hρ γ hγ'.1]
    exact ⟨IsRoot.neg hγ'.1, by simp [hγ'.2]⟩
  have hlen : componentOrbitLength ρ (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i) = 1 :=
    componentOrbitLength_eq_one hfin hstab
  have hni : ¬ twistInner (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i)
      ((ρ : (Fin Tag.E6.rank → ℤ) → _)^[1]) := by
    rw [Function.iterate_one]
    rintro ⟨w, hw, hwρ⟩
    refine twE6D5_no_neg ⟨w, ?_, ?_⟩
    · rwa [hΨ] at hw
    · intro γ hγ
      have h1 := hwρ γ (by rw [hΨ]; exact hγ)
      rw [hρ γ hγ.1] at h1
      exact h1.symm
  have hc5 : compRank (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i) = 5 := by
    rw [hΨ]; exact twE6D5_compRank
  have hn40 : (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i).ncard = 40 := by
    rw [hΨ]; exact twE6D5_ncard
  unfold twistKind
  rw [hlen, if_neg hni]
  rw [if_neg (by
    rintro (⟨h6, -⟩ | ⟨h4, -, -⟩)
    · omega
    · omega)]
  rw [if_pos]
  refine ⟨by omega, ?_⟩
  rw [hn40, hc5]

end Kind

section Dictionary


variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
  {σ : K →+* K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω ℓ]
  {Fr : Ω →+* Ω}

theorem twE6C_equiv_cgrp (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    Nonempty (↥⁅thetaFixed Fr, thetaFixed Fr⁆ ≃* ↥(Cgrp K σ Ω)) := by
  obtain ⟨g, hg, hgn⟩ := twE6EnnolaConj hℓ hf hK hFr
  have h := rgrp_derived_eq_map_cgrp hℓ hf hK hσ hFr hg hgn
  exact ⟨(MulEquiv.subgroupCongr h).trans
    (Subgroup.equivMapOfInjective (Cgrp K σ Ω) (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm⟩

end Dictionary

end CFSG.LocalAnalysis.GLTheoremA.Y10F
