module

public import CFSG.ClassicalInvolution.SmallOrth.PrimitiveTwo
public import CFSG.ClassicalInvolution.SmallOrth.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_ne_zero_sq_ne_one [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ τ : K, τ ≠ 0 ∧ τ ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic Kˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h => ?_⟩
  grw [Nat.card_eq_card_units_add_one K, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at h4
  omega

section Dimension

variable [FiniteDimensional K V]

theorem finrank_le_two_add_finrank_perp (P : HypPair Q) :
    Module.finrank K V ≤ 2 + Module.finrank K P.perp := by
  classical
  have hspan : (⊤ : Submodule K V) ≤ Submodule.span K {P.e, P.f} ⊔ P.perp := by
    intro x _
    rw [P.eq_add_proj x]
    refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.subset_span (by simp)))) (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.subset_span (by simp))))) (Submodule.mem_sup_right (P.proj_mem_perp x))
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_top] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {P.e, P.f}) P.perp
  have h3 := finrank_span_finset_le_card (R := K) ({P.e, P.f} : Finset V)
  have h4 : ({P.e, P.f} : Finset V).card ≤ 2 := Finset.card_le_two
  simp only [Finset.coe_insert, Finset.coe_singleton] at h3
  have h5 : Module.finrank K (Submodule.span K {P.e, P.f}) ≤ 2 := le_trans h3 h4
  omega

theorem four_le_finrank_of_orth {P P' : HypPair Q} (h : P.Orth P') :
    4 ≤ Module.finrank K V := by
  have hli : LinearIndependent K ![P.e, P.f, P'.e, P'.f] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_four] at hg
    have h1 := congrArg (fun z => polar Q z P.f) hg
    have h2 := congrArg (fun z => polar Q z P.e) hg
    have h3 := congrArg (fun z => polar Q z P'.f) hg
    have h4 := congrArg (fun z => polar Q z P'.e) hg
    have hs := h.symm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three, polar_add_left, polar_smul_left_eq, polar_zero_left,
      P.polar_ef, P.polar_fe, P.polar_ee, P.polar_ff, P'.polar_ef, P'.polar_fe, P'.polar_ee,
      P'.polar_ff, h.ee, h.ef, h.fe, h.ff, hs.ee, hs.ef, hs.fe, hs.ff, mul_zero, mul_one,
      add_zero, zero_add] at h1 h2 h3 h4
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have := hli.fintype_card_le_finrank
  simpa using this

end Dimension

section Finite

variable [Finite K] [FiniteDimensional K V]

open CFSG.ComponentClassification.CatalogueBOddQuadratic in
theorem exists_orth_hypPair_of_five_le_finrank (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ Module.finrank K V) (P : HypPair Q) :
    ∃ P' : HypPair Q, P.Orth P' := by
  have hQ' := nondegenerate_polarBilin_restrict (P.polarNondegOn_perp hQ)
  have hdim : 3 ≤ Module.finrank K P.perp := by
    have := finrank_le_two_add_finrank_perp P
    omega
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd (Q.restrict P.perp) hQ' hdim
  obtain ⟨P', hP', -⟩ := exists_orth_hypPair_of_mem_perp hQ P v.2
    (fun h => hv0 (Subtype.ext h)) hvQ
  exact ⟨P', hP'⟩

open CFSG.ComponentClassification.CatalogueBOddQuadratic in
theorem isQuasisimple_elementaryGroup_of_five_le_finrank (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) (hdim : 5 ≤ Module.finrank K V) :
    CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) := by
  obtain ⟨τ, hτ, hτ2⟩ := exists_ne_zero_sq_ne_one (K := K) (by omega)
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ (by omega)
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd Q hQ (by omega)
  obtain ⟨P₁, rfl⟩ := exists_hypPair hQ hvQ hv0
  obtain ⟨P₂, h₁₂⟩ := exists_orth_hypPair_of_five_le_finrank hodd hQ hdim P₁
  have hQ' := nondegenerate_polarBilin_restrict (P₁.polarNondegOn_perp hQ)
  have hdim' : 3 ≤ Module.finrank K P₁.perp := by
    have := finrank_le_two_add_finrank_perp P₁
    omega
  have hA' : HasAnisoPerp (Q.restrict P₁.perp) := hasAnisoPerp_of_three_le_finrank hQ' hdim'
  exact isQuasisimple_elementaryGroup_of_preprimitive P₁ (two_ne_zero_of_odd_card hodd) hQ hA hτ
    hτ2 (isPreprimitive_singularLines_of_orth h₁₂ hQ hA hA')

open CFSG.ComponentClassification.CatalogueBOddQuadratic in
theorem isQuasisimple_elementaryGroup_of_noOrth_of_three_le_finrank (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    (hW1 : ∀ P P' : HypPair Q, ¬ P.Orth P') : CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) := by
  obtain ⟨τ, hτ, hτ2⟩ := exists_ne_zero_sq_ne_one (K := K) (by omega)
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ hdim
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd Q hQ hdim
  obtain ⟨P₀, -⟩ := exists_hypPair hQ hvQ hv0
  exact isQuasisimple_elementaryGroup_of_noOrth P₀ (two_ne_zero_of_odd_card hodd) hQ hA hτ hτ2 hW1

theorem isQuasisimple_elementaryGroup_small (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    (hne : Module.finrank K V ≠ 4 ∨ ∀ P P' : HypPair Q, ¬ P.Orth P') :
    CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) := by
  by_cases hW : ∃ P P' : HypPair Q, P.Orth P'
  · obtain ⟨P, P', hP⟩ := hW
    have h4 := four_le_finrank_of_orth hP
    have h4' : Module.finrank K V ≠ 4 := by
      rcases hne with h | h
      · exact h
      · exact absurd hP (h P P')
    exact isQuasisimple_elementaryGroup_of_five_le_finrank hodd h5 hQ (by omega)
  · push Not at hW
    exact isQuasisimple_elementaryGroup_of_noOrth_of_three_le_finrank hodd h5 hQ hdim
      fun P P' => hW P P'

end Finite

end CFSG.ClassicalGroups.Orthogonal.Small
