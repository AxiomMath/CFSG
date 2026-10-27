module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResComp
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section InnerTL


theorem excres_hasA2Pair_spec {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hA2 : HasA2Pair τ Ψ) :
    ∃ γ ∈ Ψ, ∃ δ ∈ Ψ, δ ≠ γ ∧ δ ≠ -γ ∧ IsRoot τ (γ + δ) ∧ ¬ IsRoot τ (γ - δ) ∧
      ¬ IsRoot τ ((2 : ℤ) • γ + δ) ∧ ¬ IsRoot τ (γ + (2 : ℤ) • δ) := by
  obtain ⟨γ, hγ, δ, hδ, h1, h2, h3, h4⟩ := hA2
  refine ⟨γ, hγ, δ, hδ, ?_, ?_, h1, h2, h3, h4⟩
  · rintro rfl
    have h2' : IsRoot τ ((2 : ℤ) • δ) := by simpa [two_smul] using h1
    rcases h2'.eq_one_or_neg_one_of_eq_smul (β := δ) (m := 2) rfl with h | h <;> omega
  · rintro rfl
    simp only [add_neg_cancel] at h1
    exact h1.ne_zero rfl

theorem excres_hbig_of_hasA2Pair {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hA2 : HasA2Pair τ Ψ) :
    ∃ α ∈ Ψ, ∃ δ ∈ Ψ, δ ≠ α ∧ δ ≠ -α := by
  obtain ⟨γ, hγ, δ, hδ, hne1, hne2, -⟩ := excres_hasA2Pair_spec hA2
  exact ⟨γ, hγ, δ, hδ, hne1, hne2⟩

theorem excres_f4_A2_sameLength : ∀ γ ∈ rootFinset Tag.F4, ∀ δ ∈ rootFinset Tag.F4,
    γ + δ ∈ rootFinset Tag.F4 → γ - δ ∉ rootFinset Tag.F4 →
    (2 : ℤ) • γ + δ ∉ rootFinset Tag.F4 → γ + (2 : ℤ) • δ ∉ rootFinset Tag.F4 →
    iform γ γ = iform δ δ ∧ iform γ δ ≠ 0 := by
  decide +kernel

theorem excres_perfect_of_card_two {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hA2 : HasA2Pair τ (componentRoots χ i)) :
    Group.IsPerfect (componentRootSpan K χ i) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · obtain ⟨γ, hγ, δ, hδ, hne1, hne2, h1, h2, h3, h4⟩ := excres_hasA2Pair_spec hA2
    obtain ⟨hlen, hnz⟩ := excres_f4_A2_sameLength γ
      (mem_rootFinset.2 (isRoot_of_mem_componentRoots hγ)) δ
      (mem_rootFinset.2 (isRoot_of_mem_componentRoots hδ)) (mem_rootFinset.2 h1)
      (fun h => h2 (mem_rootFinset.1 h)) (fun h => h3 (mem_rootFinset.1 h))
      (fun h => h4 (mem_rootFinset.1 h))
    exact isPerfect_componentRootSpan_F4_two (eq_zero_or_one_of_card_two hK) i
      ⟨γ, hγ, δ, hδ, hne1, hne2, hlen, hnz⟩
  all_goals
    exact isPerfect_componentRootSpan_simplyLaced (by simp) i (excres_hbig_of_hasA2Pair hA2)

theorem excres_inner_not_typeL2 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hTLin : ExcTLInner τ) (hTLin2 : ExcTLInnerTwo τ) {L : Type} [Field L] [IsAlgClosed L]
    (hL3 : (3 : L) ≠ 0) {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner)
    (hA2 : HasA2Pair τ (componentRoots (rootCharHom a) i))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) {q : ℕ}
    (hq10 : 10 ≤ q) : ¬ IsTypeL2 q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  intro hq
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact hL3 (by simpa using CharP.cast_eq_zero L 3)
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq', ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hperfC : Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    by_cases hQ4 : 4 ≤ r ^ (e * s)
    · obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
      exact isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := rootCharHom a) ht i
    · have h2 : r ^ (e * s) = 2 := by
        have h2le : 2 ≤ r ^ (e * s) := hr.two_le.trans (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
        have h3ne : r ^ (e * s) ≠ 3 := fun h3 => hr3 (by
          have := (Nat.prime_three.eq_one_or_self_of_dvd r (by
            rw [← h3]; exact dvd_pow_self r (Nat.mul_pos he hs0).ne')).resolve_left hr.one_lt.ne'
          exact this)
        omega
      exact excres_perfect_of_card_two hτ (K := fixSubfield σ) (by rw [hKcard, h2]) _ i hA2
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
  have hqC : IsTypeL2 q ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    have hqR : IsTypeL2 q ↥f.range := p6_isTypeL2_of_equiv (MulEquiv.subgroupCongr hRf.symm) hq
    exact (excres_isTypeL2_of_central_surjection hperfC f.rangeRestrict
      f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)).1 hqR
  by_cases hQ4 : 4 ≤ r ^ (e * s)
  · exact hTLin (fixSubfield σ) (by rw [hKcard]; exact hQ4) Lˣ (rootCharHom a) i hA2 hperfC q
      hq10 hqC
  · have h2 : r ^ (e * s) = 2 := by
      have h2le : 2 ≤ r ^ (e * s) := hr.two_le.trans (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
      have h3ne : r ^ (e * s) ≠ 3 := fun h3 => hr3 (by
        have := (Nat.prime_three.eq_one_or_self_of_dvd r (by
          rw [← h3]; exact dvd_pow_self r (Nat.mul_pos he hs0).ne')).resolve_left hr.one_lt.ne'
        exact this)
      omega
    exact hTLin2 (fixSubfield σ) (by rw [hKcard, h2]) Lˣ (rootCharHom a) i hA2 hperfC q hq10 hqC

end InnerTL

end CFSG.HardMathSupport.Dickson.Sec6.I1431
