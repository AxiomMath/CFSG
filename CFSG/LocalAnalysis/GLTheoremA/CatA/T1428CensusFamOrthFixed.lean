module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

private theorem orthDerived_quasisimple_or_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (polarBilin R).Nondegenerate) (h3 : 3 ≤ finrank K W) :
    CFSG.IsQuasisimple ↥(orthDerived R) ∨
      (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ w ∈ S, R w = 0) := by
  classical
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0
  · exact Or.inl (isQuasisimple_orthDerived hR hT)
  · obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        R hR
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, R u = 0
    · obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne
        exact hT (exists_threeSingular_of_le R hUQ (by omega))
      subst hn2
      exact Or.inr ⟨by omega, U, hUn, hUQ⟩
    · left
      have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hS ⟨U, hU, hcon⟩
      rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
      · exfalso
        refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
        · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
            (by simp)
        · intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0
      · have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
            R u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
            b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le R hU (by omega))
        rcases hn23 with rfl | rfl
        · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
            hidx, hnorm, hodd⟩ :=
            CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction R hR (by omega) hts
          haveI := hsimple
          have hq : CFSG.IsQuasisimple ↥ρ.range := isQuasisimple_of_simple_nonabelian hnonab
          rw [show orthDerived R = ρ.range from hcomm]
          exact hq
        · obtain ⟨E, _, _, D, ψ, ρ, hψ, hρψ, hinj, hmem, hcomm, hsimple, hperf, hnonab, hcard,
            hidx, hnorm, hodd⟩ :=
            CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction R hR (by omega) hts
          haveI := hsimple
          have hq : CFSG.IsQuasisimple ↥ρ.range := isQuasisimple_of_simple_nonabelian hnonab
          rw [show orthDerived R = ρ.range from hcomm]
          exact hq

section Layer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem fixedComponentImage_quasisimple_or_split (hx : OddOrderIsometry Q p x)
    (h3 : 3 ≤ finrank K (fixedSpace x)) :
    CFSG.IsQuasisimple ↥(fixedComponentImage Q x) ∨
      (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
        ∀ w ∈ S, (Q.comp (fixedSpace x).subtype) w = 0) := by
  rcases orthDerived_quasisimple_or_split (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate h3 with hq | hs
  · left
    unfold fixedComponentImage
    exact isQuasisimple_map_projective hx.supportedFixedDerived_le_orthDerived
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm hq)
  · exact Or.inr hs

theorem split_of_two_components_in_fixedLayer (hx : OddOrderIsometry Q p x)
    (h3 : 3 ≤ finrank K (fixedSpace x)) {J₁ J₂ : Subgroup (ProjOrthDerived Q)}
    (h1 : CFSG.Open.IsComponentOf J₁ (centralizerImage Q x))
    (h2 : CFSG.Open.IsComponentOf J₂ (centralizerImage Q x))
    (hle1 : J₁ ≤ fixedComponentImage Q x) (hle2 : J₂ ≤ fixedComponentImage Q x) (hne : J₁ ≠ J₂) :
    finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ w ∈ S, (Q.comp (fixedSpace x).subtype) w = 0 := by
  rcases fixedComponentImage_quasisimple_or_split hx h3 with hY | hs
  · exfalso
    have hYc : CFSG.Open.IsComponentOf (fixedComponentImage Q x) (centralizerImage Q x) :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_of_normal_normal le_rfl
        fixedComponentImage_le_centralizerImage (by rw [Subgroup.subgroupOf_self]; infer_instance)
        hx.normal_fixedComponentImage hY
    haveI : Finite V := Module.finite_of_finite K
    haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    haveI : Finite (ProjOrthDerived Q) := inferInstance
    obtain ⟨j₁, hj₁⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
      (fun _ : Unit => fixedComponentImage Q x) (fun _ => hYc) h1
      (by simpa using hle1)
    obtain ⟨j₂, hj₂⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
      (fun _ : Unit => fixedComponentImage Q x) (fun _ => hYc) h2
      (by simpa using hle2)
    exact hne (hj₁.symm.trans hj₂)
  · exact hs

end Layer

end CFSG.LocalAnalysis.GLTheoremA.T1428
