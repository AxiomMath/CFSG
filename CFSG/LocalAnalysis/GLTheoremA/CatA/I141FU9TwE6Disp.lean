module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6Rat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.LocalAnalysis.GLTheoremA.HStdExcl

section Main


theorem e6TwoRatU38Centre_holds : E6TwoRatU38Centre := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hqs hcard
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have hringChar : ringChar L = 2 := ringChar.eq L 2
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_E6 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
    ·
      exfalso
      obtain ⟨f, hf1, -, hmodel⟩ :=
        rationalComponent_rankOne_model S hT i hr1 (by rw [hA.2, hr1]) hqs
      rw [hringChar] at hmodel
      have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num : 0 < 2) hmodel
      exact twE6_psl_card_ne_u38 (le_refl 2) hf1 (hc.symm.trans hcard)
    · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by
        have := hA.1
        omega
      obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
        g2LongA2Frame_proved S Nat.prime_three h3L hTp i h2 hA.2
      have hcardF : (frameRoots σ).ncard = ν * (ν - 1) := by
        have hinj : Set.InjOn (fun q : Fin ν × Fin ν => σ q.1 q.2) {q | q.1 ≠ q.2} := by
          rintro ⟨x, y⟩ hxy ⟨u, v⟩ huv h
          simp only [Set.mem_setOf_eq] at hxy huv
          obtain ⟨rfl, rfl⟩ := hψ.eq_of_eq hκ hnorm hxy huv h
          rfl
        have himg : frameRoots σ =
            (fun q : Fin ν × Fin ν => σ q.1 q.2) '' {q | q.1 ≠ q.2} := by
          ext r
          constructor
          · rintro ⟨x, y, hxy, rfl⟩
            exact ⟨(x, y), hxy, rfl⟩
          · rintro ⟨⟨x, y⟩, hxy, rfl⟩
            exact ⟨x, y, hxy, rfl⟩
        rw [himg, hinj.ncard_image]
        have hoff : ({q : Fin ν × Fin ν | q.1 ≠ q.2} : Set (Fin ν × Fin ν)) =
            ↑(Finset.univ.offDiag : Finset (Fin ν × Fin ν)) := by
          ext q
          simp [Finset.mem_offDiag]
        rw [hoff, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
          Nat.mul_sub_left_distrib, mul_one]
      have hνr : ν = compRank (componentRoots (rootCharHom a) i) + 1 := by
        have h : ν * (ν - 1) = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
          rw [← hcardF, ← hΨ]
          exact hA.2
        generalize compRank (componentRoots (rootCharHom a) i) = r at h h2 ⊢
        obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
        rw [Nat.add_sub_cancel] at h
        have hm : m = r := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
        omega
      obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
      set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
      have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈
          frameRoots σ := by
        intro x y hxy
        have hm1 : σ x y ∈ componentRoots (rootCharHom a) i := by
          rw [hΨ]
          exact ⟨x, y, hxy, rfl⟩
        have hm2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈
            (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
          ⟨_, hm1, rfl⟩
        rw [hs, hΨ] at hm2
        exact hm2
      have hneg : ∀ (n : ℕ) (γ : Fin Tag.E6.rank → ℤ),
          (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] (-γ) =
            -(S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] γ := by
        intro n
        induction n with
        | zero => exact fun γ => rfl
        | succ n ih =>
          intro γ
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
      rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s]) hmaps (hneg s)
          (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
      ·
        exfalso
        obtain ⟨f, hf1, -, hmodel⟩ := rationalComponent_splitFrame_model S hT i hν hψ hΨ π hπ
        rw [hringChar] at hmodel
        have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by omega) hmodel
        exact twE6_psl_card_ne_u38 (by omega) hf1 (hc.symm.trans hcard)
      ·
        obtain ⟨f, hf1, hfeq, hmodel⟩ := rationalComponent_unitaryFrame_model S hT i hν hψ hΨ π hπ hqs
        rw [hringChar] at hmodel hfeq
        have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu (by omega) hmodel
        obtain ⟨hν3, hf3⟩ := twE6_psu_card_eq_u38 hν hf1 (hc.symm.trans hcard)
        have hs3 : s = 3 := by
          rw [hq2, hf3] at hfeq
          exact (Nat.pow_right_injective (le_refl 2) hfeq).symm
        subst hν3
        have hr2 : compRank (componentRoots (rootCharHom a) i) = 2 := by omega
        have hi6 : (componentRoots (rootCharHom a) i).ncard = 6 := by
          rw [hA.2, hr2]
        exact center_rationalComponent_eq_bot_of_orbit_three S hT hap i hi6 hψ hΨ π hπ
          Nat.prime_two inferInstance (by norm_num : 0 < 1) (by rw [hq2]; norm_num) hs3
          (by rw [hq2])
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S
        Nat.prime_three h3L hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · exfalso
      by_cases hr4 : compRank (componentRoots (rootCharHom a) i) = 4
      · exact twE6_d4_ne_u38 S hq2 hT hap h1 i hr4 (by rw [hD.2, hr4]) hcard
      · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
          have := hD.1
          omega
        have h40 : 40 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · have hdvd := twE6_two_pow_dvd_of_inner hT hinner (by omega)
          have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
          have hfin : (componentRoots (rootCharHom a) i).Finite :=
            (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hΨ.isRoot γ hγ
          have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
          exact twE6_ne_u38_of_two_pow_dvd (k := (posRoots (componentRoots (rootCharHom a) i)).ncard)
            (by omega) hdvd hcard
        · obtain ⟨m, e, -, hlie⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_twoD_highG
              Nat.prime_three S hT hap h1 i hr5 hD.2 hinner
              (fun _ _ => True)
              (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega))
              trivial
          rw [hringChar] at hlie
          exact twE6_ne_u38_of_lieModel_pOmegaMinus hlie hcard
    · exact (false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim

end Main

end CFSG.LocalAnalysis.GLTheoremA.I141F
