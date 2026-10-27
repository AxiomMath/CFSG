module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped MatrixGroups

namespace TwE6UniqAbs

set_option linter.unusedSectionVars false


theorem orbit_ne_of_rank_one_quasisimple {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {ta : Fin τ.rank → Lˣ} (hq2 : S.D.q = 2)
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i)) :
    (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom ta) i ≠
      componentRoots (rootCharHom ta) i := by
  classical
  intro hfix
  obtain ⟨β, hβ, hΨ⟩ := exists_pair_of_rank_one i hn
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hs1 : s = 1 :=
    le_antisymm (Nat.sInf_le ⟨Nat.one_pos, by simpa using hfix⟩) hs0
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    have hkind : twistKind S.ρ (rootCharHom ta) i = .inner := by
      by_cases hin : twistInner (componentRoots (rootCharHom ta) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom ta) i)])
      · unfold twistKind
        rw [if_pos hin]
      · unfold twistKind
        rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
          if_neg (fun h => by omega), if_neg (fun h => by omega)]
    exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
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
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom ta) i =
      (CFSG.LieType.Chevalley.rootSL2 τ (fixSubfield σ) β).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom ta) i) = _
    rw [hΨ]
    simp only [rootSpan, iSup_insert, iSup_singleton]
  let eSL : SL(2, ↥(fixSubfield σ)) ≃*
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
    (MonoidHom.ofInjective (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (K := ↥(fixSubfield σ)) β)).trans (MulEquiv.subgroupCongr hC.symm)
  have hQ : r ^ (e * s) = 2 := by
    rw [hs1, mul_one, ← hq, hq2]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard, hQ]; omega
  haveI : Group.IsSolvable SL(2, ↥(fixSubfield σ)) :=
    isSolvable_specialLinear_two_of_card_le_three hKle
  haveI : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
    Group.isSolvable_of_isSolvable_injective (f := eSL.symm.toMonoidHom) eSL.symm.injective
  haveI : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  haveI : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
  exact LieComp.not_isSolvable_of_isQuasisimple hQS inferInstance

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
