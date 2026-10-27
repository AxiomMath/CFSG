module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section RankOne


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem exists_slCover_of_rankOne (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (g : SL(2, K) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i)),
      Function.Surjective g ∧ g.ker ≤ Subgroup.center SL(2, K) ∧
        Nat.card K = r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) ∧
        4 ≤ Nat.card K ∧ ringChar K = r := by
  classical
  obtain ⟨β, hβ, hΨ⟩ := exists_pair_of_rank_one i hn
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
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
  have hker' := ker_comp_mulEquiv_le_center eSL f hker
  by_cases hQ4 : 4 ≤ r ^ (e * s)
  ·
    obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
    have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
      (χ := rootCharHom ta) ht i
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
      le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
    let g : SL(2, ↥(fixSubfield σ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
      (f.comp eSL.toMonoidHom).codRestrict _ (fun c => by
        rw [← hRf]
        exact ⟨eSL c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      obtain ⟨c', rfl⟩ := eSL.surjective c
      exact ⟨c', Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center SL(2, ↥(fixSubfield σ)) := by
      intro c hc
      apply hker'
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    have hring : ringChar (fixSubfield σ) = r := (ringChar_subfield' _).trans (ringChar.eq L r)
    exact ⟨↥(fixSubfield σ), inferInstance, hfinK, g, hgsurj, hgker, hKcard,
      by rw [hKcard]; exact hQ4, hring⟩
  ·
    exfalso
    have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
    haveI : Group.IsSolvable SL(2, ↥(fixSubfield σ)) :=
      isSolvable_specialLinear_two_of_card_le_three hKle
    haveI : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
      Group.isSolvable_of_isSolvable_injective (f := eSL.symm.toMonoidHom) eSL.symm.injective
    haveI : Group.IsSolvable ↥f.range :=
      Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    haveI : Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hf1)
    exact LieComp.not_isSolvable_of_isQuasisimple hQS inferInstance


theorem not_three_dvd_center_of_rankOne (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    [Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i)] :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i)) := by
  classical
  obtain ⟨K, _, hKf, g, hg, hgk, -, hK4, -⟩ :=
    exists_slCover_of_rankOne S hT i h1 hn hQS hr hchar he hq
  haveI : Fintype K := Fintype.ofFinite K
  have hFD := slFactorFacts_holds K 2 le_rfl (fun _ => by rwa [← Nat.card_eq_fintype_card])
  have hmap := map_center_of_surjective hFD.perfect g hg hgk
  refine not_three_dvd_card_center_of_pow (n := 2) (by norm_num) fun z hz => ?_
  rw [← hmap] at hz
  obtain ⟨A, hA, rfl⟩ := hz
  rw [← map_pow, pow_card_eq_one_of_mem_center hA, map_one]

end RankOne

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
