module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeACover
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem isSolvable_specialLinear_two_of_card_le_three {K : Type} [Field K] [Finite K]
    (h : Nat.card K ≤ 3) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard := CFSG.OrderReductions.LinearOrders.card_specialLinear K 2 (by norm_num)
  haveI := Fintype.ofFinite (Matrix.SpecialLinearGroup (Fin 2) K)
  have h23 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
  rcases h23 with h2 | h3
  · refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, hcard, h2]
    decide
  · refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, hcard, h3]
    decide

theorem ker_comp_mulEquiv_le_center {X C G : Type*} [Group X] [Group C] [Group G] (e : X ≃* C)
    (f : C →* G) (h : f.ker ≤ Subgroup.center C) :
    (f.comp e.toMonoidHom).ker ≤ Subgroup.center X := by
  intro x hx
  have hx' : e x ∈ Subgroup.center C := h hx
  rw [Subgroup.mem_center_iff] at hx' ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact hx' (e y)

theorem not_isSolvable_of_isQuasisimple {G : Type*} [Group G] (hQ : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hsol
  obtain ⟨hp, hs⟩ := LieSemisimple.open_isQuasisimple hQ
  haveI := hs.toNontrivial
  haveI : Nontrivial G := (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial
  exact absurd hp (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial G))

section RankOne


theorem exists_pair_of_rank_one {τ : Tag} {L : Type} [Field L]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} (i : KernelComponent χ)
    (hn : (componentRoots χ i).ncard = 2) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ componentRoots χ i = {β, -β} := by
  classical
  obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.1 hn
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hx : x ∈ componentRoots χ i := by rw [hxy']; exact Set.mem_insert _ _
  have hxr : IsRoot τ x := hΨ.isRoot x hx
  have hnx : -x ∈ componentRoots χ i := hΨ.neg_mem x hx
  rw [hxy'] at hnx
  have hne : -x ≠ x := by
    intro h
    have h0 : x = 0 := by
      have h2 : (2 : ℤ) • x = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h]
        exact neg_add_cancel x
      funext j
      have := congrFun h2 j
      simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      simp only [Pi.zero_apply]
      omega
    have := iform_self_pos_of_isRoot hxr
    rw [h0] at this
    simp [iform] at this
  refine ⟨x, hxr, ?_⟩
  rcases hnx with h | h
  · exact absurd h hne
  · rw [hxy', h]

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem rationalLieType_of_rankOne (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2) (hℓ3 : ringChar L ≠ 3)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
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
    have hring : ringChar (fixSubfield σ) = ringChar L := ringChar_subfield' _
    have hres := rationalLieType_of_slCover (K := ↥(fixSubfield σ)) (ν := 2) le_rfl
      (fun _ => by rw [hKcard]; exact hQ4) (by rw [hring]; exact hℓ3)
      (rationalComponent S.ρ S.Γ (rootCharHom ta) i) g hgsurj hgker
    rwa [hring] at hres
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
    exact not_isSolvable_of_isQuasisimple hQS inferInstance

end RankOne

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
