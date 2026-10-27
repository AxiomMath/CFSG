module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeA
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem RationalLieType.lieCompData {ℓ : ℕ} {G : Type} [Group G] {R : Subgroup G}
    (h : RationalLieType ℓ R) : LieCompData ℓ ↥R :=
  ⟨h.1, fun ⟨e⟩ => (h.2.false e).elim⟩

theorem lieCompData_of_slCover {K : Type} [Field K] [Finite K] {ν : ℕ} (hν : 2 ≤ ν)
    (h4 : ν = 2 → 4 ≤ Nat.card K) {G : Type} [Group G] (R : Subgroup G)
    (g : Matrix.SpecialLinearGroup (Fin ν) K →* ↥R) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin ν) K)) :
    LieCompData (ringChar K) ↥R := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hFD := slFactorFacts_holds K ν hν (fun h => by
    rw [← Nat.card_eq_fintype_card]
    exact h4 h)
  exact hFD.lieCompData g hg hgk

theorem ringChar_ne_of_pow_eq_one {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1) :
    ringChar L ≠ p := by
  intro hc
  haveI : CharP L p := ringChar.of_eq hc
  haveI : Fact p.Prime := ⟨hp⟩
  apply h1
  have ha : a = 1 := by
    funext j
    have h : ((a j : L) - 1) ^ p = 0 := by
      rw [sub_pow_char, one_pow, sub_eq_zero]
      simpa using congrArg (fun u : Lˣ => (u : L)) (hap j)
    have h' : (a j : L) - 1 = 0 := pow_eq_zero_iff hp.ne_zero |>.1 h
    exact Units.ext (sub_eq_zero.1 h')
  rw [ha]
  exact rootDiagUnit_one

theorem natCast_ne_zero_of_ringChar_ne {p : ℕ} (hp : p.Prime) {L : Type} [Field L]
    (h : ringChar L ≠ p) : ((p : ℕ) : L) ≠ 0 := by
  intro h'
  have hd : ringChar L ∣ p := (ringChar.spec L p).1 (by exact_mod_cast h')
  rcases (Nat.dvd_prime hp).1 hd with h'' | h''
  · exact CharP.ringChar_ne_one h''
  · exact h h''

section TypeA


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {ta : Fin τ.rank → Lˣ}

theorem lieCompData_of_rankOne (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i)) :
    LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
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
    have hres := lieCompData_of_slCover (K := ↥(fixSubfield σ)) (ν := 2) le_rfl
      (fun _ => by rw [hKcard]; exact hQ4)
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


theorem lieCompData_of_split_frame (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b))
    :
    LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := split_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfinK, -⟩ := finite_card_fixSubfield (L := L) (r := r)
    (n := e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
    (Nat.mul_pos he hs0) σQ hσc
  have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hperf) hf1
  let g : SL(ν, ↥(fixSubfield σQ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  have hring : ringChar (fixSubfield σQ) = ringChar L := ringChar_subfield' _
  have hres := lieCompData_of_slCover (K := ↥(fixSubfield σQ)) (ν := ν) (by omega)
    (fun h => by omega)
    (rationalComponent S.ρ S.Γ (rootCharHom ta) i) g hgsurj hgker
  rwa [hring] at hres


variable {a : Fin τ.rank → Lˣ}

theorem lieCompData_of_typeA {p : ℕ} (hp : p.Prime) (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · exact lieCompData_of_rankOne S hT i hr1 (by rw [hA.2, hr1]) hQS
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
      rw [hs, hΨ] at h2
      exact h2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact lieCompData_of_split_frame S hT i hν hψ hΨ π hπ
    · exact (rationalLieType_of_unitary_frame S hT i hν hψ hΨ π hπ hQS).lieCompData

end TypeA

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
