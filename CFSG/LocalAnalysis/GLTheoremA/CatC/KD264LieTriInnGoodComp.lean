module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieTriInnGoodAlg
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne

public section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

section RankOne


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem rankOne_perfect_dvd_three {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2) (hQ : 4 ≤ S.D.q) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom ta) i, rationalComponent S.ρ S.Γ (rootCharHom ta) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
    3 ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
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
  have hQ4 : 4 ≤ r ^ (e * s) := by
    rw [pow_mul]
    exact hq ▸ hQ.trans (Nat.le_self_pow hs0.ne' _)
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom ta) ht i
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
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
  obtain ⟨y, z', hy3, hyz⟩ := exists_pair_SL2 (K := ↥(fixSubfield σ))
  have key := perfect_dvd_three_of_central_hom f hperfC hker
    (y := eSL y) (z := eSL z') (by rw [← map_pow, hy3, map_one])
    (fun h => hyz (eSL.injective (by rw [map_mul, map_mul]; exact h)))
  rw [hRf] at key
  exact key

end RankOne

section Frames


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem splitFrame_perfect_dvd_three {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b)) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom ta) i, rationalComponent S.ρ S.Γ (rootCharHom ta) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
    3 ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := split_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hperf) hf1
  obtain ⟨y, z, hy3, hyz, -⟩ := exists_pair_SL (L := ↥(fixSubfield σQ)) hν
  have key := perfect_dvd_three_of_central_hom f hperf hfker hy3 hyz
  rw [hRf] at key
  exact key

theorem unitaryFrame_perfect_dvd_three {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a)) (hQ : 4 ≤ S.D.q) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom ta) i, rationalComponent S.ρ S.Γ (rootCharHom ta) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
    3 ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfin, hqsC, hc216⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have hQ4 : 4 ≤ r ^ (e * s) := by
    rw [pow_mul]
    exact hq ▸ hQ.trans (Nat.le_self_pow hs0.ne' _)
  have h32 : (ν, r ^ (e * s)) ≠ (3, 2) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hCperf : Group.IsPerfect
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC h32).1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  obtain ⟨y, z, hy3, hyz, hfx⟩ := exists_pair_SL (L := L) hν
  have key := perfect_dvd_three_of_central_hom f hCperf hfker
    (y := ⟨y, (hfx σQ).1⟩) (z := ⟨z, (hfx σQ).2⟩)
    (Subtype.ext (by simpa using hy3)) (fun h => hyz (congrArg Subtype.val h))
  rw [hRf] at key
  exact key

end Frames

section Dispatch


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem typeA_perfect_dvd_three
    {p : ℕ} (hp : p.Prime) (hpL : ((p : ℕ) : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQ : 4 ≤ S.D.q) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom a) i, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    3 ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · exact rankOne_perfect_dvd_three S hT i hr1 (by rw [hA.2, hr1]) hQ
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
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
    · exact splitFrame_perfect_dvd_three S hT i hν hψ hΨ π hπ
    · exact unitaryFrame_perfect_dvd_three S hT i hν hψ hΨ π hπ hQ

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

end
