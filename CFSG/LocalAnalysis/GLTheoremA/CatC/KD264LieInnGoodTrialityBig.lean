module

import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTrialityAlg
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
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


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem rootChar_rho_iterate {b : Fin τ.rank → Lˣ} (hTb : rootDiagUnit τ b ∈ S.D.torus) (n : ℕ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootChar b ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ) = rootChar b γ ^ (S.D.q ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', S.frob.rootChar_eq b hTb _ (S.iterate_isRoot n hγ), ih,
      ← pow_mul, pow_succ]

theorem rootChar_neg_eq_inv {b : Fin τ.rank → Lˣ} (x : Fin τ.rank → ℤ) :
    rootChar b (-x) = (rootChar b x)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

section RankOne


theorem rankOne_perfect_dvd_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ta tb : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (hTb : rootDiagUnit τ tb ∈ S.D.torus) (hbp : ∀ i, tb i ^ p = 1)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom ta) i) (hχ : rootChar tb γ ≠ 1) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom ta) i, rationalComponent S.ρ S.Γ (rootCharHom ta) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
    p ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
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
  haveI : Fact p.Prime := ⟨hp⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hγroot : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
  set ζ : Lˣ := rootChar tb γ with hζ
  have hζp : ζ ^ p = 1 := CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one hbp γ
  have hζord : orderOf ζ = p := orderOf_eq_prime hζp hχ
  have hργ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ = γ ∨
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ = -γ := by
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ ∈ componentRoots (rootCharHom ta) i := by
      rw [← hs]
      exact ⟨γ, hγ, rfl⟩
    rw [hΨ] at hγ h2
    rcases hγ with rfl | rfl <;> rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr h2
    · exact Or.inr (by rw [h2, neg_neg])
    · exact Or.inl h2
  have hQpos : 1 ≤ S.D.q ^ s := Nat.one_le_pow _ _ (by rw [hq]; exact pow_pos hr.pos e)
  have hkey : rootChar tb ((S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ) = ζ ^ (S.D.q ^ s) :=
    rootChar_rho_iterate S hTb s hγroot
  have hdvd : p ∣ S.D.q ^ s - 1 ∨ p ∣ S.D.q ^ s + 1 := by
    rcases hργ with h | h
    · left
      rw [h] at hkey
      have h2 : ζ ^ (S.D.q ^ s - 1) = 1 := by
        have : ζ ^ (S.D.q ^ s) = ζ ^ (S.D.q ^ s - 1) * ζ := by
          rw [← pow_succ, Nat.sub_add_cancel hQpos]
        rw [this] at hkey
        exact mul_eq_right.1 hkey.symm
      rw [← hζord]
      exact orderOf_dvd_of_pow_eq_one h2
    · right
      rw [h, rootChar_neg_eq_inv] at hkey
      have h2 : ζ ^ (S.D.q ^ s + 1) = 1 := by
        rw [pow_succ, ← hkey]
        exact inv_mul_cancel ζ
      rw [← hζord]
      exact orderOf_dvd_of_pow_eq_one h2
  have hQe : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  have hQ4 : 4 ≤ r ^ (e * s) := by
    have h2 : 2 ≤ r ^ (e * s) :=
      le_trans hr.two_le (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
    rw [← hQe] at h2 ⊢
    rcases hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
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
  haveI : Finite ↥(fixSubfield σ) := hfinK
  haveI : Finite ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
    Finite.of_equiv _ eSL.toEquiv
  have hcardC : p ∣ Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) := by
    rw [← Nat.card_congr eSL.toEquiv,
      CFSG.OrderReductions.LinearOrders.card_specialLinear (fixSubfield σ) 2 (by norm_num)]
    have hFQ : Nat.card ↥(fixSubfield σ) = S.D.q ^ s := by rw [hKcard, hQe]
    rw [hFQ]
    simp only [Nat.reduceMul, Nat.reduceDiv, Finset.Icc_self, Finset.prod_singleton, pow_one]
    refine Dvd.dvd.mul_left ?_ _
    have hsq : (S.D.q ^ s) ^ 2 - 1 = (S.D.q ^ s + 1) * (S.D.q ^ s - 1) := by
      simpa using Nat.sq_sub_sq (S.D.q ^ s) 1
    rw [hsq]
    rcases hdvd with h | h
    · exact Dvd.dvd.mul_left h _
    · exact Dvd.dvd.mul_right h _
  obtain ⟨hcomm, hdvd'⟩ := perfect_range_dvd_of_central f hperfC hker hp hcardC
  rw [hRf] at hcomm hdvd'
  exact ⟨hcomm, hdvd'⟩

end RankOne

section Frames

theorem splitFrame_perfect_dvd_p {p : ℕ} (hp : p.Prime) {ta tb : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (hTb : rootDiagUnit τ tb ∈ S.D.torus)
    (hbp : ∀ i, tb i ^ p = 1) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b))
    {x₀ y₀ : Fin ν} (hxy : x₀ ≠ y₀) (hχ : rootChar tb (σ x₀ y₀) ≠ 1) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom ta) i, rationalComponent S.ρ S.Γ (rootCharHom ta) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
    p ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := split_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hperf) hf1
  set ω : Fin ν → Fin ν → Lˣ := fun x y => rootChar tb (σ x y) with hω
  have hcoc : ∀ x y z, ω x y * ω y z = ω x z := fun x y z => by
    simp only [hω]
    rw [← rootChar_add, hψ.add]
  have hωp : ∀ x y, ω x y ^ p = 1 := fun x y =>
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one hbp _
  have hωπ : ∀ x y, x ≠ y → ω (π x) (π y) = ω x y ^ ((S.D.q ^ s : ℕ) : ℤ) := by
    intro x y hxy
    simp only [hω]
    rw [← hπ x y hxy, rootChar_rho_iterate S hTb s (hψ.isRoot x y hxy), zpow_natCast]
  obtain ⟨m, hm2, hmν, hdvd⟩ :=
    exists_cycle_dvd hp π ((S.D.q ^ s : ℕ) : ℤ) ω hωp hcoc hωπ (x₀ := x₀) (y₀ := y₀) hχ
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σQ hσc
  haveI : Finite ↥(fixSubfield σQ) := hfinK
  have hQe : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  rw [hQe] at hdvd
  have hr1 : 1 ≤ r ^ (e * s) := Nat.one_le_pow _ _ hr.pos
  have hcardX : p ∣ Nat.card SL(ν, ↥(fixSubfield σQ)) := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear (fixSubfield σQ) ν (by omega),
      hKcard]
    refine Dvd.dvd.mul_left ?_ _
    exact dvd_trans (nat_dvd_pow_sub_one_of_int hr1 hdvd)
      (Finset.dvd_prod_of_mem (fun k => (r ^ (e * s)) ^ k - 1) (Finset.mem_Icc.2 ⟨hm2, hmν⟩))
  obtain ⟨hcomm, hdvd'⟩ := perfect_range_dvd_of_central f hperf hfker hp hcardX
  rw [hRf] at hcomm hdvd'
  exact ⟨hcomm, hdvd'⟩

theorem unitaryFrame_perfect_dvd_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ta tb : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (hTb : rootDiagUnit τ tb ∈ S.D.torus)
    (hbp : ∀ i, tb i ^ p = 1) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {x₀ y₀ : Fin ν} (hxy : x₀ ≠ y₀) (hχ : rootChar tb (σ x₀ y₀) ≠ 1) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom ta) i, rationalComponent S.ρ S.Γ (rootCharHom ta) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
    p ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfin, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  obtain ⟨F, hFcard, ⟨eU⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
  set ω : Fin ν → Fin ν → Lˣ := fun x y => rootChar tb (σ x y) with hω
  have hcoc : ∀ x y z, ω x y * ω y z = ω x z := fun x y z => by
    simp only [hω]
    rw [← rootChar_add, hψ.add]
  have hωp : ∀ x y, ω x y ^ p = 1 := fun x y =>
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one hbp _
  have hωπ : ∀ x y, x ≠ y → ω (π x) (π y) = ω x y ^ (-((S.D.q ^ s : ℕ) : ℤ)) := by
    intro x y hxy
    have h1 : ω (π y) (π x) = ω x y ^ (S.D.q ^ s) := by
      simp only [hω]
      rw [← hπ x y hxy, rootChar_rho_iterate S hTb s (hψ.isRoot x y hxy)]
    have h2 : ω (π x) (π y) = (ω (π y) (π x))⁻¹ := by
      simp only [hω]
      rw [hψ.neg (π y) (π x), rootChar_neg_eq_inv]
    rw [h2, h1, zpow_neg, zpow_natCast]
  obtain ⟨m, hm2, hmν, hdvd⟩ :=
    exists_cycle_dvd hp π (-((S.D.q ^ s : ℕ) : ℤ)) ω hωp hcoc hωπ (x₀ := x₀) (y₀ := y₀) hχ
  have hQe : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  rw [hQe] at hdvd
  have hdvd' : (p : ℤ) ∣ ((r ^ (e * s) : ℕ) : ℤ) ^ m - (-1) ^ m := by
    have e1 : ((-1 : ℤ)) ^ m * (-((r ^ (e * s) : ℕ) : ℤ)) ^ m = ((r ^ (e * s) : ℕ) : ℤ) ^ m := by
      rw [← mul_pow]
      congr 1
      ring
    have e2 : ((r ^ (e * s) : ℕ) : ℤ) ^ m - (-1) ^ m =
        (-1) ^ m * ((-((r ^ (e * s) : ℕ) : ℤ)) ^ m - 1) := by
      rw [mul_sub, e1, mul_one]
    rw [e2]
    exact Dvd.dvd.mul_left hdvd _
  have h32 : (ν, r ^ (e * s)) ≠ (3, 2) := by
    intro h
    have hν3 : ν = 3 := congrArg Prod.fst h
    have hQ2 : r ^ (e * s) = 2 := congrArg Prod.snd h
    rw [hQ2] at hdvd'
    subst hν3
    have h9 : p ∣ 9 := by
      interval_cases m
      · have h3 : (p : ℤ) ∣ 3 := by simpa using hdvd'
        exact (Int.natCast_dvd_natCast.1 (by exact_mod_cast h3 : (p : ℤ) ∣ ((3 : ℕ) : ℤ))).trans
          (by norm_num)
      · have h9' : (p : ℤ) ∣ 9 := by simpa using hdvd'
        exact Int.natCast_dvd_natCast.1 (by exact_mod_cast h9' : (p : ℤ) ∣ ((9 : ℕ) : ℤ))
    have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (n := 2) (by norm_num; exact h9)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hCperf : Group.IsPerfect
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC h32).1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  have hU : UnitaryFieldData r (e * s) F := ⟨hr, hes, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hcardInt := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := ν) (by omega)
  have hcardX : p ∣ Nat.card
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
    rw [← Nat.card_congr eU.toEquiv]
    refine Int.natCast_dvd_natCast.1 ?_
    rw [hcardInt]
    refine Dvd.dvd.mul_left ?_ _
    exact dvd_trans hdvd'
      (Finset.dvd_prod_of_mem (fun k => ((r ^ (e * s) : ℕ) : ℤ) ^ k - (-1) ^ k)
        (Finset.mem_Icc.2 ⟨hm2, hmν⟩))
  haveI := hfin
  obtain ⟨hcomm, hdvd''⟩ := perfect_range_dvd_of_central f hCperf hfker hp hcardX
  rw [hRf] at hcomm hdvd''
  exact ⟨hcomm, hdvd''⟩

end Frames

section Dispatch

theorem typeA_perfect_dvd_p
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpL : ((p : ℕ) : L) ≠ 0) {a b : Fin τ.rank → Lˣ}
    (hTa : rootDiagUnit τ a ∈ S.D.torus) (hTb : rootDiagUnit τ b ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (hbp : ∀ i, b i ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (hχ : rootChar b γ ≠ 1) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom a) i, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ =
      rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    p ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · exact rankOne_perfect_dvd_p S hp hp5 hTa hTb hbp i hr1 (by rw [hA.2, hr1]) hγ hχ
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hTa i
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
    have hγF := hγ
    rw [hΨ] at hγF
    obtain ⟨x₀, y₀, hxy, rfl⟩ := hγF
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact splitFrame_perfect_dvd_p S hp hTa hTb hbp i hν hψ hΨ π hπ hxy hχ
    · exact unitaryFrame_perfect_dvd_p S hp hp5 hTa hTb hbp i hν hψ hΨ π hπ hxy hχ

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

end
