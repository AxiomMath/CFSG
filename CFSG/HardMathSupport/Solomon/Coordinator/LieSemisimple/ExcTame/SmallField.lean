module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false

section RankOne

theorem card_sl2_dvd_216 {K : Type} [Field K] [Finite K] (hK : Nat.card K ≤ 3) :
    Nat.card (SL2 K) ∣ 216 := by
  classical
  have := Fintype.ofFinite K
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : Nat.card (SL2 K) =
      ((Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K)) /
        (Fintype.card K - 1) := by
    have := Matrix.card_SL_field (𝔽 := K) 2
    simpa [Fin.prod_univ_two] using this
  rw [Nat.card_eq_fintype_card] at hK h2
  rw [hcard]
  interval_cases h : Fintype.card K <;> norm_num

theorem isSolvable_componentRootSpan_of_rank_one {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K ≤ 3) {M : Type} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) :
    Group.IsSolvable (componentRootSpan K χ i) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hα : a.1 ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hle := componentRootSpan_le_range_of_rank_one (K := K) i hα (hrank a.1 hα)
  have : Group.IsSolvable (SL2 K) := isSolvable_of_card_dvd_216 (card_sl2_dvd_216 hK)
  have : Group.IsSolvable (rootSL2 τ K a.1).range :=
    Group.isSolvable_of_surjective (rootSL2 τ K a.1).rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem ncard_componentRoots_eq_two_of_rank_one {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) :
    (componentRoots χ i).ncard = 2 := by
  classical
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hα : a.1 ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hnegα : -a.1 ∈ componentRoots χ i :=
    (isRootComponent_componentRoots (χ := χ) i).neg_mem a.1 hα
  have hset : componentRoots χ i = ({a.1, -a.1} : Set (Fin τ.rank → ℤ)) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro δ hδ
      rcases hrank a.1 hα δ hδ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro δ hδ
      rcases hδ with rfl | rfl
      · exact hα
      · exact hnegα
  have hne : a.1 ≠ -a.1 := by
    intro h
    have h0 : a.1 = 0 := by
      funext k
      have hk : a.1 k = -a.1 k := by simpa using congrFun h k
      have h2 : a.1 k + a.1 k = 0 := by
        nth_rewrite 2 [hk]
        exact add_neg_cancel (a.1 k)
      have h3 : (2 : ℤ) * a.1 k = 0 := by rw [two_mul]; exact h2
      rcases Int.mul_eq_zero.1 h3 with h4 | h4
      · norm_num at h4
      · exact h4
    exact a.2.1.ne_zero h0
  rw [hset, Set.ncard_pair hne]

end RankOne

section Residual

theorem smallFieldInner_quasisimple_of_not_rankOne {τ : Tag} {K : Type} [Field K] [Finite K]
    {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) {p : ℕ} (hp : p.Prime) (hp5 : τ = .G2 → 5 ≤ p)
    (hχp : ∀ γ, IsRoot τ γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    (hχ1 : ∃ γ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1) (hK : Nat.card K ≤ 3)
    (hnrank : ¬ ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) :
    CFSG.IsQuasisimple ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :
      Subgroup (ModGL τ K)) ∧
      (Nat.card K = 2 ∨
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i) := by
  classical
  have hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α := by
    push Not at hnrank
    exact hnrank
  have hcard2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hτ : ∀ τ : Tag, τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    intro τ; cases τ <;> simp
  rcases hτ τ with rfl | rfl | h | h | h | h
  · exfalso
    obtain ⟨α, hα, δ, hδ, h1, h2⟩ := hbig
    rcases g2_component_rank_one χ hp (hp5 rfl) hχp hχ1 i α hα δ hδ with h | h
    · exact h1 h
    · exact h2 h
  ·
    have hK23 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
    rcases hK23 with hc | hc
    · have hK2 := eq_zero_or_one_of_card_two hc
      by_cases hA2 : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
          iform α α = iform δ δ ∧ iform α δ ≠ 0
      · exact conclusion_of_perfect i (isPerfect_componentRootSpan_F4_two hK2 i hA2)
      · push Not at hA2
        obtain ⟨s, l, hss, hll, hsl, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
        exact ⟨b2_two_derived_quasisimple hK2 i hss hll hsl hΨ, Or.inl hc⟩
    · exact conclusion_of_perfect i
        (isPerfect_componentRootSpan_F4_of_two_ne_zero (two_ne_zero_of_card_three hc) i hbig)
  all_goals
    exact conclusion_of_perfect i (isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig)

theorem smallFieldInner_tame_of_prime {τ : Tag} {K : Type} [Field K] [Finite K] {M : Type}
    [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) {p : ℕ}
    (hp : p.Prime) (hp5 : τ = .G2 → 5 ≤ p)
    (hχp : ∀ γ, IsRoot τ γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    (hχ1 : ∃ γ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1) (hK : Nat.card K ≤ 3) :
    Group.IsSolvable (componentRootSpan K χ i) ∨
      (CFSG.IsQuasisimple ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :
        Subgroup (ModGL τ K)) ∧
        (Nat.card K = 2 ∨
          ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i)) := by
  classical
  by_cases hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α
  · exact Or.inl (isSolvable_componentRootSpan_of_rank_one hK i hrank)
  · exact Or.inr (smallFieldInner_quasisimple_of_not_rankOne χ i hp hp5 hχp hχ1 hK hrank)

end Residual

section InnerPrime

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem rationalComponent_inner_small_tame_of_prime (hp : p.Prime) (hW : RootAutIsWeyl)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner) (hp5 : τ = .G2 → 5 ≤ p)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S hW hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : r ^ (e * s) < 4 := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  set C := componentRootSpan (fixSubfield σ) (rootCharHom a) i with hCdef
  obtain ⟨f₁, hf₁1, -, -⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  rcases smallFieldInner_tame_of_prime (rootCharHom a) i hp hp5
      (fun γ hγ => rootChar_pow_eq_one_of_pow hTp hγ)
      (by obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one ha1; exact ⟨γ, hγ, hne⟩) hKle with
    hCsolv | ⟨hDQ, hD⟩
  ·
    refine Or.inr ?_
    have : Group.IsSolvable ↥C := hCsolv
    have : Group.IsSolvable ↥f₁.range := Group.isSolvable_of_surjective f₁.rangeRestrict_surjective
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hf₁1)
      (Subgroup.inclusion_injective hf₁1)
  refine Or.inl ?_
  have hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ (⁅C, C⁆).map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    rcases hD with hD2 | hDC
    · have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
        intro d hd hd0
        let : Fintype (fixSubfield σ) := Fintype.ofFinite _
        have hcard : Fintype.card (fixSubfield σ) = 2 := by
          rw [← Nat.card_eq_fintype_card]; exact hD2
        have hdK : d ∈ fixSubfield σ := hd
        have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : fixSubfield σ)
          (fun h => hd0 (congrArg Subtype.val h))
        rw [hcard] at h1
        simpa using congrArg Subtype.val h1
      have := orbit_commutator_mem_commutator_CQT S hT i hs hmin σ hsL hF hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
    · have := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← hDC] at this
  obtain ⟨f, hf1, hker, hf2⟩ := rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
    ⁅C, C⁆ (Subgroup.commutator_le_self _ |>.trans le_rfl) hY
  have hperfD : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := Subgroup.isPerfect_iff.1 hDQ.1
  rw [le_antisymm hf1 (hf2 hperfD)]
  exact isQuasisimple_range_of_ker_le_center hDQ f hker

end InnerPrime

section Inner

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem rationalComponent_inner_small_tame (hW : RootAutIsWeyl)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner) (hp5 : 5 ≤ p)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalComponent_inner_small_tame_of_prime S S.hp hW hT hTp ha1 i hkind (fun _ => hp5) hQ

end Inner

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
