module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6KillString
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeKillStatement

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def TwKillSquareStep
    (σ : K →+* K) (J : Set (Fin TwistTag.E6.tag.rank)) (i : Fin TwistTag.E6.tag.rank) (c : K) :
    Prop :=
  ∀ (R : Set (Fin TwistTag.E6.tag.rank → ℤ)) (δ : Fin TwistTag.E6.tag.rank → ℤ)
    (z n : ModGL TwistTag.E6.tag K), TwKillAdm J i R →
    (∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R) → TwKillMin i R δ →
    TwistTag.E6.perm i ≠ i → IsRoot TwistTag.E6.tag (δ + Pi.single i 1) →
    IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1) →
    z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i) → twistHom TwistTag.E6 K σ z = z →
    n ∈ rootSpan TwistTag.E6.tag K R → twistHom TwistTag.E6 K σ n = n →
    twKillA σ i c * (z * n) * twKillA σ i c = (z * n)⁻¹ →
    TwKillStep σ J i (twKillA σ i c) R z n


theorem twKill_perm_add_single (v : Fin TwistTag.E6.tag.rank → ℤ) (j : Fin TwistTag.E6.tag.rank) :
    permLattice TwistTag.E6.perm (v + Pi.single j 1) =
      permLattice TwistTag.E6.perm v + Pi.single (TwistTag.E6.perm j) 1 := by
  rw [← twKill_perm_single]
  rfl

theorem twKill_exists_step [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) {c : K} (hc : c ≠ 0)
    (hcσ : TwistTag.E6.perm i = i → σ c = c) (hsq : TwKillSquareStep σ J i c)
    {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    (hRρ : ∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R) (hRne : R.Nonempty)
    {z n : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i))
    (hFz : twistHom TwistTag.E6 K σ z = z) (hn : n ∈ rootSpan TwistTag.E6.tag K R)
    (hFn : twistHom TwistTag.E6 K σ n = n)
    (hcoc : twKillA σ i c * (z * n) * twKillA σ i c = (z * n)⁻¹) :
    TwKillStep σ J i (twKillA σ i c) R z n := by
  have hAA := twKillA_mul_self σ i c
  obtain ⟨δ, hmin⟩ := twKill_exists_min hR hRne
  by_cases hp : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1) ∧
      ¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1)
  · by_cases hρδ : permLattice TwistTag.E6.perm δ = δ
    · exact twKill_step_perp_fixed hR hRρ hmin hp.1 hp.2 hρδ hAA hz hFz hn hFn
    · exact twKill_step_perp_pair hσσ hJ hR hRρ hmin hp.1 hp.2 hρδ (twKillA_mem σ hJ hi c) hAA
        (twKillA_F hσσ hcσ) hz hFz hn hFn
  obtain ⟨δ₀, hmin₀, hδ₀a⟩ : ∃ δ₀, TwKillMin i R δ₀ ∧ IsRoot TwistTag.E6.tag (δ₀ + Pi.single i 1) := by
    by_cases ha : IsRoot TwistTag.E6.tag (δ + Pi.single i 1)
    · exact ⟨δ, hmin, ha⟩
    · have ha' : IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1) := by tauto
      refine ⟨permLattice TwistTag.E6.perm δ, hmin.perm hRρ, ?_⟩
      have e := twKill_perm_add_single δ (TwistTag.E6.perm i)
      rw [twistedE6_perm_perm] at e
      rw [← e]
      exact ha'.permLattice TwistTag.E6.cartan_perm
  have hδ₀Ψ := hR.subset hmin₀.mem
  by_cases hsqc : TwistTag.E6.perm i ≠ i ∧
      IsRoot TwistTag.E6.tag (δ₀ + Pi.single (TwistTag.E6.perm i) 1)
  · exact hsq R δ₀ z n hR hRρ hmin₀ hsqc.1 hδ₀a hsqc.2 hz hFz hn hFn hcoc
  have hb : TwistTag.E6.perm i = i ∨
      (¬IsRoot TwistTag.E6.tag (δ₀ + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ₀ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ₀ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1)) := by
    by_cases hfix : TwistTag.E6.perm i = i
    · exact Or.inl hfix
    · have h4 : ¬IsRoot TwistTag.E6.tag (δ₀ + Pi.single (TwistTag.E6.perm i) 1) :=
        fun h => hsqc ⟨hfix, h⟩
      obtain ⟨f1, f2⟩ := twKill_string_facts hfix hδ₀Ψ.1.2.1 hδ₀Ψ.1.2.2
        (hmin₀.not_isRoot_sub hR (Or.inl rfl)) (hmin₀.not_isRoot_sub hR (Or.inr rfl)) hδ₀a h4
      exact Or.inr ⟨h4, f1, f2⟩
  by_cases hρδ₀ : permLattice TwistTag.E6.perm δ₀ = δ₀
  · have hfix : TwistTag.E6.perm i = i := by
      by_contra hfix
      apply (hb.resolve_left hfix).1
      have e := twKill_perm_add_single δ₀ i
      rw [hρδ₀] at e
      rw [← e]
      exact hδ₀a.permLattice TwistTag.E6.cartan_perm
    exact twKill_step_string_fixed hσσ hJ hi hfix hc (hcσ hfix) hR hRρ hmin₀ hδ₀a hρδ₀ hz hFz hn
      hFn hcoc
  · exact twKill_step_string_pair hσσ hJ hi hc hcσ hR hRρ hmin₀ hδ₀a hb hρδ₀ hz hFz hn hFn hcoc

theorem twKill_core [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) {c : K} (hc : c ≠ 0)
    (hcσ : TwistTag.E6.perm i = i → σ c = c) (hsq : TwKillSquareStep σ J i c) (k : ℕ) :
    ∀ R : Set (Fin TwistTag.E6.tag.rank → ℤ), R.ncard = k → TwKillAdm J i R →
      (∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R) →
      ∀ z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i), twistHom TwistTag.E6 K σ z = z →
      ∀ n ∈ rootSpan TwistTag.E6.tag K R, twistHom TwistTag.E6 K σ n = n →
      twKillA σ i c * (z * n) * twKillA σ i c = (z * n)⁻¹ →
      ∃ p ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
          {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}),
        twistHom TwistTag.E6 K σ p = p ∧
        twKillA σ i c * p * twKillA σ i c * (z * n) * p⁻¹ ∈
          rootSpan TwistTag.E6.tag K (twKillPerp J i) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro R hRk hR hRρ z hz hFz n hn hFn hcoc
  have hAA := twKillA_mul_self σ i c
  rcases R.eq_empty_or_nonempty with hR0 | hRne
  · subst hR0
    have hn1 : n = 1 := by
      have hbot : rootSpan TwistTag.E6.tag K (∅ : Set (Fin TwistTag.E6.tag.rank → ℤ)) = ⊥ :=
        iSup₂_eq_bot.2 fun β hβ => absurd hβ (Set.notMem_empty β)
      rw [hbot, Subgroup.mem_bot] at hn
      exact hn
    refine ⟨1, one_mem _, map_one _, ?_⟩
    rw [hn1, mul_one, mul_one, inv_one, mul_one, hAA, one_mul]
    exact hz
  obtain ⟨R', hR', hR'ρ, hcard, p, hp, hFp, z', hz', hFz', n', hn', hFn', heq⟩ :=
    twKill_exists_step hσσ hJ hi hc hcσ hsq hR hRρ hRne hz hFz hn hFn hcoc
  have hcoc' : twKillA σ i c * (z' * n') * twKillA σ i c = (z' * n')⁻¹ := by
    rw [← heq]
    exact classKill_tw_cocycle hAA hcoc
  obtain ⟨p', hp', hFp', hres⟩ := ih _ (hRk ▸ hcard) R' rfl hR' hR'ρ z' hz' hFz' n' hn' hFn' hcoc'
  refine ⟨p' * p, mul_mem hp' hp, by rw [map_mul, hFp', hFp], ?_⟩
  rw [← classKill_tw_comp hAA, heq]
  exact hres

theorem exists_twKill_conj [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) {c : K} (hc : c ≠ 0)
    (hcσ : TwistTag.E6.perm i = i → σ c = c) (hsq : TwKillSquareStep σ J i c)
    {u : ModGL TwistTag.E6.tag K} (hu : u ∈ rootSpan TwistTag.E6.tag K
      (parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}))
    (hFu : twistHom TwistTag.E6 K σ u = u) (h2 : (twKillA σ i c * u) ^ 2 = 1) :
    ∃ p ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
        {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}),
      twistHom TwistTag.E6 K σ p = p ∧
      ∃ u'' ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i), twistHom TwistTag.E6 K σ u'' = u'' ∧
        p * (twKillA σ i c * u) * p⁻¹ = twKillA σ i c * u'' := by
  have hAA := twKillA_mul_self σ i c
  have hFA := twKillA_F hσσ hcσ
  have hcoc : twKillA σ i c * (1 * u) * twKillA σ i c = (1 * u)⁻¹ := by
    rw [one_mul]
    have h2' : twKillA σ i c * u * (twKillA σ i c * u) = 1 := by
      rw [← pow_two]
      exact h2
    calc twKillA σ i c * u * twKillA σ i c
        = twKillA σ i c * u * (twKillA σ i c * u) * u⁻¹ := by group
      _ = u⁻¹ := by rw [h2', one_mul]
  obtain ⟨p, hp, hFp, hres⟩ := twKill_core hσσ hJ hi hc hcσ hsq _ _ rfl (twKillAdm_top hJ hi)
    (fun β hβ => twKill_perm_mem_sdiff hJ hβ) 1 (one_mem _) (map_one _) u hu hFu hcoc
  refine ⟨p, hp, hFp, _, hres, ?_, ?_⟩
  · simp only [map_mul, map_inv, hFA, hFp, hFu, map_one]
  · calc p * (twKillA σ i c * u) * p⁻¹
        = twKillA σ i c * twKillA σ i c * p * (twKillA σ i c * u) * p⁻¹ := by rw [hAA, one_mul]
      _ = twKillA σ i c * (twKillA σ i c * p * twKillA σ i c * (1 * u) * p⁻¹) := by group

theorem twKill_mem_twistedFixedGroup {σ : K →+* K} {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ rootSpan TwistTag.E6.tag K S)
    (hF : twistHom TwistTag.E6 K σ g = g) : g ∈ twistedFixedGroup TwistTag.E6 K σ :=
  Subgroup.mem_inf.2 ⟨(iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
    rootSpan TwistTag.E6.tag K S ≤ adjointGroup TwistTag.E6.tag K) hg, hF⟩

theorem twistedE6KillFixed [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) :
    TwistedE6KillFixed K σ := by
  intro J hJ i hi hfix c hc hcσ u hu hΓu h2
  have hsq : TwKillSquareStep σ J i c := fun _ _ _ _ _ _ _ hne => absurd hfix hne
  have hset : parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1} =
        parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1} := by
    rw [hfix, Set.pair_eq_singleton]
  have hperp : twKillPerp J i = classKillPerp TwistTag.E6.tag J i := by
    rw [twKillPerp, hfix, Set.inter_self]
  have hA : twKillA σ i c = pinnedX TwistTag.E6.tag K (Pi.single i 1) c := twKillA_of_fixed σ hfix c
  have hFu : twistHom TwistTag.E6 K σ u = u := hΓu.2
  obtain ⟨p, hp, hFp, u'', hu'', hFu'', he⟩ := exists_twKill_conj hσσ hJ hi hc (fun _ => hcσ)
    hsq (by rw [hset]; exact hu) hFu (by rw [hA]; exact h2)
  rw [hset] at hp
  rw [hperp] at hu''
  rw [hA] at he
  exact ⟨p, hp, twKill_mem_twistedFixedGroup hp hFp, u'', hu'',
    twKill_mem_twistedFixedGroup hu'' hFu'', he⟩

theorem twistedE6KillPair_of_square [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (hsq : ∀ J i c, (∀ j ∈ J, TwistTag.E6.perm j ∈ J) → i ∈ J → TwistTag.E6.perm i ≠ i →
      c ≠ 0 → TwKillSquareStep σ J i c) :
    TwistedE6KillPair K σ := by
  intro J hJ i hi hne c hc u hu hΓu h2
  have hA : twKillA σ i c = twistedE6PairX σ (Pi.single i 1) c := twKillA_of_ne σ hne c
  have hFu : twistHom TwistTag.E6 K σ u = u := hΓu.2
  obtain ⟨p, hp, hFp, u'', hu'', hFu'', he⟩ := exists_twKill_conj hσσ hJ hi hc
    (fun h => absurd h hne) (hsq J i c hJ hi hne hc) hu hFu (by rw [hA]; exact h2)
  rw [hA] at he
  exact ⟨p, hp, twKill_mem_twistedFixedGroup hp hFp, u'', hu'',
    twKill_mem_twistedFixedGroup hu'' hFu'', he⟩

end CFSG.SeitzReduction
