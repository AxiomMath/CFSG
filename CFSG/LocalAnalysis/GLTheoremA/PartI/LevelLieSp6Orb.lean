module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6Prim
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

open Polynomial CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup)

variable {K : Type} [Field K]

theorem solvable_of_card_two_three {G : Type*} [Group G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])

theorem not_solvable_of_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (hs : Group.IsSolvable Q) : False := by
  obtain ⟨hp, hsimp, -⟩ := hQ
  haveI : Group.IsPerfect Q := hp
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimp.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
  exact Group.IsPerfect.not_isSolvable Q hs

theorem fixed_factor_iso [Finite K] {ℓ f : ℕ} {x : StatedSp 3 K}
    (blocks : SpPrimaryBlocks ℓ f 3 x (proj 3 K x)) (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) :
    ∃ s : ℕ, spFixedDim x = 2 * s ∧ Nonempty (spFixedFactor x ≃* StatedSp s K) := by
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm 3 K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin 3 ⊕ Fin 3 → K)
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
  exact ⟨s, hs, ⟨φ.trans e⟩⟩

theorem fixed_factor_solvable_of_small [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K}
    {s : ℕ} (hs : s ≤ 1) (e : spFixedFactor x ≃* StatedSp s K) :
    Group.IsSolvable ↥(spFixedFactor x) := by
  have hc : Nat.card (spFixedFactor x) = Nat.card (StatedSp s K) := Nat.card_congr e.toEquiv
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK] at hc
  interval_cases s
  · exact solvable_of_card_two_three (a := 0) (b := 0) (by rw [hc]; simp)
  · exact solvable_of_card_two_three (a := 1) (b := 1) (by rw [hc]; norm_num)

theorem gu_card_two_three {G : Type*} [Group G] {n f : ℕ} (hn : n ≤ 3) (hn1 : 1 ≤ n)
    (hf : f = 1)
    (hc : (Nat.card G : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 n, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i)) :
    ∃ a b : ℕ, Nat.card G = 2 ^ a * 3 ^ b := by
  subst hf
  interval_cases n
  · exact ⟨0, 1, by norm_num [Finset.Icc_self] at hc; exact_mod_cast hc⟩
  · exact ⟨1, 2, by norm_num [Finset.prod_Icc_succ_top] at hc; exact_mod_cast hc⟩
  · exact ⟨3, 4, by norm_num [Finset.prod_Icc_succ_top] at hc; exact_mod_cast hc⟩

theorem selfDual_solvable [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K}
    (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x)) (hmem : (X2K : K[X]) ∈ primaryFactors (spEnd x)) :
    Group.IsSolvable ↥(spSupported x {(X2K : K[X])}) := by
  haveI : Fact (Irreducible (X2K : K[X])) := ⟨X2K_irreducible hK⟩
  have hdeg : (X2K : K[X]).natDegree = 2 := by unfold X2K; compute_degree!
  have hne : (X2K : K[X]) ≠ X - 1 := by
    intro h
    have h1 := congrArg Polynomial.natDegree h
    rw [hdeg] at h1
    have h2 : (X - 1 : K[X]).natDegree = 1 := by compute_degree!
    omega
  obtain ⟨d, hd2, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
    (blocks.selfDual ⟨X2K, hmem⟩ hne reciprocal_X2K).exists_half
  have hd1 : d = 1 := by
    have : (X2K : K[X]).natDegree = 2 * d := hd2
    omega
  subst hd1
  have hfin : Module.finrank K (primaryComponent (spEnd x) (X2K : K[X])) =
      2 * primaryMultiplicity (spEnd x) (X2K : K[X]) := by
    rw [finrank_primaryComponent, hdeg]
  have hle : Module.finrank K (primaryComponent (spEnd x) (X2K : K[X])) ≤ 6 := by
    rw [← finrank_sixDim hK]
    exact Submodule.finrank_le _
  have hn3 : primaryMultiplicity (spEnd x) (X2K : K[X]) ≤ 3 := by omega
  have hcardφ : Nat.card (spSupported x {(X2K : K[X])}) = Nat.card (sesqUnitaryGroup Hf) :=
    Nat.card_congr φ.toEquiv
  rcases Nat.eq_zero_or_pos (primaryMultiplicity (spEnd x) (X2K : K[X])) with h0 | hpos
  ·
    have hV : ∀ v : ↥(primaryComponent (spEnd x) (X2K : K[X])), v = 0 := by
      exact (finrank_zero_iff_forall_zero (K := K)).1 (by omega)
    haveI : Subsingleton ↥(sesqUnitaryGroup Hf) :=
      ⟨fun a b => Subtype.ext (Units.ext (LinearMap.ext fun v => by
        rw [hV v, map_zero, map_zero]))⟩
    haveI : Nonempty ↥(sesqUnitaryGroup Hf) := ⟨1⟩
    have h1 : Nat.card (spSupported x {(X2K : K[X])}) = 1 := by
      rw [hcardφ]
      exact Nat.card_of_subsingleton (1 : ↥(sesqUnitaryGroup Hf))
    exact solvable_of_card_two_three (a := 0) (b := 0) (by rw [h1]; norm_num)
  · have hc := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      (n := primaryMultiplicity (spEnd x) (X2K : K[X])) rfl hpos).1
    obtain ⟨a, b, hab⟩ := gu_card_two_three (G := ↥(sesqUnitaryGroup Hf)) hn3 hpos rfl hc
    exact solvable_of_card_two_three (a := a) (b := b) (by rw [hcardφ, hab])

theorem reciprocalOrbit_cases [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K}
    (hx : x ^ 3 = 1) (O : ↥(reciprocalOrbits (spEnd x))) :
    ∃ h : K[X], h ∈ primaryFactors (spEnd x) ∧ (h = X - 1 ∨ h = X2K) ∧
      (O : Set K[X]) = {h} := by
  obtain ⟨h, hh, hO⟩ := O.2
  refine ⟨h, hh, primaryFactor_cases hK x hx hh, ?_⟩
  rw [← hO]
  exact reciprocalOrbit_singleton hK x hx hh

theorem commutator_solvable_of_solvable {A : Subgroup (StatedSp 3 K)}
    (hA : Group.IsSolvable ↥A) : Group.IsSolvable ↥⁅A, A⁆ := by
  have hle : ⁅A, A⁆ ≤ A := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem orbit_tame [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K} (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x))
    (O : ↥(reciprocalOrbits (spEnd x))) :
    (CFSG.IsQuasisimple ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ∧
        spFixedDim x = 4 ∧ (O : Set K[X]) = {X - 1}) ∨
      Group.IsSolvable ↥(spSupported x (O : Set K[X])) := by
  obtain ⟨h, hh, hcase, hO⟩ := reciprocalOrbit_cases hK hx O
  rcases hcase with rfl | rfl
  ·
    obtain ⟨s, hs, ⟨e⟩⟩ := fixed_factor_iso blocks hh
    have hdim : spFixedDim x = Module.finrank K (primaryComponent (spEnd x) (X - 1 : K[X])) := rfl
    have hle : Module.finrank K (primaryComponent (spEnd x) (X - 1 : K[X])) ≤ 6 := by
      rw [← finrank_sixDim hK]
      exact Submodule.finrank_le _
    by_cases h4 : s = 2
    · subst h4
      left
      obtain ⟨hq, -⟩ := spFixed_four_two hK blocks (by omega : spFixedDim x = 4)
      refine ⟨?_, by omega, hO⟩
      rw [hO]
      exact hq
    · right
      have hs1 : s ≤ 1 := by
        by_contra hcon
        have h3 : s = 3 := by omega
        apply hx1
        apply eq_one_of_fixed_finrank_six hK x
        omega
      rw [hO]
      exact fixed_factor_solvable_of_small hK hs1 e
  · right
    rw [hO]
    exact selfDual_solvable hK blocks hh

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

end
