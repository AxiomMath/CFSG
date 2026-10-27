module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSp

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {f r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {a : StatedProj (StatedSp r K)}

open scoped Classical in
theorem exists_factor_of_lt (HB : SpPrimaryBlocks 2 f 3 x a) (hx3 : x ^ 3 = 1) {s : ℕ}
    (hs : finrank K (primaryComponent (spEnd x) (X - 1)) = 2 * s) (hsr : s < r) :
    ∃ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 ∧
      primaryMultiplicity (spEnd x) h = r - s ∧ (h : K[X]).natDegree ≤ 2 ∧
      ((h : K[X]) ≠ reciprocalPolynomial (h : K[X]) → (h : K[X]).natDegree = 1) := by
  obtain ⟨s', hs', ⟨P₀, hP₀⟩, hsum⟩ := HB.rank
  have hss : s' = s := by omega
  subst hss
  have key := hsum P₀ hP₀
  have hfac : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 →
      Irreducible h ∧ h.Monic ∧ h ∣ X ^ 2 + X + 1 := fun h hh hX =>
    ⟨irreducible_of_mem_primaryFactors hh, monic_of_mem_primaryFactors hh,
      dvd_X_sq_add_X_add_one (irreducible_of_mem_primaryFactors hh)
        (monic_of_mem_primaryFactors hh) (dvd_of_mem_primaryFactors hx3 hh) hX⟩
  have hdeg2 : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → h.natDegree ≤ 2 := fun h hh hX =>
    (natDegree_le_of_dvd (hfac h hh hX).2.2 X_sq_add_X_add_one_ne_zero).trans
      natDegree_X_sq_add_X_add_one.le
  have hrecX : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 →
      reciprocalPolynomial h ≠ X - 1 := fun h hh hX h1 => by
    have hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := h1 ▸ HB.bijOn.mapsTo hh
    exact hX (HB.bijOn.injOn hh hX1 (by rw [h1, reciprocalPolynomial_X_sub_one]))
  by_cases hsd : ∃ h ∈ primaryFactors (spEnd x), reciprocalPolynomial h = h ∧ h ≠ X - 1
  · obtain ⟨h₀, hh₀, hself₀, hX₀⟩ := hsd
    obtain ⟨d, hd, -⟩ := (HB.selfDual ⟨h₀, hh₀⟩ hX₀ hself₀).exists_half
    have hpos := (irreducible_of_mem_primaryFactors hh₀).natDegree_pos
    have hdeg₀ : h₀.natDegree = 2 := by
      have := hdeg2 h₀ hh₀ hX₀
      simp only at hd
      omega
    obtain ⟨hirr₀, hmon₀, hdvd₀⟩ := hfac h₀ hh₀ hX₀
    have huniq : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → h = h₀ := fun h hh hX => by
      obtain ⟨hirr, hmon, hdvd⟩ := hfac h hh hX
      exact eq_of_dvd_of_natDegree_eq_two hirr₀ hmon₀ hdvd₀ hdeg₀ hirr hmon hdvd
    have hP0 : ∑ h ∈ P₀, h.natDegree * primaryMultiplicity (spEnd x) h = 0 :=
      Finset.sum_eq_zero fun h hh => by
        obtain ⟨hhΦ, hne⟩ := hP₀.1 h hh
        have hX : h ≠ X - 1 := fun h1 => hne (by rw [h1, reciprocalPolynomial_X_sub_one])
        exact absurd (by rw [huniq h hhΦ hX, hself₀]) hne
    have hF : (primaryFactors (spEnd x)).filter
        (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) = {h₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hh₀, hself₀, hX₀⟩,
        fun h hh => huniq h (Finset.mem_filter.mp hh).1 (Finset.mem_filter.mp hh).2.2⟩
    rw [hP0, add_zero, hF, Finset.sum_singleton, hdeg₀] at key
    refine ⟨⟨h₀, hh₀⟩, hX₀, ?_, ?_, fun h => absurd hself₀.symm h⟩
    · show primaryMultiplicity (spEnd x) h₀ = r - s'
      omega
    · show h₀.natDegree ≤ 2
      omega
  · push Not at hsd
    have hF : (primaryFactors (spEnd x)).filter
        (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) = ∅ :=
      Finset.filter_false_of_mem fun h hh hc => hc.2 (hsd h hh hc.1)
    rw [hF, Finset.sum_empty, add_zero] at key
    obtain ⟨h₀, hh₀P⟩ : P₀.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      rw [Finset.sum_empty] at key
      omega
    obtain ⟨hh₀, hne₀⟩ := hP₀.1 h₀ hh₀P
    have hX₀ : h₀ ≠ X - 1 := fun h1 => hne₀ (by rw [h1, reciprocalPolynomial_X_sub_one])
    have hh₀' := HB.bijOn.mapsTo hh₀
    obtain ⟨hirr₀, hmon₀, hdvd₀⟩ := hfac h₀ hh₀ hX₀
    obtain ⟨hirr₀', hmon₀', hdvd₀'⟩ := hfac _ hh₀' (hrecX h₀ hh₀ hX₀)
    obtain ⟨hdeg₀, hprod⟩ := natDegree_eq_one_of_pair hirr₀ hmon₀ hdvd₀ hirr₀' hmon₀' hdvd₀'
      hne₀ (HB.paired ⟨h₀, hh₀⟩ hne₀).natDegree_eq
    have hP : P₀ = {h₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hh₀P, fun h hh => by
      obtain ⟨hhΦ, hne⟩ := hP₀.1 h hh
      have hX : h ≠ X - 1 := fun h1 => hne (by rw [h1, reciprocalPolynomial_X_sub_one])
      obtain ⟨hirr, hmon, hdvd⟩ := hfac h hhΦ hX
      rcases eq_or_eq_of_pair hmon₀ hirr₀ hmon₀' hirr₀' hprod hirr hmon hdvd with rfl | rfl
      · rfl
      · exact absurd hh (hP₀.2.2 h₀ hh₀P)⟩
    rw [hP, Finset.sum_singleton, hdeg₀, one_mul] at key
    refine ⟨⟨h₀, hh₀⟩, hX₀, ?_, ?_, fun _ => hdeg₀⟩
    · show primaryMultiplicity (spEnd x) h₀ = r - s'
      omega
    · show h₀.natDegree ≤ 2
      omega

variable [Finite K]

theorem perfectNoncycThreeIn_of_two_factors (HB : SpPrimaryBlocks 2 f 3 x a) {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x)) (hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (hX : h ≠ X - 1) (hX' : reciprocalPolynomial h ≠ X - 1)
    (h₁ : PerfectThreeIn (spSupported x {X - 1}))
    (h₂ : PerfectThreeIn (spSupported x {h, reciprocalPolynomial h})) :
    PerfectNoncycThreeIn (Subgroup.centralizer ({x} : Set (StatedSp r K))) := by
  obtain ⟨hcomm, hind, -⟩ := HB.directProduct
  have hO₁ : ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
    ⟨X - 1, hX1, rfl⟩
  have hO₂ : ({h, reciprocalPolynomial h} : Set K[X]) ∈ reciprocalOrbits (spEnd x) := ⟨h, hh, rfl⟩
  have hne : ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) ≠ {h, reciprocalPolynomial h} :=
    fun he => by
      have : (X - 1 : K[X]) ∈ ({h, reciprocalPolynomial h} : Set K[X]) := he ▸ Set.mem_insert _ _
      rcases this with h1 | h1
      exacts [hX h1.symm, hX' h1.symm]
  have hdisj : Disjoint (spSupported x {X - 1, reciprocalPolynomial (X - 1)})
      (spSupported x {h, reciprocalPolynomial h}) :=
    hind.pairwiseDisjoint (show (⟨_, hO₁⟩ : reciprocalOrbits (spEnd x)) ≠ ⟨_, hO₂⟩
      from fun he => hne (congrArg Subtype.val he))
  rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton] at hO₁ hne hdisj
  exact PerfectNoncycThreeIn.of_two (spSupported_le_centralizer _) (spSupported_le_centralizer _)
    (fun g hg g' hg' => hcomm _ hO₁ _ hO₂ hne g hg g' hg') hdisj h₁ h₂

theorem perfectNoncycThreeIn_centralizer_of_blocks (hK : Nat.card K = 2 ^ f)
    (hr : (2 ≤ f ∧ 3 ≤ r) ∨ (f = 1 ∧ 5 ≤ r)) (HB : SpPrimaryBlocks 2 f 3 x a)
    (hx3 : x ^ 3 = 1) : PerfectNoncycThreeIn (Subgroup.centralizer ({x} : Set (StatedSp r K))) := by
  have hf : 1 ≤ f := by omega
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨s, hs, -⟩ := HB.rank
  by_cases hs2 : 2 ≤ s
  · exact (perfectNoncycThreeIn_spFixed HB (by omega)).mono (spSupported_le_centralizer _)
  obtain ⟨h, hX, hm, hdeg, hdeg1⟩ := exists_factor_of_lt HB hx3 hs (by omega)
  have hrecX : reciprocalPolynomial (h : K[X]) ≠ X - 1 := fun h1 => by
    have hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := h1 ▸ HB.bijOn.mapsTo h.2
    exact hX (HB.bijOn.injOn h.2 hX1 (by rw [h1, reciprocalPolynomial_X_sub_one]))
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · by_cases hm3 : 3 ≤ primaryMultiplicity (spEnd x) h ∧
        (primaryMultiplicity (spEnd x) h = 3 → 2 ≤ f)
    · exact (perfectNoncycThreeIn_spSelfDual HB h hX hself hdeg hm3.1 hm3.2).mono
        (spSupported_le_centralizer _)
    · have hf2 : 2 ≤ f := by omega
      have hs1 : s = 1 := by omega
      exact perfectNoncycThreeIn_of_two_factors HB h.2 (X_sub_one_mem_of_finrank_pos (by omega))
        hX hrecX (perfectThreeIn_spFixed HB (by omega) (by rw [hK]; exact
          (Nat.pow_le_pow_right (by norm_num) hf2 : 2 ^ 2 ≤ 2 ^ f)))
        (perfectThreeIn_spSelfDual HB hf2 h hX hself hdeg (by omega))
  · have hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]) := Ne.symm hself
    by_cases hm3 : 3 ≤ primaryMultiplicity (spEnd x) h
    · exact (perfectNoncycThreeIn_spPaired HB h hne hX hm3).mono (spSupported_le_centralizer _)
    · have hf2 : 2 ≤ f := by omega
      have hs1 : s = 1 := by omega
      exact perfectNoncycThreeIn_of_two_factors HB h.2 (X_sub_one_mem_of_finrank_pos (by omega))
        hX hrecX (perfectThreeIn_spFixed HB (by omega) (by rw [hK]; exact
          (Nat.pow_le_pow_right (by norm_num) hf2 : 2 ^ 2 ≤ 2 ^ f)))
        (perfectThreeIn_spPaired HB hf2 h hne hX (by omega))

theorem centNoncycThreeGroup_statedProj_statedSp (hK : Nat.card K = 2 ^ f)
    (hr : (2 ≤ f ∧ 3 ≤ r) ∨ (f = 1 ∧ 5 ≤ r)) :
    CentNoncycThreeGroup (StatedProj (StatedSp r K)) := by
  have hf : 1 ≤ f := by omega
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  intro a ha3 ha1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, ⟨hxa, hxo⟩, -⟩, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks
    Nat.prime_two hf hK Nat.prime_three (by norm_num) (by norm_num) (by omega) a
    (orderOf_eq_prime ha3 ha1)
  have HB := hblocks x hxa hxo
  rw [HB.centralizer_eq]
  exact (perfectNoncycThreeIn_centralizer_of_blocks hK hr HB (hxo ▸ pow_orderOf_eq_one x)).map
    (proj r K) (proj_injective_of_charTwo (by omega))

theorem centNoncycThreeGroup_of_model_psp {X : Type} [Group X]
    (h : StatedClassicalModel X .PSp r 2 f) (hr : (2 ≤ f ∧ 3 ≤ r) ∨ (f = 1 ∧ 5 ≤ r)) :
    CentNoncycThreeGroup X := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  exact (centNoncycThreeGroup_statedProj_statedSp hF hr).of_mulEquiv e

end CFSG.AGLEmbedding.ToralCensus
