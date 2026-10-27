module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFactor
import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem finrank_eq_sum_of_subset {y : Module.End K V} (hsq : Squarefree (minpoly K y))
    {S : Finset K[X]} (hS : primaryFactors y ⊆ S) (hirr : ∀ a ∈ S, Irreducible a ∧ a.Monic) :
    finrank K V = ∑ a ∈ S, finrank K (primaryComponent y a) := by
  rw [finrank_eq_sum_primaryComponent hsq,
    Finset.sum_coe_sort (primaryFactors y) fun a => finrank K (primaryComponent y a)]
  refine Finset.sum_subset hS fun a haS ha => ?_
  rw [CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem (hirr a haS).1 (hirr a haS).2
    ha, finrank_bot]

omit [Finite K] in
theorem disjoint_supportedBlock_of_orbit {p : ℕ} (hx : OddOrderIsometry Q p x) {h k : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hk : k ∈ primaryFactors x.toLinearMap)
    (hkh : k ≠ h) (hkh' : k ≠ reciprocalPolynomial h) :
    Disjoint (supportedBlock Q x h) (supportedBlock Q x k) := by
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  refine LinearEquiv.ext fun v => ?_
  have := congrArg (fun f : Module.End K V => f v) (ext_primaryComponent
    (f := g.toLinearMap) (g := LinearMap.id) hx.squarefree_minpoly fun a ha v hv => ?_)
  · exact this
  · by_cases hah : a = h ∨ a = reciprocalPolynomial h
    · obtain ⟨h1, h2⟩ := hx.orbit_disjoint hh hk hkh hkh' hah
      exact apply_eq_of_mem_supportedBlock hg' ha h1 h2 hv
    · exact apply_eq_of_mem_supportedBlock hg ha (fun e => hah (Or.inl e))
        (fun e => hah (Or.inr e)) hv

omit [Finite K] in
theorem orth_dvd_of_mem (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) :
    Irreducible h ∧ h.Monic ∧ h ∣ X ^ 2 + X + 1 := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  refine ⟨hirr, hmon, dvd_X_sq_add_X_add_one hirr hmon ?_ hX⟩
  have := hx.dvd_X_pow_sub_one hh
  rwa [show (X ^ 3 - 1 : K[X]) = X ^ 3 - C 1 by rw [map_one]] at this

theorem exists_orth_factor (hx : OddOrderIsometry Q 3 x)
    (hlt : finrank K (fixedSpace x) < finrank K V) :
    ∃ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 ∧ reciprocalPolynomial h ≠ X - 1 ∧
      h.natDegree ≤ 2 ∧ (h ≠ reciprocalPolynomial h → h.natDegree = 1) ∧
      finrank K V = finrank K (fixedSpace x) + 2 * primaryMultiplicity x.toLinearMap h := by
  classical
  have hsq := hx.squarefree_minpoly
  have hirrX : Irreducible (X - 1 : K[X]) ∧ (X - 1 : K[X]).Monic :=
    ⟨irreducible_X_sub_one, monic_X_sub_one⟩
  have hV₁ : finrank K (fixedSpace x) = finrank K (primaryComponent x.toLinearMap (X - 1)) := by
    rw [fixedSpace_eq_primaryComponent]
  obtain ⟨h₀, hh₀, hX₀⟩ : ∃ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 := by
    by_contra hall
    push Not at hall
    have := finrank_eq_sum_of_subset hsq (S := {X - 1}) (fun a ha => Finset.mem_singleton.mpr
      (hall a ha)) fun a ha => (Finset.mem_singleton.mp ha) ▸ hirrX
    rw [Finset.sum_singleton, ← hV₁] at this
    omega
  have hrecX : reciprocalPolynomial h₀ ≠ X - 1 := fun h1 => hX₀ (by
    rw [← hx.reciprocal_reciprocal_eq hh₀, h1, reciprocalPolynomial_X_sub_one])
  have hfac₀ := orth_dvd_of_mem hx hh₀ hX₀
  have hdeg₀ : h₀.natDegree ≤ 2 := (natDegree_le_of_dvd hfac₀.2.2 X_sq_add_X_add_one_ne_zero).trans
    natDegree_X_sq_add_X_add_one.le
  have : Fact (Irreducible h₀) := ⟨hfac₀.1⟩
  have hdim₀ := finrank_primaryComponent x.toLinearMap h₀
  have hm : primaryMultiplicity x.toLinearMap h₀ =
      finrank (AdjoinRoot h₀) (primaryComponent x.toLinearMap h₀) := rfl
  refine ⟨h₀, hh₀, hX₀, hrecX, hdeg₀, ?_⟩
  by_cases hself : h₀ = reciprocalPolynomial h₀
  · obtain ⟨d, -, hd, -⟩ := hx.exists_selfDual_hermitian (by decide) hh₀ hX₀ hself
    have hpos := hfac₀.1.natDegree_pos
    have h2 : h₀.natDegree = 2 := by omega
    have huniq : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 → h = h₀ := fun h hh hX => by
      obtain ⟨hirr, hmon, hdvd⟩ := orth_dvd_of_mem hx hh hX
      exact eq_of_dvd_of_natDegree_eq_two hfac₀.1 hfac₀.2.1 hfac₀.2.2 h2 hirr hmon hdvd
    have hsum := finrank_eq_sum_of_subset hsq (S := {X - 1, h₀}) (fun a ha => by
      by_cases haX : a = X - 1
      · exact haX ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (huniq a ha haX))) fun a ha => by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hirrX
      · rw [Finset.mem_singleton.mp ha]; exact ⟨hfac₀.1, hfac₀.2.1⟩
    rw [Finset.sum_pair (Ne.symm hX₀), ← hV₁, hdim₀, h2] at hsum
    exact ⟨fun h => absurd hself h, hsum⟩
  · have hh₀' := hx.reciprocalPolynomial_mem hh₀
    have hfac₀' := orth_dvd_of_mem hx hh₀' hrecX
    obtain ⟨h1, hprod⟩ := natDegree_eq_one_of_pair hfac₀.1 hfac₀.2.1 hfac₀.2.2 hfac₀'.1
      hfac₀'.2.1 hfac₀'.2.2 hself (natDegree_reciprocalPolynomial (hx.coeff_zero_ne hh₀)).symm
    have huniq : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
        h = h₀ ∨ h = reciprocalPolynomial h₀ := fun h hh hX => by
      obtain ⟨hirr, hmon, hdvd⟩ := orth_dvd_of_mem hx hh hX
      exact eq_or_eq_of_pair hfac₀.2.1 hfac₀.1 hfac₀'.2.1 hfac₀'.1 hprod hirr hmon hdvd
    have hsum := finrank_eq_sum_of_subset hsq (S := {X - 1, h₀, reciprocalPolynomial h₀})
      (fun a ha => by
        by_cases haX : a = X - 1
        · exact haX ▸ Finset.mem_insert_self _ _
        · rcases huniq a ha haX with rfl | rfl
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_singleton_self _))) fun a ha => by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hirrX
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨hfac₀.1, hfac₀.2.1⟩
      · rw [Finset.mem_singleton.mp ha]; exact ⟨hfac₀'.1, hfac₀'.2.1⟩
    have hpair : finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial h₀)) =
        finrank K (primaryComponent x.toLinearMap h₀) := by
      rw [(LinearEquiv.ofBijective _ (hx.pairing_flip_bijective hh₀)).finrank_eq,
        Subspace.dual_finrank_eq]
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hX₀, Ne.symm hrecX⟩),
      Finset.sum_pair hself, ← hV₁, hpair, hdim₀, h1, one_mul] at hsum
    exact ⟨fun _ => h1, by omega⟩

theorem perfectNoncycThreeIn_isometryCentralizer [CharP K 2] (hx : OddOrderIsometry Q 3 x)
    {r : ℕ} (hdim : finrank K V = 2 * r)
    (hr : (4 ≤ Nat.card K ∧ 4 ≤ r) ∨ (Nat.card K = 2 ∧ 6 ≤ r)) :
    PerfectNoncycThreeIn (isometryCentralizer Q x) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  by_cases h6 : 6 ≤ finrank K (fixedSpace x)
  · exact (perfectNoncycThreeIn_orthFixed hx h6).mono (supportedBlock_le_isometryCentralizer _)
  obtain ⟨h, hh, hX, hrecX, hdeg, hdeg1, hsum⟩ := exists_orth_factor hx (by omega)
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hK := card_eq_two_or_four_le K
  have htwo : 4 ≤ Nat.card K → finrank K (fixedSpace x) = 4 →
      PerfectThreeIn (supportedBlock Q x h) → PerfectNoncycThreeIn (isometryCentralizer Q x) := by
    intro hK4 hd4 hP₂
    have hX1 : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
      by_contra hn
      rw [fixedSpace_eq_primaryComponent,
        CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one
          monic_X_sub_one hn, finrank_bot] at hd4
      omega
    have hne' : h ≠ reciprocalPolynomial (X - 1) := by rw [reciprocalPolynomial_X_sub_one]; exact hX
    exact PerfectNoncycThreeIn.of_two (supportedBlock_le_isometryCentralizer _)
      (supportedBlock_le_isometryCentralizer _)
      (fun g hg g' hg' => hx.commute_supportedBlock hX1 hh hX hne' hg hg')
      (disjoint_supportedBlock_of_orbit hx hX1 hh hX hne')
      (perfectThreeIn_orthFixed hx hd4 hK4) hP₂
  by_cases hself : h = reciprocalPolynomial h
  · by_cases hm3 : 3 ≤ primaryMultiplicity x.toLinearMap h ∧
        (primaryMultiplicity x.toLinearMap h = 3 → 4 ≤ Nat.card K)
    · exact (perfectNoncycThreeIn_orthSelfDual hx hh hX hself hdeg hm3.1 hm3.2).mono
        (supportedBlock_le_isometryCentralizer _)
    · have hK4 : 4 ≤ Nat.card K := by omega
      exact htwo hK4 (by omega) (perfectThreeIn_orthSelfDual hx hh hX hself hdeg (by omega) hK4)
  · by_cases hm3 : 3 ≤ primaryMultiplicity x.toLinearMap h
    · exact (perfectNoncycThreeIn_orthPaired hx hh hX hself hm3).mono
        (supportedBlock_le_isometryCentralizer _)
    · have hK4 : 4 ≤ Nat.card K := by omega
      exact htwo hK4 (by omega) (perfectThreeIn_orthPaired hx hh hX hself (by omega) hK4)

end CFSG.AGLEmbedding.ToralCensus
