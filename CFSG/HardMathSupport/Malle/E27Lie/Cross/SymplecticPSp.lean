module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticOrder
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.MapPerfect
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.PrimaryCount

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Polynomial Module Matrix CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

theorem spBlockFacts_nontrivial_three {ℓ f : ℕ} {x : StatedSp r K} (hq4 : 4 ≤ ℓ ^ f)
    (blocks : SpPrimaryBlocks ℓ f 3 x (proj r K x)) (h : primaryFactors (spEnd x))
    (hh : (h : K[X]) ≠ X - 1) : SpBlockFacts (spForm r K) (spLin r K x) h := by
  by_cases hself : KCOrthogonal.reciprocalPolynomial (h : K[X]) = h
  · have hS := blocks.selfDual h hh hself
    obtain ⟨d, hd2, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
    have hO : ({(h : K[X]), KCOrthogonal.reciprocalPolynomial (h : K[X])} : Set K[X]) =
        {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    refine spBlockFacts_of_selfDual hE hHf hHfl ((spOrbitEquiv x hO).trans φ) (fun g v hv => ?_) ?_
    · rw [MulEquiv.trans_apply]
      have := hφ (spOrbitEquiv x hO g) v hv
      rw [this, spEnd_orbitEquiv]
    · have hdeg : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      have hd1 : d ≠ 0 := by omega
      calc 4 ≤ ℓ ^ f := hq4
        _ ≤ (ℓ ^ f) ^ d := Nat.le_self_pow hd1 _
        _ = ℓ ^ (f * d) := (pow_mul ℓ f d).symm
  · have hP := blocks.paired h (Ne.symm hself)
    obtain ⟨φ, hφ, -⟩ := hP.factor
    refine spBlockFacts_of_paired ((spOrbitEquiv x rfl).trans φ) (fun g v hv => ?_) ?_
    · rw [MulEquiv.trans_apply, hφ, spEnd_orbitEquiv]
    · have hdeg : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
      have hcard : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
        rw [hP.card_field]
        omega
      have : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
      exact exists_finset_card_four_of_card hcard

theorem three_dvd_card_sq_sub_one {Q : ℕ} (hQ : ¬ 3 ∣ Q) : 3 ∣ Q ^ 2 - 1 := by
  have h1 : Q % 3 = 1 ∨ Q % 3 = 2 := by omega
  have h2 : Q ^ 2 % 3 = 1 := by
    rcases h1 with h | h <;> simp [pow_two, Nat.mul_mod, h]
  have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

variable [Finite K]

theorem three_dvd_card_spFixedFactor {ℓ f p : ℕ} {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hd : 2 ≤ spFixedDim x)
    (hnd : ¬ 3 ∣ Nat.card K) : 3 ∣ Nat.card ↥(spFixedFactor x) := by
  have hmem := X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  obtain ⟨s', hs', ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
  have hs1 : 1 ≤ s' := by
    have : finrank K (primaryComponent (spEnd x) (X - 1)) = spFixedDim x := rfl
    omega
  change 3 ∣ Nat.card ↥(spSupported x {X - 1})
  rw [Nat.card_congr (φ.trans e).toEquiv, SymplecticFlag.card_statedSp]
  refine Dvd.dvd.mul_left ?_ _
  refine (three_dvd_card_sq_sub_one hnd |>.trans ?_)
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 s' := Finset.mem_Icc.2 ⟨le_rfl, hs1⟩
  have := Finset.dvd_prod_of_mem (fun j => Nat.card K ^ (2 * j) - 1) h1
  simpa using this

open scoped Classical in
theorem exists_perfect_three_dvd_centralizer_psp {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3) (hq4 : 4 ≤ ℓ ^ f) (hr : 2 ≤ r)
    {a : StatedProj (StatedSp r K)} (ha : orderOf a = 3) :
    ∃ Q : Subgroup (StatedProj (StatedSp r K)),
      Q ≤ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))) ∧ ⁅Q, Q⁆ = Q ∧
        3 ∣ Nat.card Q := by
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := by omega
  obtain ⟨-, -, hinj⟩ := spProj_facts hℓ hf hK hr hrq
  have hcharK : CharP K ℓ := by
    have := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  obtain ⟨⟨x, ⟨hxa, hxo⟩, -⟩, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK
    Nat.prime_three (by norm_num) (Ne.symm hℓ3) (by omega) a ha
  have blocks0 := hblocks x hxa hxo
  subst hxa
  have blocks := blocks0
  have hcent := blocks.centralizer_eq
  have hker : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hx3).squarefree
  have hdeg : (minpoly K (spEnd x)).natDegree ≤ 3 := by
    have hdvd : minpoly K (spEnd x) ∣ (X ^ 3 - C (1 : K) : K[X]) := by
      refine minpoly.dvd K _ ?_
      have h1 : spEnd x ^ 3 = 1 := by
        have : (spLin r K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
        have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) =>
          (u : Module.End K (Fin r ⊕ Fin r → K))) this
        simpa [Units.val_pow_eq_pow_val] using h2
      simp [h1]
    have hne0 : (X ^ 3 - C (1 : K) : K[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
    have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [natDegree_X_pow_sub_C] at h4
  have hfr : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [two_mul]
  obtain ⟨h, hm⟩ := exists_primaryMultiplicity_gt (M := 1) hsq hdeg (by omega)
  by_cases h1 : (h : K[X]) = X - 1
  ·
    have hd : 2 ≤ spFixedDim x := by
      have h2 : 2 ≤ primaryMultiplicity (spEnd x) (X - 1) := by rw [← h1]; exact hm
      rw [show (X - 1 : K[X]) = X - C 1 by rw [C_1], primaryMultiplicity_X_sub_C_eq] at h2
      exact h2
    have hcard4 : 4 ≤ Nat.card K := by rw [hK]; exact hq4
    have hl : SpFixedListed x := ⟨hd, by omega⟩
    have h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := by omega
    have hqs := spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42
    have hperf : ⁅spFixedFactor x, spFixedFactor x⁆ = spFixedFactor x :=
      commutator_eq_of_isPerfect hqs.1
    have hnd : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      intro hd3
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
        (Nat.prime_three.dvd_of_dvd_pow hd3)).symm
    refine ⟨(spFixedFactor x).map (proj r K), ?_, ?_, ?_⟩
    · rw [hcent]
      exact Subgroup.map_mono (spFixedFactor_le_centralizer x)
    · rw [← Subgroup.map_commutator, hperf]
    · exact three_dvd_card_map_of_perfect (proj r K) hker hperf
        (three_dvd_card_spFixedFactor blocks hd hnd)
  ·
    have hm2 : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) := by omega
    have facts := spBlockFacts_nontrivial_three hq4 blocks h h1
    have hqs := spPull_isQuasisimple facts hm2
    obtain ⟨hle, hqm, -⟩ := spListed_facts (p := 3) Nat.prime_three
      (B := ⊤) le_top hinj hcent (spPull_le_centralizer x _) (spPull_normalized x _) hqs
    refine ⟨(spPull x (h : K[X])).map (proj r K), hle, ?_, ?_⟩
    · exact commutator_eq_of_isPerfect hqm.1
    · have := dvd_card_spBlockImage (K := K) (r := r) (by omega) Nat.prime_three (by norm_num)
        blocks h h1 hm2
      rwa [spBlockImage_eq] at this

end CFSG.HardMathSupport.Malle.E27Lie
