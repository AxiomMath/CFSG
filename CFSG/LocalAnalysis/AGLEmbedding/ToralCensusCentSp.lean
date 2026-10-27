module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpBlocks
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {f r : ℕ} {K : Type} [Field K]

theorem proj_injective_of_charTwo [CharP K 2] (hr : 1 ≤ r) : Function.Injective (proj r K) := by
  rw [← MonoidHom.ker_eq_bot_iff, SymplecticFlag.proj, QuotientGroup.ker_mk']
  exact CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp hr

variable {x : StatedSp r K} {a : StatedProj (StatedSp r K)}

theorem spSupported_le_centralizer (O : Set K[X]) :
    spSupported x O ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_spSupported.mp hg).1

theorem dvd_of_mem_primaryFactors (hx3 : x ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x)) : h ∣ X ^ 3 - C 1 :=
  (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K _ (by simp [spEnd_pow hx3]))

theorem X_sub_one_mem_of_finrank_pos
    (hd : 0 < finrank K (primaryComponent (spEnd x) (X - 1))) :
    (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
  by_contra hX
  rw [primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one hX,
    finrank_bot] at hd
  exact lt_irrefl 0 hd

variable [Finite K]

theorem perfectNoncycThreeIn_spFixed [CharP K 2] (HB : SpPrimaryBlocks 2 f 3 x a)
    (hd : 4 ≤ finrank K (primaryComponent (spEnd x) (X - 1))) :
    PerfectNoncycThreeIn (spSupported x {X - 1}) := by
  obtain ⟨φ, -⟩ := HB.fixedFactor (X_sub_one_mem_of_finrank_pos (by omega))
  have halt : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  refine ((perfectNoncycThreeIn_sesqUnitary_alt halt HB.fixed_nondegenerate hd).map
    ((spSupported x {X - 1}).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm g).2

theorem perfectThreeIn_spFixed [CharP K 2] (HB : SpPrimaryBlocks 2 f 3 x a)
    (hd : 2 ≤ finrank K (primaryComponent (spEnd x) (X - 1))) (hK : 4 ≤ Nat.card K) :
    PerfectThreeIn (spSupported x {X - 1}) := by
  obtain ⟨φ, -⟩ := HB.fixedFactor (X_sub_one_mem_of_finrank_pos (by omega))
  have halt : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  refine ((perfectThreeIn_sesqUnitary_alt halt HB.fixed_nondegenerate hd hK).map
    ((spSupported x {X - 1}).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm g).2

omit [Finite K] in
theorem perfectNoncycThreeIn_spPaired (HB : SpPrimaryBlocks 2 f 3 x a)
    (h : primaryFactors (spEnd x)) (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    (hX : (h : K[X]) ≠ X - 1) (hm : 3 ≤ primaryMultiplicity (spEnd x) h) :
    PerfectNoncycThreeIn (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  obtain ⟨φ⟩ := (HB.paired h hne).matrixFactor
  have : Finite (AdjoinRoot (h : K[X])) :=
    Nat.finite_of_card_ne_zero (by rw [(HB.paired h hne).card_field]; positivity)
  refine ((perfectNoncycThreeIn_gl hm (HB.nontrivial h h.2 hX)).map
    ((spSupported x _).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm g).2

omit [Finite K] in
theorem perfectThreeIn_spPaired (HB : SpPrimaryBlocks 2 f 3 x a) (hf : 2 ≤ f)
    (h : primaryFactors (spEnd x)) (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    (hX : (h : K[X]) ≠ X - 1) (hm : 2 ≤ primaryMultiplicity (spEnd x) h) :
    PerfectThreeIn (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  obtain ⟨φ⟩ := (HB.paired h hne).matrixFactor
  have hcard := (HB.paired h hne).card_field
  have : Finite (AdjoinRoot (h : K[X])) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hdeg := (irreducible_of_mem_primaryFactors h.2).natDegree_pos
  have h4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ (h : K[X]).natDegree :=
        Nat.pow_le_pow_right (by positivity) hdeg
  refine ((perfectThreeIn_gl hm h4 (HB.nontrivial h h.2 hX)).map
    ((spSupported x _).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm g).2

omit [Finite K] in
theorem perfectNoncycThreeIn_spSelfDual (HB : SpPrimaryBlocks 2 f 3 x a)
    (h : primaryFactors (spEnd x)) (hX : (h : K[X]) ≠ X - 1)
    (hself : reciprocalPolynomial (h : K[X]) = h) (hdeg : (h : K[X]).natDegree ≤ 2)
    (hm : 3 ≤ primaryMultiplicity (spEnd x) h)
    (hq : primaryMultiplicity (spEnd x) h = 3 → 2 ≤ f) :
    PerfectNoncycThreeIn (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  obtain ⟨d, hd, -, σ, -, -, -, hσ, -, hE, hbar, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, -⟩ :=
    (HB.selfDual h hX hself).exists_half
  have hpos := (irreducible_of_mem_primaryFactors h.2).natDegree_pos
  have hd1 : d = 1 := by omega
  subst hd1
  have : Finite (AdjoinRoot (h : K[X])) := hE.finite
  rw [hself, Set.pair_eq_singleton]
  refine ((perfectNoncycThreeIn_sesqUnitary hHf hHfl e he hm (fun h3 => ?_)
    (HB.nontrivial h h.2 hX) ((hbar _).trans hσ)).map
    ((spSupported x _).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  · rw [mul_one]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (hq h3)
  · rintro _ ⟨g, -, rfl⟩
    exact (φ.symm g).2

omit [Finite K] in
theorem perfectThreeIn_spSelfDual (HB : SpPrimaryBlocks 2 f 3 x a) (hf : 2 ≤ f)
    (h : primaryFactors (spEnd x)) (hX : (h : K[X]) ≠ X - 1)
    (hself : reciprocalPolynomial (h : K[X]) = h) (hdeg : (h : K[X]).natDegree ≤ 2)
    (hm : 2 ≤ primaryMultiplicity (spEnd x) h) :
    PerfectThreeIn (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  obtain ⟨d, hd, -, σ, -, -, -, hσ, -, hE, hbar, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, -⟩ :=
    (HB.selfDual h hX hself).exists_half
  have hpos := (irreducible_of_mem_primaryFactors h.2).natDegree_pos
  have hd1 : d = 1 := by omega
  subst hd1
  rw [hself, Set.pair_eq_singleton]
  refine ((perfectThreeIn_sesqUnitary hHf hHfl e he hm ?_ (HB.nontrivial h h.2 hX)
    ((hbar _).trans hσ)).map ((spSupported x _).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  · rw [mul_one]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · rintro _ ⟨g, -, rfl⟩
    exact (φ.symm g).2

end CFSG.AGLEmbedding.ToralCensus
