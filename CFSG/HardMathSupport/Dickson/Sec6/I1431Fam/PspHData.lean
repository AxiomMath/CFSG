module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHSU
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHSp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (quasisimple_or_solvable_spSupported)
open scoped commutatorElement

theorem t6psph_hsqProp_orbit (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {r : ℕ} {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} (hq2 : 2 ≤ ℓ ^ f) (hp3 : 3 ≤ p)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsqf : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x a) {q : ℕ}
    (hq : 10 ≤ q) (h : primaryFactors (spEnd x)) :
    t6psph_HsqProp q (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hOO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hOO]
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsqf hm)
      exact t6psph_hsqProp_of_equiv _ φ (t6psph_sqOK_sesqUnitaryAlt
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate hq)
    · obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact t6psph_hsqProp_of_equiv _ φ (t6psph_sqOK_sesqUnitary hO hE hHf hHfl hq)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
    have hle := Nat.le_of_dvd (by omega) hP.dvd
    have hcard : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field]
      omega
    exact t6psph_hsqProp_of_equiv _ φ
      (t6psph_sqOK_generalLinear hO (exists_finset_card_four_of_card hcard) hq)

theorem t6psph_data_psp (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 1 ≤ r) (hpK : (3 : K) ≠ 0) {q : ℕ}
    (hq : 10 ≤ q) (a : StatedSp r K) (ha3 : a ^ 3 = 1)
    (hπa : SymplecticFlag.proj r K a ≠ 1) :
    ∃ (ι : Type) (_ : Finite ι) (N : ι → Subgroup (StatedSp r K)),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set (StatedSp r K))) ∧
      (∀ i, ∀ g ∈ Subgroup.centralizer ({a} : Set (StatedSp r K)), ∀ m ∈ N i,
        g * m * g⁻¹ ∈ N i) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set (StatedSp r K))) k,
        (g : StatedSp r K) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set (StatedSp r K)), b ^ 3 = 1 →
        ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹) := by
  classical
  have ha1 : a ≠ 1 := fun h => hπa (by rw [h, map_one])
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hπo : orderOf (SymplecticFlag.proj r K a) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, ha3, map_one]) hπa
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hE⟩ := FiniteField.card K (ringChar K)
  have hKcard : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hE]
  have hpℓ : (3 : ℕ) ≠ ringChar K := by
    intro h
    apply hpK
    have h0 := CharP.cast_eq_zero K (ringChar K)
    rw [← h] at h0
    exact_mod_cast h0
  have hq2 : 2 ≤ ringChar K ^ (f : ℕ) :=
    hℓ.two_le.trans (Nat.le_self_pow f.pos.ne' _)
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓ f.pos hKcard
    Nat.prime_three (by norm_num) hpℓ hr (SymplecticFlag.proj r K a) hπo).2 a rfl hao
  have hpK' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast hpK
  have hsqf := (altPrimaryData_spLin hpK' ha3).squarefree
  haveI : Finite (reciprocalOrbits (spEnd a)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  refine lift_blocks_of_orbit_family_sq q a
    (fun O : reciprocalOrbits (spEnd a) => spSupported a (O : Set K[X]))
    (fun i j hij x hx y hy => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx y hy)
    hjoin (fun O => quasisimple_or_solvable_spSupported le_rfl hq2 hsqf blocks O) ?_
  rintro ⟨O, h, hh, rfl⟩
  exact t6psph_hsqProp_orbit hO hq2 le_rfl hsqf blocks hq ⟨h, Finset.mem_coe.mp hh⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431
