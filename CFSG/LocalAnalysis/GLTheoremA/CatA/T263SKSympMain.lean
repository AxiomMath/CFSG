module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKSympBlk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Polynomial Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement

theorem sk_four_le_selfDual {f d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ 2 ^ f)
    (hpd : p ∣ (2 ^ f) ^ d + 1) : 4 ≤ 2 ^ (f * d) := by
  rw [← pow_mul] at hpd
  by_contra hlt
  push Not at hlt
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hfd : f * d ≤ 1 := by
    by_contra h2
    push Not at h2
    have : 2 ^ 2 ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hQ2 : 2 ^ (f * d) ≤ 2 :=
    calc 2 ^ (f * d) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hfd
      _ = 2 := by norm_num
  have hle : p ≤ 2 ^ (f * d) + 1 := Nat.le_of_dvd (by positivity) hpd
  have hp3' : p = 3 := by omega
  have hfd1 : f * d = 1 := by
    rcases (show f * d = 0 ∨ f * d = 1 by omega) with h0 | h1
    · rw [h0, pow_zero] at hle
      omega
    · exact h1
  have hf1 : f ≤ 1 := Nat.le_of_dvd one_pos ⟨d, hfd1.symm⟩
  have h4 := hK3 hp3'
  have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hf1
  omega

theorem sk_four_le_of_dvd_sub_one {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 2 ≤ N) (hpd : p ∣ N - 1) :
    4 ≤ N := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have := Nat.le_of_dvd (by omega) hpd
  omega

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sk_goodOrBad_factor {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hK3 : p = 3 → 4 ≤ Nat.card K) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 f p x a)
    (h : primaryFactors (spEnd x)) :
    SkGood p ↥(spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) ∨
      SkBad p ↥(spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  classical
  have hK3' : p = 3 → 4 ≤ 2 ^ f := fun h3 => hK ▸ hK3 h3
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO]
    by_cases h1 : (h : K[X]) = X - 1
    ·
      obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      rcases sk_goodOrBad_alt (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate hp hp2 hK3 with hg | hb
      · exact Or.inl (skGood_of_mulEquiv φ hg)
      · exact Or.inr (skBad_of_mulEquiv φ hb)
    ·
      obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      have hQ : 4 ≤ 2 ^ (f * d) := sk_four_le_selfDual hp hp2 hK3' hpd
      have hpQ : p ∣ 2 ^ (f * d) + 1 := by rwa [pow_mul]
      by_cases hm : 2 ≤ finrank (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))
      · exact Or.inl (skGood_of_mulEquiv φ (skGood_GU hE hHf hHfl hm hQ hp hpQ))
      · exact Or.inr (skBad_of_mulEquiv φ (skBad_GU_of_le_one hE (by omega) p))
  ·
    have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    have hdeg : 0 < (h : K[X]).natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hq2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    have hN : 2 ≤ (2 ^ f) ^ (h : K[X]).natDegree := hq2.trans (Nat.le_self_pow (by omega) _)
    have hpq : p ∣ Nat.card (AdjoinRoot (h : K[X])) - 1 := by
      rw [hP.card_field]
      exact hP.dvd
    have h4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field]
      exact sk_four_le_of_dvd_sub_one hp hp2 hN hP.dvd
    haveI : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
    haveI : CharP (AdjoinRoot (h : K[X])) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (h : K[X]))).injective 2
    by_cases hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])
    · exact Or.inl (skGood_of_mulEquiv φ (skGood_GL hm h4 hp hpq))
    · exact Or.inr (skBad_of_mulEquiv φ (skBad_GL_of_le_one (by omega) p))

theorem sk_goodOrBad_orbit {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hK3 : p = 3 → 4 ≤ Nat.card K) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 f p x a)
    (O : reciprocalOrbits (spEnd x)) :
    SkGood p ↥(spSupported x (O : Set K[X])) ∨ SkBad p ↥(spSupported x (O : Set K[X])) := by
  obtain ⟨O, h, hh, rfl⟩ := O
  exact sk_goodOrBad_factor hp hp2 hf hK hK3 hsq blocks ⟨h, hh⟩

theorem famSel_symplectic (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ Nat.card K) :
    SD.FamSel p ↥(StatedSp r K)
      (fun φ => φ ∈ Set.range (MulAut.conj : ↥(StatedSp r K) →* MulAut ↥(StatedSp r K))) := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  refine SD.sdo_famSel_of_elements p sk_center_statedSp ?_
  intro g hgp hg1 B hB Y hYc hY2 hYB hne
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have ha : orderOf (SymplecticFlag.proj r K g) = p := by
    rw [orderOf_injective (SymplecticFlag.proj r K) UnitaryHigher.proj_bijective_of_charTwo.1 g, hord]
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK hp hp2 hp2 hr _
    ha).2 g rfl hord
  have hsq := (altPrimaryData_spLin hpK hgp).squarefree
  haveI : Finite (reciprocalOrbits (spEnd g)) := (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, hind, hjoin⟩ := blocks.directProduct
  have hY2' : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k = 1 := fun y hy => by
    obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  exact sk_select_of_blocks hp hp2 (fun O : reciprocalOrbits (spEnd g) => spSupported g (O : Set K[X]))
    (fun i j hij u hu v hv => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) u hu v hv) hind
    (Subgroup.centralizer {g}) hjoin (fun O => sk_goodOrBad_orbit hp hp2 hf hK hK3 hsq blocks O) B Y
    (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB b hb).2) hYc (fun b hb => (hB b hb).1) hY2' hYB hne

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
