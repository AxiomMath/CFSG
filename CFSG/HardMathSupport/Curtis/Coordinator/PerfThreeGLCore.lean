module

public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm Matrix

section Field

variable {K : Type} [Field K]

theorem eq_zero_or_eq_one_of_card_eq_two [Finite K] (hK : Nat.card K = 2) :
    ∀ r : K, r = 0 ∨ r = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  intro r
  have h := Finset.eq_univ_of_card _ hc
  have hr' : r ∈ ({0, 1} : Finset K) := h ▸ Finset.mem_univ r
  simpa using hr'

theorem two_eq_zero_of_card_eq_two [Finite K] (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have := card_nsmul_eq_zero (G := K) (x := 1)
  rw [Nat.card_eq_fintype_card] at hK
  rw [hK] at this
  simpa using this

theorem irreducible_X_sq_add_X_add_one_of_card_eq_two [Finite K] (hK : Nat.card K = 2) :
    Irreducible (X ^ 2 + X + 1 : K[X]) := by
  have h2 := two_eq_zero_of_card_eq_two hK
  have hmon : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by
    compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hmon]; simp) fun c hc => ?_
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hc
  rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
  · simp at hc
  · have : (1 : K) + 1 + 1 = 0 := by simpa using hc
    have h3 : (1 : K) + 1 + 1 = 1 := by
      have : (1 : K) + 1 = 2 := by norm_num
      rw [this, h2, zero_add]
    rw [h3] at this
    exact one_ne_zero this

theorem eq_X_sub_one_or_eq_quad_of_dvd [Finite K] (hK : Nat.card K = 2) {b : K[X]}
    (hb : Irreducible b)
    (hm : b.Monic) (hd : b ∣ X ^ 3 - C 1) : b = X - C 1 ∨ b = X ^ 2 + X + 1 := by
  have hfac : (X ^ 3 - C 1 : K[X]) = (X - C 1) * (X ^ 2 + X + 1) := by
    simp only [map_one]; ring
  rw [hfac] at hd
  rcases hb.prime.dvd_or_dvd hd with h | h
  · left
    exact eq_of_monic_of_associated hm (monic_X_sub_C 1)
      (hb.associated_of_dvd (irreducible_X_sub_C 1) h)
  · right
    exact eq_of_monic_of_associated hm (by monicity!)
      (hb.associated_of_dvd (irreducible_X_sq_add_X_add_one_of_card_eq_two hK) h)


theorem natCard_adjoinRoot_of_card_eq_two [Finite K] (hK : Nat.card K = 2) {b : K[X]}
    (hb : Irreducible b) :
    Nat.card (AdjoinRoot b) = 2 ^ b.natDegree := by
  have : Fact (Irreducible b) := ⟨hb⟩
  have hfin : Module.Finite K (AdjoinRoot b) := (AdjoinRoot.powerBasis hb.ne_zero).finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot b), hK,
    (AdjoinRoot.powerBasis hb.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

theorem exists_good_primaryFactor [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn : 5 ≤ n)
    {x : Module.End K (Fin n → K)} (hx : Squarefree (minpoly K x))
    (hx3 : aeval x (X ^ 3 - C 1 : K[X]) = 0) :
    ∃ b : primaryFactors x, 2 ≤ mult x b ∧
      (3 ≤ mult x b ∨ ∃ s : Finset (Efac x b), s.card = 4) := by
  classical
  by_contra hcon
  push Not at hcon
  have hdvd : minpoly K x ∣ X ^ 3 - C 1 := minpoly.dvd K x hx3
  have hcls : ∀ b : primaryFactors x, (b : K[X]) = X - C 1 ∨ (b : K[X]) = X ^ 2 + X + 1 := by
    intro b
    obtain ⟨hirr, hmon, hbd⟩ := mem_primaryFactors.mp b.2
    exact eq_X_sub_one_or_eq_quad_of_dvd hK hirr hmon (hbd.trans hdvd)
  have hterm : ∀ b : primaryFactors x, (b : K[X]).natDegree * mult x b ≤ 2 := by
    intro b
    have hirr : Irreducible (b : K[X]) := irreducible_of_mem_primaryFactors b.2
    have hE : Nat.card (Efac x b) = 2 ^ (b : K[X]).natDegree :=
      natCard_adjoinRoot_of_card_eq_two hK hirr
    rcases hcls b with h | h
    · have hd : (b : K[X]).natDegree = 1 := by rw [h]; exact natDegree_X_sub_C 1
      rw [hd] at hE ⊢
      have hno : ¬ ∃ s : Finset (Efac x b), s.card = 4 := by
        rintro ⟨s, hs⟩
        have : Finite (Efac x b) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
        have := Fintype.ofFinite (Efac x b)
        have h1 : s.card ≤ Fintype.card (Efac x b) := Finset.card_le_univ s
        rw [← Nat.card_eq_fintype_card, hE] at h1
        omega
      by_contra hlt
      have h3 : 3 ≤ mult x b := by omega
      exact absurd (hcon b (by omega)).1 (not_lt.mpr h3)
    · have hd : (b : K[X]).natDegree = 2 := by
        rw [h]; compute_degree!
      rw [hd] at hE ⊢
      have hyes : ∃ s : Finset (Efac x b), s.card = 4 := by
        have : Finite (Efac x b) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
        have := Fintype.ofFinite (Efac x b)
        exact ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hE]; norm_num⟩
      by_contra hlt
      have h2 : 2 ≤ mult x b := by omega
      obtain ⟨hm3, hs⟩ := hcon b h2
      obtain ⟨s, hs4⟩ := hyes
      exact hs s hs4
  have hcard : (primaryFactors x).card ≤ 2 := by
    have hsub : primaryFactors x ⊆ ({X - C 1, X ^ 2 + X + 1} : Finset K[X]) := by
      intro b hb
      rcases hcls ⟨b, hb⟩ with h | h
      · have h' : b = X - C 1 := h
        simp [h']
      · have h' : b = X ^ 2 + X + 1 := h
        simp [h']
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  rw [Module.finrank_fin_fun] at hsum
  have : n ≤ 4 := by
    rw [hsum]
    calc ∑ a : primaryFactors x, (a : K[X]).natDegree * primaryMultiplicity x (a : K[X])
        ≤ ∑ _a : primaryFactors x, 2 := Finset.sum_le_sum fun b _ => hterm b
      _ = 2 * (primaryFactors x).card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]
      _ ≤ 4 := by omega
  omega


theorem three_dvd_card_special_linear_adjoinRoot [Finite K] (hK : Nat.card K = 2) {b : K[X]}
    (hb : Irreducible b)
    {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (SpecialLinearGroup (Fin m) (AdjoinRoot b)) := by
  have : Fact (Irreducible b) := ⟨hb⟩
  have hfin : Module.Finite K (AdjoinRoot b) := (AdjoinRoot.powerBasis hb.ne_zero).finite
  have : Finite (AdjoinRoot b) := Module.finite_of_finite K
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega),
    natCard_adjoinRoot_of_card_eq_two hK hb]
  refine Dvd.dvd.mul_left ?_ _
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hm⟩))
  rw [← pow_mul, mul_comm, pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 b.natDegree

theorem exists_perfect_three_dvd_centralizer_gl_two [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 5 ≤ n)
    (a : GL (Fin n) K) (ha : a ^ 3 = 1) :
    ∃ P : Subgroup (GL (Fin n) K), P ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  classical
  set x : Module.End K (Fin n → K) := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) with hxdef
  have h2 := two_eq_zero_of_card_eq_two hK
  have h3 : ((3 : ℕ) : K) ≠ 0 := by
    have : ((3 : ℕ) : K) = 1 := by
      have : ((3 : ℕ) : K) = 2 + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [this]
    exact one_ne_zero
  have hx3 : aeval x (X ^ 3 - C 1 : K[X]) = 0 := by
    have hX : x = Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
      (toLinAlgEquiv'_eq_toLin' _).symm
    have hM : (a : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
    rw [hX]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [← map_pow, hM]
    simp
  have hx : Squarefree (minpoly K x) :=
    squarefree_minpoly_of_aeval_eq_zero
      (separable_X_pow_sub_C (1 : K) h3 one_ne_zero).squarefree hx3
  obtain ⟨b, hb2, hb3⟩ := exists_good_primaryFactor hK hn hx hx3
  have hirr : Irreducible (b : K[X]) := irreducible_of_mem_primaryFactors b.2
  refine ⟨blockImage hx b, ?_, ?_, ?_⟩
  · refine (blockImage_le_range hx b).trans (le_of_eq ?_)
    exact range_commutantUnitsToGL_eq_centralizer a rfl
  · have hq : CFSG.IsQuasisimple (blockImage hx b) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx))
        (isQuasisimple_blockSL b hb2 hb3)
    exact Subgroup.isPerfect_iff.1 hq.1
  · have e : ↥(blockImage hx b) ≃* SpecialLinearGroup (Fin (mult x b)) (Efac x b) :=
      ((Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx)).symm).trans
        (MonoidHom.ofInjective (blockEmbed_injective b)).symm
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_special_linear_adjoinRoot hK hirr hb2

end Field

end CFSG.HardMathSupport.Curtis.Coordinator
