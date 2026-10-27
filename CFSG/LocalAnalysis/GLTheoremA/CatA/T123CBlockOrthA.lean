module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonal

section Regular

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

private theorem finite_orthogonalGroup (Q : QuadraticForm K W) :
    Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W)) DFunLike.coe_injective
  infer_instance

theorem isSolvable_orthogonalGroup_of_card_two_of_plus (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 2) (h4 : finrank K W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 1)
    (by rw [h4]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [hK] at hc
  have h72 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ 3 * 3 ^ 2 := by
    have h1 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 72 := by
      rw [hc]
      decide
    exact_mod_cast h1
  have := finite_orthogonalGroup Q
  letI := Fintype.ofFinite ↥(TauCeti.QuadraticMap.orthogonalGroup Q)
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h72])

theorem four_le_finrank_of_not_isSolvable (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) : 4 ≤ finrank K W := by
  by_contra h
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  exact hns (CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
    hQ (by omega))

theorem not_smallFixedException_of_not_isSolvable (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ¬ SmallFixedException Q := by
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    have h2 : (2 : ℕ) ∣ Nat.card K := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self 2 n.ne_zero
    omega
  rintro (⟨-, h3⟩ | ⟨⟨h4, S, hS2, hSQ⟩, h2 | h3⟩)
  · exact hK3 h3
  · exact hns (isSolvable_orthogonalGroup_of_card_two_of_plus Q hQ h2 h4
      ⟨S, by rw [hS2, h4], hSQ⟩)
  · exact hK3 h3

theorem mem_orthDerived_of_pow_prime_of_not_isSolvable (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {g : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgp : g ^ p = 1) : g ∈ orthDerived Q := by
  have h4 := four_le_finrank_of_not_isSolvable Q hQ hns
  have hodd : Odd (orderOf g) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hgp)
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases hK4 : 4 ≤ Nat.card K
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_mem_orthDerived_of_pow_prime Q hQ
      (by omega) hK4 hp hp2 hg hgp
  have hK : Nat.card K = 2 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hcard] at hK4 ⊢
    have hn1 : (n : ℕ) = 1 := by
      by_contra hne
      have h2 : 2 ≤ (n : ℕ) := by have := n.pos; omega
      exact hK4 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h2))
    rw [hn1, pow_one]
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  by_cases h6 : 6 ≤ finrank K W
  · exact (CFSG.AGLEmbedding.ToralCensus.perfect_and_odd_orthDerived_of_card_two hK hQ h6).2 g
      hg hodd
  have hdim : finrank K W = 4 := by omega
  have hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hns (isSolvable_orthogonalGroup_of_card_two_of_plus Q hQ hK hdim
      ⟨U, by rw [hU, hdim], hcon⟩)
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hder, -, -, -, -, -, -, hodd'⟩ :=
    even_minus_four_actual_derived_extraction Q hQ hdim hts
  have hmem := hodd' g hg hodd
  rw [← hder] at hmem
  exact hmem

theorem dvd_card_orthDerived_of_not_isSolvable (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card K + 1) : p ∣ Nat.card ↥(orthDerived Q) := by
  classical
  haveI := Fact.mk hp
  have h4 := four_le_finrank_of_not_isSolvable Q hQ hns
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + 1 := ⟨k - 2, by omega⟩
  have hdim : finrank K W = 2 * (m + 1 + 1) := by omega
  have hO : p ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
    have hpZ : (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 2) ^ 1 - 1 := by
      have h1 : ((Nat.card K : ℤ) ^ 2) ^ 1 - 1 = ((Nat.card K + 1 : ℕ) : ℤ) * (Nat.card K - 1) := by
        push_cast
        ring
      rw [h1]
      exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hdvd) _
    have hprod : (p : ℤ) ∣ ∏ i ∈ Finset.Icc 1 (m + 1), (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
      hpZ.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim (ε := 1)
        (Or.inl ⟨rfl, hplus⟩)
      exact Int.natCast_dvd_natCast.mp (hc ▸ Dvd.dvd.mul_left hprod _)
    · have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim (ε := -1)
        (Or.inr ⟨rfl, hplus⟩)
      exact Int.natCast_dvd_natCast.mp (hc ▸ Dvd.dvd.mul_left hprod _)
  have := finite_orthogonalGroup Q
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hO
  have hgp : (g : W ≃ₗ[K] W) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
  have hgΩ := mem_orthDerived_of_pow_prime_of_not_isSolvable Q hQ hns hp hp2 g.2 hgp
  have hord : orderOf (⟨g, hgΩ⟩ : ↥(orthDerived Q)) = p := by
    rw [← Subgroup.orderOf_coe, ← hg, ← Subgroup.orderOf_coe]
  have : Finite ↥(orthDerived Q) := by
    have : Finite W := Module.finite_of_finite K
    have : Finite (W ≃ₗ[K] W) :=
      Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W)) DFunLike.coe_injective
    infer_instance
  rw [← hord]
  exact orderOf_dvd_natCard _

end Regular

section Block

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
private theorem eq_two_of_card_eq_pow (K : Type) [Field K] [Finite K] [CharP K 2] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ f) : ℓ = 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard] at hK
  have h2 : 2 ∣ ℓ ^ f := hK ▸ dvd_pow_self 2 n.ne_zero
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem isQuasisimple_specialBlock_of_good (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm2 : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hm4 : Nat.card (AdjoinRoot h) = 4 → 4 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  obtain ⟨d, ℓ, f, hU, B, -, hq, hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx hp2 hh hne1 hself
  obtain rfl : ℓ = 2 := eq_two_of_card_eq_pow K hU.prime hq
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
  have hmr : primaryMultiplicity x.toLinearMap h =
      finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := rfl
  have hfd : 1 ≤ f * d := hU.one_le
  rcases (show f * d = 1 ∨ 2 ≤ f * d by omega) with h1 | h2
  · have hE4 : Nat.card (AdjoinRoot h) = 4 := by rw [hU.card, h1]; norm_num
    have hm := hm4 hE4
    exact isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl (by omega)
      fun e => by
        have := congrArg Prod.fst e
        simp only at this
        omega
  · have hq4 : 4 ≤ 2 ^ (f * d) := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h2)
    rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with h3 | h3
    · exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hU hBsymm hBl
        (by omega) hq4
    · exact isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl h3 fun e => by
        have := congrArg Prod.snd e
        simp only at this
        omega

theorem isSolvable_supportedBlock_of_bad (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hbad : primaryMultiplicity x.toLinearMap h ≤ 1 ∨
      (Nat.card (AdjoinRoot h) = 4 ∧ primaryMultiplicity x.toLinearMap h ≤ 3)) :
    Group.IsSolvable ↥(supportedBlock Q x h) := by
  classical
  have hne := primaryComponent_ne_bot hx.squarefree_minpoly hh
  haveI : Nontrivial ↥(primaryComponent x.toLinearMap h) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  have hm1 : 0 < primaryMultiplicity x.toLinearMap h := Module.finrank_pos
  have hS : Group.IsSolvable ↥(specialBlock Q x h) := by
    by_cases hm : primaryMultiplicity x.toLinearMap h = 1
    · rw [hx.specialBlock_eq_bot_of_finrank_eq_one hh hm]
      infer_instance
    obtain ⟨hE4, hm3⟩ : Nat.card (AdjoinRoot h) = 4 ∧ primaryMultiplicity x.toLinearMap h ≤ 3 :=
      hbad.resolve_left (by omega)
    obtain ⟨d, ℓ, f, hU, B, -, hq, hBsymm, hBl, hrange⟩ :=
      orth2_exists_unitary_model hx hp2 hh hne1 hself
    obtain rfl : ℓ = 2 := eq_two_of_card_eq_pow K hU.prime hq
    have hfd : f * d = 1 := by
      have h1 := hU.card
      rw [hE4] at h1
      have h2 : (2 : ℕ) ^ 2 = 2 ^ (2 * (f * d)) := by rw [← h1]; norm_num
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
      (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
        (MulEquiv.subgroupCongr hrange)
    obtain ⟨-, hSU, -⟩ := CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
      (n := primaryMultiplicity x.toLinearMap h) rfl hm1
    have hq2 : ((2 ^ (f * d) : ℕ) : ℤ) = 2 := by rw [hfd]; norm_num
    rw [hq2] at hSU
    have hcard : ∃ a b : ℕ, Nat.card ↥(specialBlock Q x h) = 2 ^ a * 3 ^ b := by
      rw [Nat.card_congr e₁.toEquiv]
      rcases (show primaryMultiplicity x.toLinearMap h = 2 ∨
          primaryMultiplicity x.toLinearMap h = 3 by omega) with h2 | h3
      · rw [h2] at hSU
        refine ⟨1, 1, ?_⟩
        have : (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) = 6 := by
          rw [hSU]
          decide
        exact_mod_cast this
      · rw [h3] at hSU
        refine ⟨3, 3, ?_⟩
        have : (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) = 216 := by
          rw [hSU]
          decide
        exact_mod_cast this
    obtain ⟨a, b, hab⟩ := hcard
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) :=
      Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
    letI := Fintype.ofFinite ↥(specialBlock Q x h)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hab])
  let ι : ↥(specialBlock Q x h) →* ↥(supportedBlock Q x h) :=
    Subgroup.inclusion (specialBlock_le_supportedBlock h)
  refine Group.isSolvable_of_ker_le_range ι (blockDet Q x h).toHomUnits fun g hg => ?_
  have hg1 : blockDet Q x h g = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  exact ⟨⟨g.1, mem_specialBlock.mpr ⟨g.2, hg1⟩⟩, rfl⟩

private theorem card_sup_dvd_of_commute {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.card ↥(A ⊔ B) ∣ Nat.card A * Nat.card B := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hAB a a.2 b b.2
  have hr : (MonoidHom.noncommCoprod A.subtype B.subtype hc).range = A ⊔ B := by
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype hc
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
  rw [← hr, ← Nat.card_prod]
  exact Subgroup.card_range_dvd _

theorem exists_fixed_factor_dvd_card (hx : OddOrderIsometry Q p x) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card K + 1)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))) :
    ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧ F ≤ supportedFixedDerived Q x ∧
      (F.subgroupOf (supportedFixedDerived Q x)).Normal ∧ r ∣ Nat.card ↥F := by
  have hQ0 := hx.polarBilin_fixed_nondegenerate
  have h4 := four_le_finrank_of_not_isSolvable _ hQ0 hns
  have hnexc := not_smallFixedException_of_not_isSolvable _ hQ0 hns
  have hcov := (orthogonal_regular_space_coverage _ hQ0 (by omega)).2 hnexc
  obtain ⟨n, F, hn1, hn2, hsup, hF, hcomm, -⟩ := hx.exists_supported_factors hcov
  have hdS : r ∣ Nat.card ↥(supportedFixedDerived Q x) := by
    rw [Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv]
    exact dvd_card_orthDerived_of_not_isSolvable _ hQ0 hns hr hr2 hdvd
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨i, hi⟩ : ∃ i, r ∣ Nat.card ↥(F i) := by
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · refine ⟨0, ?_⟩
      have h : (⨆ i, F i) = F 0 := by
        refine le_antisymm (iSup_le fun i => ?_) (le_iSup F 0)
        rw [Subsingleton.elim i 0]
      rwa [← hsup, h] at hdS
    · have h : (⨆ i, F i) = F 0 ⊔ F 1 := by
        refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup F 0) (le_iSup F 1))
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      rw [← hsup, h] at hdS
      rcases (Nat.Prime.dvd_mul hr).mp
          (hdS.trans (card_sup_dvd_of_commute (hcomm 0 1 (by decide)))) with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
  exact ⟨F i, (hF i).1, (hF i).2.1, (hF i).2.2, hi⟩

end Block

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
