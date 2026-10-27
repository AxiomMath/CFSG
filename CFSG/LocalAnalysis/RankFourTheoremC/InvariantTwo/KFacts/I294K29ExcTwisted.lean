module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcFive
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Order

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.Timmesfeld.ExceptionalOrders CFSG.HardMathSupport.Timmesfeld.LinearRank Polynomial
  CFSG.RankThree.Lattice
open scoped Matrix

section Arith

variable {p q : ℕ}

theorem sq_sub_one_eq (q : ℕ) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  rcases q with _ | q
  · simp
  · simp only [Nat.add_sub_cancel]; ring_nf; omega

theorem not_dvd_sub_one_of_dvd_add_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) :
    ¬ p ∣ q - 1 := by
  intro h1
  rcases q with _ | q
  · simp at hpq; exact hp.one_lt.ne' hpq
  have h2 : p ∣ (q + 1 + 1) - (q + 1 - 1) := Nat.dvd_sub hpq h1
  rw [show (q + 1 + 1) - (q + 1 - 1) = 2 by omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem factorization_sq_sub_one (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q) (hpq : p ∣ q + 1) :
    (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
  rw [sq_sub_one_eq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_sub_one_of_dvd_add_one hp hp2 hpq), add_zero]

theorem factorization_pow_two_mul_sub_one (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q)
    (hpq : p ∣ q + 1) {k : ℕ} (hk : k ≠ 0) :
    (q ^ (2 * k) - 1).factorization p = (q + 1).factorization p + k.factorization p := by
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hpq2 : p ∣ q ^ 2 - 1 := by rw [sq_sub_one_eq]; exact Dvd.dvd.mul_right hpq _
  rw [pow_mul, factorization_pow_sub_one hp hp2 hq2 hpq2 hk,
    factorization_sq_sub_one hp hp2 hq hpq]

theorem factorization_pow_add_one_of_dvd_add_one (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q)
    (hpq : p ∣ q + 1) {n : ℕ} (hn : Odd n) :
    (q ^ n + 1).factorization p = (q + 1).factorization p + n.factorization p := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have h := factorization_pow_two_mul_sub_one hp hp2 hq hpq hn0
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hsplit : q ^ (2 * n) - 1 = (q ^ n - 1) * (q ^ n + 1) := by
    rw [mul_comm 2 n, pow_mul, sq_sub_one_eq, mul_comm]
  have hdvd : p ∣ q ^ n + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow q 1 hn
    rw [one_pow] at this
    exact hpq.trans this
  have hnd : ¬ p ∣ q ^ n - 1 := by
    intro h1
    have h2 : p ∣ (q ^ n + 1) - (q ^ n - 1) := Nat.dvd_sub hdvd h1
    rw [show (q ^ n + 1) - (q ^ n - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hq1 : q ^ n - 1 ≠ 0 := by
    intro h0
    have : q ^ n = 1 := by omega
    have : q = 1 := (Nat.pow_eq_one.1 this).resolve_right hn0
    omega
  rw [hsplit, Nat.factorization_mul hq1 (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, zero_add] at h
  exact h

theorem factorization_five_numTwistedE6 (hq : 1 < q) (hpq : 5 ∣ q + 1) :
    (CFSG.SeitzReduction.E6Pilot.numTwistedE6 q).factorization 5 =
      6 * (q + 1).factorization 5 + 1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have e2 := fun k (hk : k ≠ 0) => factorization_pow_two_mul_sub_one hp hp2 hq hpq hk
  have e1 := fun n (hn : Odd n) => factorization_pow_add_one_of_dvd_add_one hp hp2 hq hpq hn
  have h12 := e2 6 (by norm_num)
  have h8 := e2 4 (by norm_num)
  have h6 := e2 3 (by norm_num)
  have h2 := e2 1 (by norm_num)
  have h9 := e1 9 (by decide)
  have h5 := e1 5 (by decide)
  rw [show 2 * 6 = 12 from rfl] at h12
  rw [show 2 * 4 = 8 from rfl] at h8
  rw [show 2 * 3 = 6 from rfl] at h6
  rw [show 2 * 1 = 2 from rfl] at h2
  have f6 : (6 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have f4 : (4 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have f3 : (3 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have f1 : (1 : ℕ).factorization 5 = 0 := by simp
  have f9 : (9 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have f5 : (5 : ℕ).factorization 5 = 1 := hp.factorization_self
  have hq0 : q ^ 36 ≠ 0 := pow_ne_zero _ (by omega)
  have hnd : ¬ 5 ∣ q := fun h => by
    have h1 : 5 ∣ (q + 1) - q := Nat.dvd_sub hpq h
    rw [show (q + 1) - q = 1 by omega] at h1
    norm_num at h1
  have h36 : (q ^ 36).factorization 5 = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hnd, mul_zero]
  have ne : ∀ d : ℕ, d ≠ 0 → q ^ d - 1 ≠ 0 := fun d hd h => by
    have : q ^ d ≤ 1 := by omega
    have : q ^ d = 1 := le_antisymm this (Nat.one_le_pow _ _ (by omega))
    have := (Nat.pow_eq_one.1 this).resolve_right hd
    omega
  have ne' : ∀ d : ℕ, q ^ d + 1 ≠ 0 := fun d => by omega
  unfold CFSG.SeitzReduction.E6Pilot.numTwistedE6
  rw [Nat.factorization_mul (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨⟨⟨hq0, ne 12 (by norm_num)⟩, ne' 9⟩, ne 8 (by norm_num)⟩, ne 6 (by norm_num)⟩,
        ne' 5⟩) (ne 2 (by norm_num)),
    Nat.factorization_mul (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨⟨hq0, ne 12 (by norm_num)⟩, ne' 9⟩, ne 8 (by norm_num)⟩, ne 6 (by norm_num)⟩)
      (ne' 5),
    Nat.factorization_mul (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨hq0, ne 12 (by norm_num)⟩, ne' 9⟩, ne 8 (by norm_num)⟩) (ne 6 (by norm_num)),
    Nat.factorization_mul (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨hq0, ne 12 (by norm_num)⟩, ne' 9⟩) (ne 8 (by norm_num)),
    Nat.factorization_mul (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨hq0, ne 12 (by norm_num)⟩) (ne' 9),
    Nat.factorization_mul hq0 (ne 12 (by norm_num))]
  simp only [Finsupp.add_apply, h36, h12, h9, h8, h6, h5, h2, f6, f4, f3, f1, f9, f5]
  ring

end Arith

section Adjoint


theorem factorization_card_adjointGroup_of_dvd {τ : Tag} {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hker : ¬ p ∣ Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker) (ds : List ℕ)
    (hd0 : ∀ d ∈ ds, d ≠ 0)
    (hds : ∀ [Fintype (WeylGroup τ)] (x : ℕ), ∑ w : WeylGroup τ, x ^ (coxeterSystem τ).length w =
      (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod) :
    (Nat.card (adjointGroup τ K)).factorization p =
      τ.rank * (Nat.card K - 1).factorization p + (ds.map fun d => d.factorization p).sum := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hpq0 : ¬ p ∣ Nat.card K := fun h => by
    have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h hpq
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hH0 : Nat.card (torusGroup τ K) ≠ 0 := by
    have : Finite (torusGroup τ K) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have hgs : ∀ d ∈ ds, ∑ i ∈ Finset.range d, Nat.card K ^ i ≠ 0 :=
    fun d hd => geom_sum_ne_zero hq.le (hd0 d hd)
  have hP0 : (ds.map fun d => ∑ i ∈ Finset.range d, Nat.card K ^ i).prod ≠ 0 :=
    List.prod_ne_zero (fun h => by
      obtain ⟨d, hd, h0⟩ := List.mem_map.1 h
      exact hgs d hd h0)
  have hT := factorization_card_torusGroup (τ := τ) (K := K) p
  rw [Nat.factorization_eq_zero_of_not_dvd hker, add_zero] at hT
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, hds,
    Nat.factorization_mul (Nat.mul_ne_zero hH0 (pow_ne_zero _ (by omega))) hP0,
    Nat.factorization_mul hH0 (pow_ne_zero _ (by omega)), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd hpq0, mul_zero, add_zero, hT,
    factorization_list_prod _ (fun a ha => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ha
      exact hgs d hd), List.map_map]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  exact factorization_geom_sum_of_dvd_sub_one hp hp2 hq hpq (hd0 d hd)

theorem rank_twistedE6_five {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hpq : 5 ∣ ℓ ^ f + 1) :
    3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (twistedE6RootGroup K σ)) ∧
      ∀ y : twistedE6RootGroup K σ, y ^ 5 = 1 →
        3 ≤ CFSG.Open.pRank 5 (centralizer ({y} : Set (twistedE6RootGroup K σ))) := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  set q := ℓ ^ f with hqdef
  have hq : 1 < q := Nat.one_lt_pow (by omega) hℓ.one_lt
  haveI : Finite (adjointGroup Tag.E6 K) := generated_group_finite Tag.E6 K
  have hle : twistedE6RootGroup K σ ≤ adjointGroup Tag.E6 K :=
    (graphFixedRootGroup_le _ _ _).trans inf_le_left
  haveI : Finite (twistedE6RootGroup K σ) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  set ι : twistedE6RootGroup K σ →* adjointGroup Tag.E6 K := Subgroup.inclusion hle with hι
  have hιi : Function.Injective ι := Subgroup.inclusion_injective hle
  have hpq' : 5 ∣ Nat.card K - 1 := by
    rw [hK, sq_sub_one_eq]; exact Dvd.dvd.mul_right hpq _
  have hker : ¬ 5 ∣ Nat.card (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker :=
    not_dvd_of_dvd_lt card_ker_zpowMatrix_dvd_E6 (by norm_num) (by norm_num)
  have hds := fun [Fintype (WeylGroup Tag.E6)] (x : ℕ) => CFSG.RankThree.Chevalley.sum_length_E6_eq x
  have hidx : ¬ 5 ∣ ι.range.index := by
    refine not_dvd_index_of_card_eq hp _ ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hιi).toEquiv,
      factorization_card_adjointGroup_of_dvd hp hp2 hpq' hker [2, 5, 6, 8, 9, 12] (by decide) hds]
    have hC := CFSG.HardMathSupport.Lang.Coordinator.card_graphFixedRootGroup_E6_mul_gcd hℓ hf hK hσ (σ := σ.toRingHom)
    have hg : ¬ 5 ∣ Nat.gcd 3 (q + 1) := not_dvd_of_dvd_lt (Nat.gcd_dvd_left _ _) (by norm_num)
      (by norm_num)
    have hC0 : Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≠ 0 := Nat.card_pos.ne'
    have hg0 : Nat.gcd 3 (q + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
    have h1 : (Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) *
        Nat.gcd 3 (q + 1)).factorization 5 =
        (CFSG.SeitzReduction.E6Pilot.numTwistedE6 q).factorization 5 := by rw [hC]
    rw [Nat.factorization_mul hC0 hg0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hg, add_zero,
      factorization_five_numTwistedE6 hq hpq] at h1
    change _ = (Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).factorization 5
    rw [h1, hK, factorization_sq_sub_one hp hp2 hq hpq]
    have : (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => d.factorization 5).sum = 1 := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2),
        Nat.Prime.factorization_self hp,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 6),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 8),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 9),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 12)]
      rfl
    rw [this]
    rfl
  obtain ⟨A, hAR, hRN, hA, hAc⟩ := exists_torsion_torusSub hp hpq' hker
  have hRidx := not_dvd_index_monomialSub (K := K) hp hp2 hpq' [2, 5, 6, 8, 9, 12] (by decide) hds
  refine ⟨?_, fun y hy => three_le_pRank_centralizer_of_overgroup hp ι hιi hidx hAR hRN hRidx hA
    hAc (by decide) hy⟩
  have := le_pRank_of_overgroup hp ι hιi hidx hAR hRN hRidx hA hAc
  change 6 ≤ _ at this
  omega

end Adjoint

section Catalog


theorem crossAtPrime_twistedE6_five {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    CrossAtPrime ⟨.twistedE6 q, hv⟩ 5 := by
  intro hp hp5 hdp
  have hpq : (5 : ℕ) ≠ q.p := fun h =>
    hdp (h.trans (TauCeti.LieTypeIndex.characteristic_twistedE6 q).symm).symm
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hnd : ¬ 5 ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]; exact not_dvd_card_of_ne hp hpq
  rcases orderOf_five_eq hnd with h1 | h2 | h4
  · refine crossAtPrime_of_sylowTorus (fun _ _ _ => ⟨[1, 1, 1, 1, 2, 2].count 1, ?_⟩) hp hp5 hdp
    refine SylowTorus.of_mulEquiv ?_ e.symm
    have hv' : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
        toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
      rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
        Matrix.mulVec_mulVec]
    have he' := orderOf_neg_natCast_zmod hp (by norm_num) hnd h1
    rw [show ennola 1 = 2 by decide] at he'
    have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs =
        ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
      rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
        show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
    exact sylowTorus_twistedE6_of_blocks_of_three_lt q.prime_p q.exponent_pos K hK σ hσ hp
      (by norm_num) hnd _ hv' [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow
      (Or.inr (by decide)) h1 he' hΦ (by decide) (by decide) (by decide)
  · refine crossAtPrime_of_model (fun _ _ _ => ?_) hp hp5 hdp
    have hd := dvd_add_one_of_orderOf_eq_two hp h2
    obtain ⟨h3, hr⟩ := rank_twistedE6_five q.prime_p q.exponent_pos hK σ hσ hd
    exact ⟨twistedE6RootGroup K σ, inferInstance, Finite.of_injective _ Subtype.val_injective,
      ⟨e⟩, h3, hr⟩
  · refine crossAtPrime_of_sylowTorus (fun _ _ _ => ⟨2, ?_⟩) hp hp5 hdp
    exact (sylowTorus_twistedE6_four q.prime_p q.exponent_pos K hK σ hσ hp h4).of_mulEquiv e.symm

theorem crossFamTwistedE6Five_holds : CrossFamTwistedE6Five := fun _ hv =>
  crossAtPrime_twistedE6_five hv

theorem crossFamE6Five_holds : CrossFamE6Five := fun _ hv => crossAtPrime_E6_five hv

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
