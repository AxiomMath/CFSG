module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.HardMathSupport.Timmesfeld.LinearRank

section Arith

variable {p q : ℕ}

theorem geom_sum_mul_sub_one (hq : 1 ≤ q) (d : ℕ) :
    (∑ i ∈ Finset.range d, q ^ i) * (q - 1) = q ^ d - 1 :=
  geom_sum_mul_of_one_le hq d

theorem geom_sum_ne_zero (hq : 1 ≤ q) {d : ℕ} (hd : d ≠ 0) : ∑ i ∈ Finset.range d, q ^ i ≠ 0 := by
  intro h
  have : 0 ∈ Finset.range d := Finset.mem_range.2 (Nat.pos_of_ne_zero hd)
  have h1 := Finset.sum_eq_zero_iff.1 h 0 this
  simp at h1

theorem factorization_geom_sum_of_dvd_sub_one (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q)
    (hpq : p ∣ q - 1) {d : ℕ} (hd : d ≠ 0) :
    (∑ i ∈ Finset.range d, q ^ i).factorization p = d.factorization p := by
  have h := factorization_pow_sub_one hp hp2 hq hpq hd
  rw [← geom_sum_mul_sub_one hq.le d, Nat.factorization_mul (geom_sum_ne_zero hq.le hd)
    (by omega), Finsupp.add_apply] at h
  omega

theorem factorization_geom_sum_of_dvd_add_one (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q)
    (hpq : p ∣ q + 1) {d : ℕ} (hd : d ≠ 0) (hde : 2 ∣ d) :
    (∑ i ∈ Finset.range d, q ^ i).factorization p = (q + 1).factorization p + d.factorization p := by
  obtain ⟨k, rfl⟩ := hde
  have hk : k ≠ 0 := by omega
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hpq2 : p ∣ q ^ 2 - 1 := by
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      rcases q with _ | q
      · omega
      · simp only [Nat.add_sub_cancel]; ring_nf; omega
    rw [this]
    exact Dvd.dvd.mul_right hpq _
  have h := factorization_pow_sub_one hp hp2 hq2 hpq2 hk
  rw [← pow_mul] at h
  have hpq1 : ¬ p ∣ q - 1 := by
    intro h1
    have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq h1
    have : (q + 1) - (q - 1) = 2 := by omega
    rw [this] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hq1 : (q - 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpq1
  have hsq : (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      rcases q with _ | q
      · omega
      · simp only [Nat.add_sub_cancel]; ring_nf; omega
    rw [this, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, hq1, add_zero]
  have hg := geom_sum_mul_sub_one hq.le (2 * k)
  rw [← hg, Nat.factorization_mul (geom_sum_ne_zero hq.le (by omega)) (by omega),
    Finsupp.add_apply, hq1, add_zero, hsq] at h
  rw [h, Nat.factorization_mul (by norm_num) hk, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => hp2
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)), zero_add]

theorem factorization_list_prod (l : List ℕ) (h : ∀ a ∈ l, a ≠ 0) :
    l.prod.factorization p = (l.map fun a => a.factorization p).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      Nat.factorization_mul (h a (by simp)) (List.prod_ne_zero (fun h0 => h 0 (by simp [h0]) rfl)),
      Finsupp.add_apply, ih fun b hb => h b (by simp [hb])]

end Arith

section Card


variable {τ : Tag} {K : Type} [Field K]

theorem card_monomialSub_eq :
    Nat.card (monomialSub τ K) = Nat.card (torusGroup τ K) * Nat.card (WeylGroup τ) := by
  have h := Subgroup.card_ker_mul_card_range (monomialSubHom (τ := τ) (K := K))
  rw [MonoidHom.range_eq_top.2 monomialSubHom_surjective, Subgroup.card_top,
    monomialSubHom_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : borelSub τ K ⊓ monomialSub τ K ≤ monomialSub τ K)).toEquiv,
    borelSub_inf_monomialSub] at h
  have ht : Nat.card (torusSub τ K) = Nat.card (torusGroup τ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup')).toEquiv
  rw [← ht]
  exact h.symm



theorem not_dvd_index_monomialSub [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (ds : List ℕ) (hd0 : ∀ d ∈ ds, d ≠ 0)
    (hds : ∀ [Fintype (WeylGroup τ)] (x : ℕ), ∑ w : WeylGroup τ, x ^ (coxeterSystem τ).length w =
      (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod) :
    ¬ p ∣ (monomialSub τ K).index := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  set q := Nat.card K with hqdef
  have hq : 1 < q := Finite.one_lt_card
  have hpq' : ¬ p ∣ q := fun h => by
    have h1 : p ∣ q - (q - 1) := Nat.dvd_sub h hpq
    rw [show q - (q - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  refine not_dvd_index_of_card_eq hp _ ?_
  have hH0 : Nat.card (torusGroup τ K) ≠ 0 := by
    have : Finite (torusGroup τ K) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have hgs : ∀ d ∈ ds, ∑ i ∈ Finset.range d, q ^ i ≠ 0 := fun d hd => geom_sum_ne_zero hq.le (hd0 d hd)
  have hP0 : (ds.map fun d => ∑ i ∈ Finset.range d, q ^ i).prod ≠ 0 :=
    List.prod_ne_zero (fun h => by
      obtain ⟨d, hd, h0⟩ := List.mem_map.1 h
      exact hgs d hd h0)
  have hW : Nat.card (WeylGroup τ) = ds.prod := by
    have h1 := hds 1
    simp only [one_pow, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      Finset.card_univ] at h1
    rw [Nat.card_eq_fintype_card, h1, List.map_id']
  have hW0 : ds.prod ≠ 0 := List.prod_ne_zero (fun h => hd0 0 h rfl)
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, hds q, card_monomialSub_eq, hW,
    Nat.factorization_mul (Nat.mul_ne_zero hH0 (pow_ne_zero _ (by omega))) hP0,
    Nat.factorization_mul hH0 (pow_ne_zero _ (by omega)), Nat.factorization_mul hH0 hW0,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul, Nat.factorization_eq_zero_of_not_dvd hpq', mul_zero,
    add_zero, factorization_list_prod _ (fun a ha => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ha
      exact hgs d hd), factorization_list_prod _ hd0, List.map_map]
  congr 2
  refine List.map_congr_left fun d hd => ?_
  exact factorization_geom_sum_of_dvd_sub_one hp hp2 hq hpq (hd0 d hd)

end Card

end CFSG.LocalAnalysis.RankFourTheoremC
