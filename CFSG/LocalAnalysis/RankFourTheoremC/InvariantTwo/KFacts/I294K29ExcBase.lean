module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcSplit

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.HardMathSupport.Timmesfeld.LinearRank

theorem list_sum_map_add_const (ds : List ℕ) (a : ℕ) (v : ℕ → ℕ) :
    (ds.map fun d => a + v d).sum = ds.length * a + (ds.map v).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

section Base


variable {τ : Tag}

theorem exists_baseChange_adjointGroup {K K' : Type} [Field K] [Field K'] (f : K →+* K') :
    ∃ φ : adjointGroup τ K →* adjointGroup τ K', Function.Injective φ := by
  have hle : (adjointGroup τ K).map (baseChangeGL f) ≤ adjointGroup τ K' := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  refine ⟨((baseChangeGL f).comp (adjointGroup τ K).subtype).codRestrict _
    fun g => hle (Subgroup.mem_map_of_mem _ g.2), fun a b h => ?_⟩
  exact Subtype.ext (baseChangeGL_injective f (congrArg Subtype.val h))

theorem factorization_card_torusGroup {K : Type} [Field K] [Finite K] (p : ℕ) :
    (Nat.card (torusGroup τ K)).factorization p +
      (Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker).factorization p =
      τ.rank * (Nat.card K - 1).factorization p := by
  have h := card_torusGroup_mul (τ := τ) (K := K)
  have hH : Nat.card (torusGroup τ K) ≠ 0 := by
    have : Finite (torusGroup τ K) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have hk : Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker ≠ 0 := Nat.card_pos.ne'
  have := congrArg (fun n => n.factorization p) h
  simp only [Nat.factorization_mul hH hk, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul] at this
  exact this

theorem rank_adjointGroup_of_dvd_add_one {K K' : Type} [Field K] [Field K'] [Finite K]
    [Finite K'] (f : K →+* K') (hK' : Nat.card K' = Nat.card K ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hker : ¬ p ∣ Nat.card (zpowMatrix (G := K'ˣ) τ.cartan).ker) (hr : p + 1 ≤ τ.rank)
    (ds : List ℕ) (hd0 : ∀ d ∈ ds, d ≠ 0) (hde : ∀ d ∈ ds, 2 ∣ d) (hlen : ds.length = τ.rank)
    (hds : ∀ [Fintype (WeylGroup τ)] (x : ℕ), ∑ w : WeylGroup τ, x ^ (coxeterSystem τ).length w =
      (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) ∧
      ∀ y : adjointGroup τ K, y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (adjointGroup τ K))) := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  haveI : Finite (adjointGroup τ K') := generated_group_finite τ K'
  set q := Nat.card K with hqdef
  have hq : 1 < q := Finite.one_lt_card
  have hpq1 : ¬ p ∣ q - 1 := by
    intro h1
    have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq h1
    rw [show (q + 1) - (q - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hpq0 : ¬ p ∣ q := fun h => by
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq h
    rw [show (q + 1) - q = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    rcases q with _ | q
    · omega
    · simp only [Nat.add_sub_cancel]; ring_nf; omega
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hpq2 : p ∣ q ^ 2 - 1 := by rw [hsq]; exact Dvd.dvd.mul_right hpq _
  have hvsq : (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
    rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpq1, add_zero]
  have hgs : ∀ x, 1 ≤ x → ∀ d ∈ ds, ∑ i ∈ Finset.range d, x ^ i ≠ 0 :=
    fun x hx d hd => geom_sum_ne_zero hx (hd0 d hd)
  have hP0 : ∀ x, 1 ≤ x → (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod ≠ 0 :=
    fun x hx => List.prod_ne_zero (fun h => by
      obtain ⟨d, hd, h0⟩ := List.mem_map.1 h
      exact hgs x hx d hd h0)
  have hH0 : ∀ (L : Type) [Field L] [Finite L], Nat.card (torusGroup τ L) ≠ 0 := fun L _ _ => by
    have : Finite (torusGroup τ L) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have hvP : ∀ x, 1 ≤ x → (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod.factorization p =
      (ds.map fun d => (∑ i ∈ Finset.range d, x ^ i).factorization p).sum := fun x hx => by
    rw [factorization_list_prod _ (fun a ha => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ha
      exact hgs x hx d hd), List.map_map]
    rfl
  have hvK : (Nat.card (adjointGroup τ K)).factorization p =
      τ.rank * (q + 1).factorization p + (ds.map fun d => d.factorization p).sum := by
    have hT := factorization_card_torusGroup (τ := τ) (K := K) p
    rw [← hqdef, Nat.factorization_eq_zero_of_not_dvd hpq1, mul_zero] at hT
    rw [card_adjointGroup, finsum_eq_sum_of_fintype, hds q,
      Nat.factorization_mul (Nat.mul_ne_zero (hH0 K) (pow_ne_zero _ (by omega))) (hP0 q hq.le),
      Nat.factorization_mul (hH0 K) (pow_ne_zero _ (by omega)), Finsupp.add_apply,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hpq0, mul_zero, add_zero, hvP q hq.le]
    rw [List.map_congr_left (fun d hd => factorization_geom_sum_of_dvd_add_one hp hp2 hq hpq
      (hd0 d hd) (hde d hd)), list_sum_map_add_const, hlen]
    omega
  have hvK' : (Nat.card (adjointGroup τ K')).factorization p =
      τ.rank * (q + 1).factorization p + (ds.map fun d => d.factorization p).sum := by
    have hT := factorization_card_torusGroup (τ := τ) (K := K') p
    rw [hK', hvsq, Nat.factorization_eq_zero_of_not_dvd hker, add_zero] at hT
    have hq' : 1 < Nat.card K' := Finite.one_lt_card
    have hpq0' : ¬ p ∣ Nat.card K' := by
      rw [hK']
      exact fun h => hpq0 (hp.dvd_of_dvd_pow h)
    rw [card_adjointGroup, finsum_eq_sum_of_fintype, hds (Nat.card K'),
      Nat.factorization_mul (Nat.mul_ne_zero (hH0 K') (pow_ne_zero _ (by omega)))
        (hP0 _ hq'.le),
      Nat.factorization_mul (hH0 K') (pow_ne_zero _ (by omega)), Finsupp.add_apply,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hpq0', mul_zero, add_zero, hvP _ hq'.le, hT]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
    exact factorization_geom_sum_of_dvd_sub_one hp hp2 hq' (by rw [hK']; exact hpq2) (hd0 d hd)
  obtain ⟨φ, hφ⟩ := exists_baseChange_adjointGroup (τ := τ) f
  have hidx : ¬ p ∣ φ.range.index := by
    refine not_dvd_index_of_card_eq hp _ ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hvK, hvK']
  have hpq' : p ∣ Nat.card K' - 1 := by rw [hK']; exact hpq2
  obtain ⟨A, hAR, hRN, hA, hAc⟩ := exists_torsion_torusSub hp hpq' hker
  have hRidx := not_dvd_index_monomialSub (K := K') hp hp2 hpq' ds hd0 hds
  refine ⟨?_, fun y hy => three_le_pRank_centralizer_of_overgroup hp φ hφ hidx hAR hRN hRidx hA
    hAc hr hy⟩
  have := le_pRank_of_overgroup hp φ hφ hidx hAR hRN hRidx hA hAc
  have := hp.two_le
  omega

end Base

section Catalog


theorem crossAtPrime_untwisted_of_dvd_add_one {τ : Tag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {q : TauCeti.PrimePower}
    (hv : (c q).Valid) {p : ℕ} (hpq : p ∣ q.card + 1) (hr : p + 1 ≤ τ.rank)
    (hker : ∀ (K : Type) [Field K] [Finite K], 5 ≤ p →
      ¬ p ∣ Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker)
    (ds : List ℕ) (hd0 : ∀ d ∈ ds, d ≠ 0) (hde : ∀ d ∈ ds, 2 ∣ d) (hlen : ds.length = τ.rank)
    (hds : ∀ [Fintype (WeylGroup τ)] (x : ℕ), ∑ w : WeylGroup τ, x ^ (coxeterSystem τ).length w =
      (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod) :
    CrossAtPrime ⟨c q, hv⟩ p := by
  refine crossAtPrime_of_model fun hp hp5 _ => ?_
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have h2e : q.exponent * 2 ≠ 0 := Nat.mul_ne_zero q.exponent_pos.ne' (by norm_num)
  have hK' : Nat.card (GaloisField q.p (q.exponent * 2)) =
      Nat.card (GaloisField q.p q.exponent) ^ 2 := by
    rw [GaloisField.card _ _ h2e, hK, TauCeti.PrimePower.card_def, pow_mul]
  obtain ⟨ι⟩ : Nonempty (GaloisField q.p q.exponent →ₐ[ZMod q.p] GaloisField q.p (q.exponent * 2)) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [GaloisField.finrank q.p h2e, GaloisField.finrank q.p q.exponent_pos.ne']
      exact dvd_mul_right _ _)
  obtain ⟨φ⟩ := hB q hv (GaloisField q.p q.exponent) hK
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h3, hr'⟩ := rank_adjointGroup_of_dvd_add_one ι.toRingHom hK' hp hp2
    (by rw [hK]; exact hpq) (hker _ hp5) hr ds hd0 hde hlen hds
  haveI : Finite (adjointGroup τ (GaloisField q.p q.exponent)) := generated_group_finite τ _
  exact ⟨adjointGroup τ (GaloisField q.p q.exponent), inferInstance, inferInstance,
    ⟨φ.symm.trans (adjointQuotientEquiv τ _)⟩, h3, hr'⟩

theorem crossAtPrime_E7_five_of_dvd_add_one {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (hpq : 5 ∣ q.card + 1) :
    CrossAtPrime ⟨.E7 q, hv⟩ 5 :=
  crossAtPrime_untwisted_of_dvd_add_one CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 hv hpq
    (by decide) (fun _ _ _ _ => not_dvd_of_dvd_lt card_ker_zpowMatrix_dvd_E7 (by norm_num)
      (by norm_num))
    [2, 6, 8, 10, 12, 14, 18] (by decide) (by decide) rfl
    fun x => CFSG.RankThree.Chevalley.sum_length_E7_eq x

theorem crossAtPrime_E8_of_dvd_add_one {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp7 : p ≤ 7) (hpq : p ∣ q.card + 1) :
    CrossAtPrime ⟨.E8 q, hv⟩ p :=
  crossAtPrime_untwisted_of_dvd_add_one CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 hv hpq
    (by change p + 1 ≤ 8; omega) (fun _ _ _ hp5 => not_dvd_of_dvd_lt
      card_ker_zpowMatrix_dvd_E8 (by norm_num) (by omega))
    [2, 8, 12, 14, 18, 20, 24, 30] (by decide) (by decide) rfl
    fun x => CFSG.RankThree.Chevalley.sum_length_E8_eq x

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
