module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcE
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRank
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcIndex
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcTorus
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders

theorem crossAtPrime_of_model {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (h : p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
      ∃ (G : Type) (_ : Group G) (_ : Finite G),
        Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* G) ∧ 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) ∧
          ∀ y : G, y ^ p = 1 → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set G))) :
    CrossAtPrime d p := by
  intro hp hp5 hdp
  obtain ⟨G, _, _, ⟨φ⟩, h3, hr⟩ := h hp hp5 hdp
  refine ⟨fun L _ _ _ ⟨e⟩ _ h2 _ => ?_, fun L _ _ _ ⟨e⟩ _ _ y hy => ?_⟩
  · exfalso
    have := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (e.trans φ).symm.toMonoidHom
      (e.trans φ).symm.injective
    omega
  · set ψ := e.trans φ with hψ
    have hyp : ψ y ^ p = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    have h1 := hr (ψ y) hyp
    have h2 := CFSG.SectionRank.pRank_le_map hp.one_lt ψ.symm.toMonoidHom ψ.symm.injective
      (centralizer ({ψ y} : Set G))
    have h3 : (centralizer ({ψ y} : Set G)).map ψ.symm.toMonoidHom ≤
        centralizer ({y} : Set L) := by
      rintro _ ⟨c, hc, rfl⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg ψ.symm hc'
      simp only [map_mul, MulEquiv.symm_apply_apply] at this
      simpa only [MulEquiv.coe_toMonoidHom] using this
    have h4 := CFSG.SectionRank.pRank_mono hp.one_lt h3
    omega

section Adjoint


variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem rank_adjointGroup_of_dvd_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hker : ¬ p ∣ Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker)
    (hr : p + 1 ≤ τ.rank) (ds : List ℕ) (hd0 : ∀ d ∈ ds, d ≠ 0)
    (hds : ∀ [Fintype (WeylGroup τ)] (x : ℕ), ∑ w : WeylGroup τ, x ^ (coxeterSystem τ).length w =
      (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) ∧
      ∀ y : adjointGroup τ K, y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (adjointGroup τ K))) := by
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨A, hAR, hRN, hA, hAc⟩ := exists_torsion_torusSub hp hpq hker
  have hRidx := not_dvd_index_monomialSub hp hp2 hpq ds hd0 hds
  have hidx : ¬ p ∣ (MonoidHom.id (adjointGroup τ K)).range.index := by
    rw [MonoidHom.range_eq_top.2 Function.surjective_id, Subgroup.index_top]
    exact hp.not_dvd_one
  refine ⟨?_, fun y hy => three_le_pRank_centralizer_of_overgroup hp (MonoidHom.id _)
    Function.injective_id hidx hAR hRN hRidx hA hAc hr hy⟩
  have := le_pRank_of_overgroup hp (MonoidHom.id _) Function.injective_id hidx hAR hRN hRidx hA hAc
  have := hp.two_le
  omega

noncomputable def adjointQuotientEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    AdjointQuotient τ K ≃* adjointGroup τ K :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

theorem card_ker_zpowMatrix_dvd_E6 :
    Nat.card (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker ∣ 3 := by
  have h1 := card_torusGroup_mul (τ := .E6) (K := K)
  have h2 := card_torusGroup_E6 (K := K)
  have hH : Nat.card (torusGroup .E6 K) ≠ 0 := by
    have : Finite (torusGroup .E6 K) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have : Nat.card (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker = (Nat.card K - 1).gcd 3 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH) (h1.trans h2.symm)
  rw [this]
  exact Nat.gcd_dvd_right _ _

theorem card_ker_zpowMatrix_dvd_E7 :
    Nat.card (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker ∣ 2 := by
  have h1 := card_torusGroup_mul (τ := .E7) (K := K)
  have h2 := card_torusGroup_E7 (K := K)
  have hH : Nat.card (torusGroup .E7 K) ≠ 0 := by
    have : Finite (torusGroup .E7 K) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have : Nat.card (zpowMatrix (G := Kˣ) Tag.E7.cartan).ker = (Nat.card K - 1).gcd 2 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH) (h1.trans h2.symm)
  rw [this]
  exact Nat.gcd_dvd_right _ _

theorem card_ker_zpowMatrix_dvd_E8 :
    Nat.card (zpowMatrix (G := Kˣ) Tag.E8.cartan).ker ∣ 1 := by
  have h1 := card_torusGroup_mul (τ := .E8) (K := K)
  have h2 := card_torusGroup_E8 (K := K)
  have hH : Nat.card (torusGroup .E8 K) ≠ 0 := by
    have : Finite (torusGroup .E8 K) := Finite.of_injective _ Subtype.val_injective
    exact Nat.card_pos.ne'
  have : Nat.card (zpowMatrix (G := Kˣ) Tag.E8.cartan).ker = 1 := by
    have h3 : Nat.card (torusGroup .E8 K) * Nat.card (zpowMatrix (G := Kˣ) Tag.E8.cartan).ker =
        Nat.card (torusGroup .E8 K) * 1 := by rw [h1, h2, mul_one]; rfl
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH) h3
  rw [this]

end Adjoint

theorem not_dvd_of_dvd_lt {p n m : ℕ} (hn : n ∣ m) (hm : 0 < m) (hmp : m < p) : ¬ p ∣ n :=
  fun h => absurd (Nat.le_of_dvd hm (h.trans hn)) (by omega)

section Catalog


theorem crossAtPrime_untwisted_of_dvd_sub_one {τ : Tag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {q : TauCeti.PrimePower}
    (hv : (c q).Valid) {p : ℕ} (hpq : p ∣ q.card - 1) (hr : p + 1 ≤ τ.rank)
    (hker : ∀ (K : Type) [Field K] [Finite K], 5 ≤ p →
      ¬ p ∣ Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker)
    (ds : List ℕ) (hd0 : ∀ d ∈ ds, d ≠ 0)
    (hds : ∀ [Fintype (WeylGroup τ)] (x : ℕ), ∑ w : WeylGroup τ, x ^ (coxeterSystem τ).length w =
      (ds.map fun d => ∑ i ∈ Finset.range d, x ^ i).prod) :
    CrossAtPrime ⟨c q, hv⟩ p := by
  refine crossAtPrime_of_model fun hp hp5 _ => ?_
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨φ⟩ := hB q hv (GaloisField q.p q.exponent) hK
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h3, hr'⟩ := rank_adjointGroup_of_dvd_sub_one (K := GaloisField q.p q.exponent) hp hp2
    (by rw [hK]; exact hpq) (hker _ hp5) hr ds hd0 hds
  haveI : Finite (adjointGroup τ (GaloisField q.p q.exponent)) := generated_group_finite τ _
  exact ⟨adjointGroup τ (GaloisField q.p q.exponent), inferInstance, inferInstance,
    ⟨φ.symm.trans (adjointQuotientEquiv τ _)⟩, h3, hr'⟩

theorem crossAtPrime_E6_five_of_dvd {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hpq : 5 ∣ q.card - 1) :
    CrossAtPrime ⟨.E6 q, hv⟩ 5 :=
  crossAtPrime_untwisted_of_dvd_sub_one CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 hv hpq
    (by decide) (fun _ _ _ hp5 => not_dvd_of_dvd_lt card_ker_zpowMatrix_dvd_E6 (by norm_num) (by omega))
    [2, 5, 6, 8, 9, 12] (by decide) fun x => CFSG.RankThree.Chevalley.sum_length_E6_eq x

theorem crossAtPrime_E7_five_of_dvd {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (hpq : 5 ∣ q.card - 1) :
    CrossAtPrime ⟨.E7 q, hv⟩ 5 :=
  crossAtPrime_untwisted_of_dvd_sub_one CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 hv hpq
    (by decide) (fun _ _ _ hp5 => not_dvd_of_dvd_lt
      card_ker_zpowMatrix_dvd_E7 (by norm_num) (by omega))
    [2, 6, 8, 10, 12, 14, 18] (by decide) fun x => CFSG.RankThree.Chevalley.sum_length_E7_eq x

theorem crossAtPrime_E8_of_dvd {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ} (hp7 : p ≤ 7) (hpq : p ∣ q.card - 1) :
    CrossAtPrime ⟨.E8 q, hv⟩ p :=
  crossAtPrime_untwisted_of_dvd_sub_one CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 hv hpq
    (by change p + 1 ≤ 8; omega) (fun _ _ _ hp5 => not_dvd_of_dvd_lt
      card_ker_zpowMatrix_dvd_E8 (by norm_num) (by omega))
    [2, 8, 12, 14, 18, 20, 24, 30] (by decide) fun x => CFSG.RankThree.Chevalley.sum_length_E8_eq x

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
