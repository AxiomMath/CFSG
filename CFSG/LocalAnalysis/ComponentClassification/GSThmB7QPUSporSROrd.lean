module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

namespace CFSG.ComponentClassification.GSThmB.QPUSpor

open CFSG Subgroup CFSG.Blueprint

theorem inf_center_eq_bot {M : Type*} [Group M] [Finite M] (hZ : IsPGroup 2 (center M))
    {L : Subgroup M} (hs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L)) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrd : r ∣ Nat.card (↥L ⧸ pPrimeCore 2 ↥L)) : L ⊓ center M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro z ⟨hzL, hzZ⟩
  rw [mem_bot]
  set y : L := ⟨z, hzL⟩ with hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ) ⟨z, hzZ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hky : orderOf y = 2 ^ k := by rw [hy, Subgroup.orderOf_mk, hk]
  have hn : (zpowers y).Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hc : Commute g y := Subtype.ext (mem_center_iff.1 hzZ g)
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
    exact ha
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  have hnπ : ((zpowers y).map π).Normal := hn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((zpowers y).map π) with h | h
  ·
    have hyO : y ∈ pPrimeCore 2 ↥L := by
      have h1 : π y ∈ (zpowers y).map π := mem_map_of_mem π (mem_zpowers y)
      rw [h, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥L)
    have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 ↥L) := by
      have h1 := orderOf_dvd_natCard (⟨y, hyO⟩ : pPrimeCore 2 ↥L)
      rwa [Subgroup.orderOf_mk] at h1
    have h1 : orderOf y = 1 := by
      rw [hky] at hdvd ⊢
      rcases k with _ | k
      · rfl
      · exact absurd ((dvd_pow_self 2 (by omega)).trans hdvd)
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  ·
    exfalso
    have h1 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ 2 ^ k := by
      rw [← Subgroup.card_top, ← h, ← hky, ← Nat.card_zpowers]
      exact Subgroup.card_map_dvd _ π
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow (hrd.trans h1)))

theorem card_dvd_card_quotient_center {M : Type*} [Group M] [Finite M] {L : Subgroup M}
    (h : L ⊓ center M = ⊥) : Nat.card L ∣ Nat.card (M ⧸ center M) := by
  refine Subgroup.card_dvd_of_injective ((QuotientGroup.mk' (center M)).comp L.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  have hx' : (x : M) ∈ L ⊓ center M := ⟨x.2, hx⟩
  rw [h, mem_bot] at hx'
  rw [mem_bot]
  exact Subtype.ext hx'

theorem card_mul_two_of_lieModel_psp
    {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (h : LieModel X .PSp 2 p f) : Finite X ∧ Nat.card X * 2 = psp4Num (p ^ f) := by
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .PSp 2 p f :=
    ⟨hp, hf, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  obtain ⟨hfin, hcard, -⟩ := CatLeafProof.lieOrderFormulasInput X .PSp 2 p f hadm h
  refine ⟨hfin, ?_⟩
  obtain ⟨m, hm⟩ := (hp.eq_two_or_odd'.resolve_left hp2).pow (n := f)
  have hdiv : CatLeaf.lieOrderDivisor .PSp 2 (p ^ f) = 2 := by
    simp only [CatLeaf.lieOrderDivisor]
    exact Nat.gcd_eq_left ⟨m, by omega⟩
  have hnum : CatLeaf.lieOrderNumerator .PSp 2 (p ^ f) = psp4Num (p ^ f) := by
    simp only [CatLeaf.lieOrderNumerator]
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), psp4Num]
    norm_num [mul_assoc]
  rw [← hdiv, hcard, hnum]

theorem card_carrier_eq_sporOrder
    (s : TauCeti.SporadicName) (hM : s ≠ .M) :
    Nat.card (NativeSporadic.Carrier s) = sporOrder s := by
  by_cases hTh : s = .Th
  · subst hTh
    change Nat.card NativeSporadic.Th = _
    rw [RankThree.PartOne.CTP.card_Th]
    decide
  · rw [EvenSmallLie.Child3.card_carrier s hTh hM]
    cases s <;> first | exact absurd rfl hM | exact absurd rfl hTh | decide

theorem psp4_pair_of_le
    {M : Type} [Group M] [Finite M] (hZ : IsPGroup 2 (center M)) {s : TauCeti.SporadicName}
    (e : M ⧸ center M ≃* NativeSporadic.Carrier s) (hM : s ≠ .M) {L : Subgroup M} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hL : LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f) :
    (s = .Co1 ∨ s = .B) ∧ p ^ f = 5 := by
  obtain ⟨-, hcard⟩ := card_mul_two_of_lieModel_psp hp hp2 hf h5 hL
  have hs := SeitzReduction.F4Pilot.isSimpleGroup_of_lieModel_PSp hL
  have hpd : p ∣ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
    have h1 : p ∣ psp4Num (p ^ f) :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self p (by omega)) (by norm_num)) _) _
    rw [← hcard] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hp Nat.prime_two).2 hp2) h1
  have hLZ := inf_center_eq_bot hZ hs hp hp2 hpd
  have h1 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card (M ⧸ center M) :=
    (Subgroup.card_quotient_dvd_card _).trans (card_dvd_card_quotient_center hLZ)
  rw [Nat.card_congr e.toEquiv, card_carrier_eq_sporOrder s hM] at h1
  have h2 : psp4Num (p ^ f) ∣ 2 * sporOrder s := by
    rw [← hcard, mul_comm]
    exact Nat.mul_dvd_mul_left 2 h1
  have h3 := psp4_allowed s hp hp2 hf h5 h2
  cases s <;> simp only [psp4Allowed, beq_iff_eq, Bool.false_eq_true] at h3
  all_goals first | exact absurd rfl hM | exact ⟨Or.inl rfl, h3⟩ | exact ⟨Or.inr rfl, h3⟩

end CFSG.ComponentClassification.GSThmB.QPUSpor
