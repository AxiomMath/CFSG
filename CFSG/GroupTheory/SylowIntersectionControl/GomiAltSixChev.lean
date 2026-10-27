module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.StronglyEmbedded.Catalog.SuzukiThree
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GroupTheory

private theorem card_alternatingGroup_six_ga6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem card_alternatingGroup_five_ga6 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem exists_not_commute_alt_six_ga6 :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra h
  have hcomm : IsMulCommutative (alternatingGroup (Fin 6)) :=
    isMulCommutative_iff.mpr fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩
  rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hcomm
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcomm
  omega

private theorem not_two_pow_mul_sq_sub_one_eq_360_ga6 {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 360 := by
  intro h
  have hdvd : 2 ^ n ∣ 360 := ⟨(2 ^ n) ^ 2 - 1, h.symm⟩
  have hle : 2 ^ n ≤ 360 := Nat.le_of_dvd (by norm_num) hdvd
  have hn9 : n ≤ 8 := by
    by_contra hlt
    have h9 : 9 ≤ n := by omega
    have hpow : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h9
    norm_num at hpow
    omega
  interval_cases n <;> norm_num at h

private theorem pCore_two_alt_six_ga6 : CFSG.pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 (alternatingGroup (Fin 6))) with
    h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_not_commute_alt_six_ga6
    have hp2 : IsPGroup 2 (CFSG.pCore 2 (alternatingGroup (Fin 6))) := CFSG.pCore_isPGroup
    have hp : IsPGroup 2 (alternatingGroup (Fin 6)) := by
      rw [h] at hp2
      exact hp2.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent (alternatingGroup (Fin 6)) := hp.isNilpotent
    have hsol : Group.IsSolvable (alternatingGroup (Fin 6)) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 6))).mpr hsol a b)

private theorem isQuasisimple_alt_six_ga6 : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup exists_not_commute_alt_six_ga6).1

private theorem isGomiChevTwo_alt_six_ga6 : IsGomiChevTwo (alternatingGroup (Fin 6)) := by
  refine ⟨isQuasisimple_alt_six_ga6, pCore_two_alt_six_ga6, ?_⟩
  have hc : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have eQ : (alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6))) ≃*
      alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), ⟨eQ⟩⟩)

private theorem card_psu_three_two_mul_ga6 {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSU 3 2 n) :
    Nat.card X * Nat.gcd 3 (2 ^ n + 1) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu (k := 3) (p := 2) (e := n)
    (by norm_num) h
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have e2 : (((2 ^ n : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ n) ^ 2 - 1 := by
    have : (((2 ^ n : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((2 ^ n) ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
      push_cast
      first | done | ring
    rw [this, Int.toNat_natCast]
  have e3 : (((2 ^ n : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ n) ^ 3 + 1 := by
    have : (((2 ^ n : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((2 ^ n) ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      first | done | ring
    rw [this, Int.toNat_natCast]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((2 ^ n : ℕ) : ℤ) ^ i - (-1) ^ i).toNat =
      ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num), e2, e3]
  rw [hprod, show 3 * (3 - 1) / 2 = 3 by norm_num] at h1
  have h2 : Nat.gcd 3 (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.gcd_dvd_right _ _
  have h3 : 2 ^ n + 1 ∣ (2 ^ n) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 (by decide : Odd 3)
  have hd : Nat.gcd 3 (2 ^ n + 1) ∣
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (h2.trans h3) _) _
  rw [h1, Nat.div_mul_cancel hd, mul_assoc]

theorem not_isGomiL2_alternatingGroup_six : ¬ IsGomiL2 (alternatingGroup (Fin 6)) := by
  intro h
  rcases h with hleft | hright
  · obtain ⟨e⟩ := hleft
    have hcard := Nat.card_congr e.toEquiv
    rw [card_alternatingGroup_six_ga6, card_alternatingGroup_five_ga6] at hcard
    norm_num at hcard
  · obtain ⟨⟨d, hv⟩, ⟨q, hq2, rfl⟩, ⟨e⟩⟩ := hright
    have hmodel :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA (r := 1) hv e
    rw [hq2] at hmodel
    have h2 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hmodel
    have hn2 : 2 ≤ q.exponent := by
      have h4 : 4 ≤ q.card :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
          ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
      rw [TauCeti.PrimePower.card_def, hq2] at h4
      by_contra hlt
      have hle : q.exponent ≤ 1 := by omega
      have hpow : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpow
      omega
    exact not_two_pow_mul_sq_sub_one_eq_360_ga6 hn2
      (h2.symm.trans card_alternatingGroup_six_ga6)

theorem not_isGomiU3_alternatingGroup_six : ¬ IsGomiU3 (alternatingGroup (Fin 6)) := by
  intro h
  rcases h with ⟨⟨d, hv⟩, ⟨q, hq2, rfl⟩, ⟨e⟩⟩
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hq2] at hmodel
  have hn2 : 2 ≤ q.exponent := by
    have h3 : 3 ≤ q.card :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
    rw [TauCeti.PrimePower.card_def, hq2] at h3
    by_contra hlt
    have hle : q.exponent ≤ 1 := by omega
    have hpow : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    norm_num at hpow
    omega
  have hmul := card_psu_three_two_mul_ga6 hmodel
  have h64 : 64 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    have h64N : 64 ∣ (2 ^ q.exponent) ^ 3 * ((2 ^ q.exponent) ^ 2 - 1) *
        ((2 ^ q.exponent) ^ 3 + 1) := by
      have h1 : 64 ∣ (2 ^ q.exponent) ^ 3 := by
        rw [← pow_mul]
        have hpow : 2 ^ 6 = (64 : ℕ) := by norm_num
        rw [← hpow]
        exact pow_dvd_pow 2 (by omega : 6 ≤ q.exponent * 3)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h1 _) _
    have hcop : Nat.Coprime 64 (Nat.gcd 3 (2 ^ q.exponent + 1)) :=
      Nat.Coprime.of_dvd_right (Nat.gcd_dvd_left 3 _) (by decide : Nat.Coprime 64 3)
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [hmul]
    exact h64N
  rw [card_alternatingGroup_six_ga6] at h64
  norm_num at h64

theorem not_isGomiSz_alternatingGroup_six : ¬ IsGomiSz (alternatingGroup (Fin 6)) := by
  intro h
  rcases h with ⟨⟨d, hv⟩, ⟨k, rfl⟩, ⟨e⟩⟩
  refine CFSG.BenderSuzuki.Catalog.not_three_dvd_card_lie_suzuki hv ?_
  rw [Nat.card_congr e.symm.toEquiv, card_alternatingGroup_six_ga6]
  norm_num

theorem isGomiChevTwo_of_mulEquiv_altSix {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 6)) :
    IsGomiChevTwo Y ∧ ¬ IsGomiL2 (Y ⧸ Subgroup.center Y) ∧ ¬ IsGomiU3 (Y ⧸ Subgroup.center Y) ∧
      ¬ IsGomiSz (Y ⧸ Subgroup.center Y) := by
  have eZ := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
    (Subgroup.map_center_eq e)
  have hc : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have eQ : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6) :=
    eZ.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  exact ⟨IsGomiChevTwo.of_mulEquiv e.symm isGomiChevTwo_alt_six_ga6,
    fun h => not_isGomiL2_alternatingGroup_six (IsGomiL2.of_mulEquiv eQ h),
    fun h => not_isGomiU3_alternatingGroup_six (IsGomiU3.of_mulEquiv eQ h),
    fun h => not_isGomiSz_alternatingGroup_six (IsGomiSz.of_mulEquiv eQ h)⟩

end CFSG.GroupTheory

end
