module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SL2RankB
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SSplit
public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

namespace SL2Rank

theorem center_hat_ne_bot {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {q : ℕ} (hq : Odd q)
    (hK : HasSL2Model ↥K (fun q' => q' = q)) : center (Hat K) ≠ ⊥ := by
  obtain ⟨t, htK, ht2, huniq, -⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hq hK
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2, sq] at this
    exact this
  have htc : ∀ w ∈ K, t * w = w * t := by
    intro w hw
    have h1 : w * t * w⁻¹ ∈ K := K.mul_mem (K.mul_mem hw htK) (K.inv_mem hw)
    have h2 : (w * t * w⁻¹) * (w * t * w⁻¹) = 1 := by
      calc (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
        _ = 1 := by rw [htt]; group
    rcases huniq _ h1 h2 with h | h
    · exfalso
      apply ht1
      have h3 : w * t = w := mul_inv_eq_one.1 h
      exact mul_eq_left.1 h3
    · calc t * w = (w * t * w⁻¹) * w := by rw [h]
        _ = w * t := by group
  intro hbot
  have hmem : (QuotientGroup.mk ⟨t, htK⟩ : Hat K) ∈ center (Hat K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (htc w w.2).symm
  have h1 : (QuotientGroup.mk ⟨t, htK⟩ : Hat K) = 1 := (Subgroup.eq_bot_iff_forall _).1 hbot _ hmem
  rw [QuotientGroup.eq_one_iff] at h1
  have h3 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥K) h1
  rw [Subgroup.orderOf_mk, ht2] at h3
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  exact hN h3

theorem card_le_two_of_unique {Y : Type} [Group Y] (C : Subgroup Y)
    (huniq : ∀ u ∈ C, ∀ v ∈ C, u ≠ 1 → v ≠ 1 → u = v) : Nat.card ↥C ≤ 2 := by
  by_cases h : ∃ u ∈ C, u ≠ 1
  · obtain ⟨u, huC, hu1⟩ := h
    have hsub : (C : Set Y) ⊆ {1, u} := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · exact Or.inr (huniq x hx u huC hx1 hu1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : Nat.card ↥C = (C : Set Y).ncard := Nat.card_coe_set_eq (C : Set Y)
    have h3 : ({1, u} : Set Y).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  · push Not at h
    have : C = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [this, Subgroup.card_bot]
    norm_num

end SL2Rank

theorem p47SL2b_thm : P47BranchSL2b := by
  intro G _ _ z k S _ F4 Y _ _ b hY _ p X hA _ hc T' _ _ hTn E hET hE
  have hEN : E ≤ normalizer (X : Set Y) := hET.trans hTn
  have hcard := SL2Rank.card_le_four_mul_card_cent hA.prime hA.odd hc hEN hE
  have hC : Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) ≤ 2 := by
    obtain ⟨n, hn, hmodel, -⟩ := hc
    have hq : Odd (p ^ n) := (hA.prime.odd_of_ne_two hA.odd).pow
    have hnormal : (ncl X).Normal := Subgroup.normalClosure_normal
    have hcomp : IsComponent (ncl X) :=
      ⟨CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 (by omega) hmodel, hnormal.isSubnormal⟩
    have hZ := SL2Rank.center_hat_ne_bot hq hmodel
    apply SL2Rank.card_le_two_of_unique
    intro u hu v hv hu1 hv1
    have hu2 : u * u = 1 := by simpa [sq] using hE.2 u hu.1
    have hv2 : v * v = 1 := by simpa [sq] using hE.2 v hv.1
    have huv : u * v = v * u := hE.1.is_comm.comm ⟨u, hu.1⟩ ⟨v, hv.1⟩ |> congrArg Subtype.val
    exact F4.uinv Y b hY (ncl X) hcomp hZ u v hu2 hv2 hu1 hv1 hu.2 hv.2 huv
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
