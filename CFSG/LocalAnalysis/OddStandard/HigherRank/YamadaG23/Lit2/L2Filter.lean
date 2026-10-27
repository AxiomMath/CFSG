module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Tables
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Arith
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint.Multiplier

theorem l2_elem_order_four {K X P : Type} [Group K] [Finite K] [Group X] [Group P]
    (hK : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* X)
    (eM : CFSG.Open.griessHopfMultiplier X ≃* P) (hz : ∃ z ∈ center K, orderOf z = 4) :
    ∃ m : P, 4 ∣ orderOf m := by
  haveI : Group.IsPerfect K := hK.1
  have hqsurj : Function.Surjective (CFSG.RankThree.PerfectCover.centralQuotientMap e) :=
    CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hqker : (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker = center K :=
    CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  let ψ : CFSG.RankThree.PerfectCover.hopfMultiplier X →*
      (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer
      (CFSG.RankThree.PerfectCover.centralQuotientMap e) hqsurj hqker.le
  have hψ : Function.Surjective ψ :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective _ hqsurj hqker.le
  let φ : P →* CFSG.RankThree.PerfectCover.hopfMultiplier X :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toMonoidHom.comp
      eM.symm.toMonoidHom
  have hφ : Function.Surjective φ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).surjective.comp eM.symm.surjective
  let ψ' : P →* (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker := ψ.comp φ
  have hψ' : Function.Surjective ψ' := hψ.comp hφ
  obtain ⟨z, hzmem, hzord⟩ := hz
  have hzker : z ∈ (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker := by
    rw [hqker]; exact hzmem
  obtain ⟨m, hm⟩ := hψ' ⟨z, hzker⟩
  refine ⟨m, ?_⟩
  have hdvd : orderOf (ψ' m) ∣ orderOf m := orderOf_map_dvd ψ' m
  have hord : orderOf
      (⟨z, hzker⟩ : (CFSG.RankThree.PerfectCover.centralQuotientMap e).ker) = 4 := by
    rw [Subgroup.orderOf_mk, hzord]
  rw [hm, hord] at hdvd
  exact hdvd

theorem l2_lie_four (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (hX : CFSG.Blueprint.LieModel (K ⧸ center K) t n p f)
    (hz : ∃ z ∈ center K, orderOf z = 4) :
    4 ∣ (genericOrders t n p f).1 ∨ 4 ∣ (genericOrders t n p f).2 ∨
      4 ∣ (exceptionalOrders t n p f).1 ∨ 4 ∣ (exceptionalOrders t n p f).2 := by
  obtain ⟨-, ⟨eM⟩⟩ := hG (K ⧸ center K) t n p f hX
  obtain ⟨m, hm⟩ := l2_elem_order_four hK (MulEquiv.refl (K ⧸ center K)) eM hz
  exact l2_four_dvd_orders t n p f m hm

theorem l2_alt_no_four
    (hA : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {m : ℕ} (hm : 5 ≤ m)
    (e : K ⧸ center K ≃* alternatingGroup (Fin m)) : ¬ ∃ z ∈ center K, orderOf z = 4 := by
  rintro ⟨z, hzmem, hzord⟩
  have h4 : 4 ∣ Nat.card (center K) := by
    have h := orderOf_dvd_natCard (⟨z, hzmem⟩ : center K)
    rwa [Subgroup.orderOf_mk, hzord] at h
  have hdvd : Nat.card (center K) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin m))) :=
    CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hK e
  rw [(hA m hm).2] at hdvd
  by_cases h : m = 6 ∨ m = 7
  · rw [if_pos h] at hdvd
    have : 4 ∣ 6 := h4.trans hdvd
    omega
  · rw [if_neg h] at hdvd
    have : 4 ∣ 2 := h4.trans hdvd
    omega

theorem l2_spor_four
    (hS : CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.NativeSporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hs : CFSG.Blueprint.NativeSporadic.SporadicRep (K ⧸ center K))
    (hz : ∃ z ∈ center K, orderOf z = 4) :
    CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ center K) .M22 := by
  obtain ⟨s, ⟨e⟩⟩ := hs
  have h4 : 4 ∣ Nat.card (center K) := by
    obtain ⟨z, hzmem, hzord⟩ := hz
    have h := orderOf_dvd_natCard (⟨z, hzmem⟩ : center K)
    rwa [Subgroup.orderOf_mk, hzord] at h
  have hdvd : Nat.card (center K) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (CFSG.Blueprint.NativeSporadic.Carrier s)) :=
    CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hK e
  rw [hS s] at hdvd
  have h4s : 4 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := h4.trans hdvd
  have hsM22 : s = .M22 := by
    revert h4s
    cases s <;> decide
  rw [hsM22] at e
  exact ⟨e⟩

theorem l2_filter (hT : L2Tables) {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hcat : CFSG.Blueprint.Catalog (K ⧸ center K)) (hz : ∃ z ∈ center K, orderOf z = 4) :
    L2Z4Type (K ⧸ center K) := by
  have hnab : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.2.2
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition (K ⧸ center K) hnab).mp hcat with
    hA | hOdd | hEven | hS
  · rcases hA with ⟨m, hm, ⟨e⟩⟩
    exact (l2_alt_no_four hT.2.2 hK hm e hz).elim
  · rcases hOdd with ⟨t, n, p, f, _hp, _hp2, _hadm, hX⟩
    exact l2_orders_cases hX (l2_lie_four hT.1 hK hX hz)
  · rcases hEven with ⟨t, n, f, _hadm, hX⟩
    exact l2_orders_cases hX (l2_lie_four hT.1 hK hX hz)
  · exact Or.inl (l2_spor_four hT.2.1 hK hS hz)

end CFSG.OddStandard.HigherRank.YamadaG23
