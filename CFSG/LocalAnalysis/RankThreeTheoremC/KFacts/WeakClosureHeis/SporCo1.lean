module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporDispatch
public import CFSG.RankThree.PartOne.KS.Co1ScalCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Blueprint CFSG.RankThree.PartOne.KS.ScalFive CFSG.RankThree.PartOne.KS.Co1Scal
  CFSG.Monster.B.Pinned
open scoped commutatorElement

section Abstract

variable {G : Type} [Group G] [Finite G] {q : Fin 2 → G} {z s t : G}
  {M Sm : Matrix (Fin 2) (Fin 2) (ZMod 5)} {cs ct : Fin 2 → ℕ} {r : ZMod 5}

theorem sylowDichotomyAt_five_of_scalRel_two (hR : ScalRel q z s t M Sm 0 1 cs r ct)
    (hs : s⁻¹ * q 0 * s = q 0 * q 1 ^ 4) : SylowDichotomyAt G 5 := by
  have hfact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hs25 : s ^ 25 = 1 := by
    have h := hR.pow_five_of_mem hR.s_pow
    rwa [← pow_mul] at h
  have hsP : IsPGroup 5 (Subgroup.zpowers s) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1
      (show orderOf s ∣ 5 ^ 2 from orderOf_dvd_of_pow_eq_one hs25)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hQP : IsPGroup 5 (QG q) := IsPGroup.of_card hR.card_Q
  have hnorm : Subgroup.zpowers s ≤ Subgroup.normalizer (QG q) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    exact hR.H_conj' (Subgroup.zpowers_le.2 (s_mem_H (t := t)) hh) k hk
  have hU : IsPGroup 5 ↥(Subgroup.zpowers s ⊔ QG q) := hsP.to_sup_of_normal_right' hQP hnorm
  set U : Subgroup G := Subgroup.zpowers s ⊔ QG q
  have hq0U : q 0 ∈ U := Subgroup.mem_sup_right (q_mem 0)
  have hq1U : q 1 ∈ U := Subgroup.mem_sup_right (q_mem 1)
  have hsU : s ∈ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  have hcomm : ∀ a b : G, a ∈ U → b ∈ U → bcomm a b ∈ ⁅U, U⁆ := by
    intro a b ha hb
    have := Subgroup.commutator_mem_commutator (Subgroup.inv_mem U ha) (Subgroup.inv_mem U hb)
    simpa [bcomm, commutatorElement_def] using this
  have hz : z ∈ ⁅U, U⁆ := hR.z_eq ▸ hcomm _ _ hq0U hq1U
  have hy : q 1 ^ 4 ∈ ⁅U, U⁆ := by
    have := hcomm (q 0) s hq0U hsU
    have h2 : bcomm (q 0) s = q 1 ^ 4 := by
      unfold bcomm
      calc (q 0)⁻¹ * s⁻¹ * q 0 * s = (q 0)⁻¹ * (s⁻¹ * q 0 * s) := by group
        _ = q 1 ^ 4 := by rw [hs]; group
    rwa [h2] at this
  have h5 : q 1 ^ 5 = 1 := hR.pow_five_of_mem (q_mem 1)
  have hq1 : q 1 ∈ ⁅U, U⁆ := by
    have : (q 1 ^ 4) ^ 4 = q 1 := by
      calc (q 1 ^ 4) ^ 4 = (q 1 ^ 5) ^ 3 * q 1 := by group
        _ = q 1 := by rw [h5]; group
    rw [← this]
    exact pow_mem hy 4
  refine SylowDichotomyAt.of_not_cyclic_derived hU ?_
  intro hcyc
  have hz1 : z ≠ 1 := by
    intro h
    have := hR.orderOf_z
    rw [h, orderOf_one] at this
    omega
  have hq1_ne : q 1 ≠ 1 := by
    intro h
    apply hz1
    rw [← hR.z_eq, h]
    simp [bcomm]
  have hq1_ord : orderOf (q 1) = 5 := orderOf_eq_prime h5 hq1_ne
  let a : ↥⁅U, U⁆ := ⟨z, hz⟩
  let b : ↥⁅U, U⁆ := ⟨q 1, hq1⟩
  have ha : orderOf a = 5 := by
    rw [show orderOf a = orderOf z from Subgroup.orderOf_mk z hz]
    exact hR.orderOf_z
  have hb : orderOf b = 5 := by
    rw [show orderOf b = orderOf (q 1) from Subgroup.orderOf_mk (q 1) hq1]
    exact hq1_ord
  have heq : Subgroup.zpowers a = Subgroup.zpowers b := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  have hbmem : b ∈ Subgroup.zpowers a := heq ▸ Subgroup.mem_zpowers b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbmem
  have hkz : z ^ k = q 1 := by
    have := congrArg Subtype.val hk
    simpa [a, b] using this
  have hc : Commute (q 0) (q 1) := by
    rw [← hkz]
    exact Commute.zpow_right (hR.Q_commute_z (q_mem 0)) k
  apply hz1
  rw [← hR.z_eq]
  have h1 : ⁅(q 0)⁻¹, (q 1)⁻¹⁆ = 1 := commutatorElement_eq_one_iff_commute.2 hc.inv_inv
  simpa [bcomm, commutatorElement_def] using h1

end Abstract

theorem co1_conj_s_zero :
    (Rg co1Data.iS)⁻¹ * Rg (co1Data.iQ 0) * Rg co1Data.iS =
      Rg (co1Data.iQ 0) * Rg (co1Data.iQ 1) ^ 4 := by
  have h00 : (co1Data.Sm 0 0).val = 1 := by decide +kernel
  have h01 : (co1Data.Sm 0 1).val = 4 := by decide +kernel
  have hc0 : co1Data.cs 0 = 0 := by decide
  rw [co1Scal_rel.conj_s 0]
  simp [List.ofFn_succ, h00, h01, hc0]

theorem sdSpor_Co1_5 : SDSporAt .Co1 5 := by
  intro K _ _ ⟨e⟩
  haveI hfin : Finite (NativeSporadic.Carrier .Co1) := (inferInstance : Finite NativeSporadic.Co1)
  refine SylowDichotomyAt.of_mulEquiv Nat.prime_five e ?_
  exact sylowDichotomyAt_five_of_scalRel_two co1Scal_rel co1_conj_s_zero

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
