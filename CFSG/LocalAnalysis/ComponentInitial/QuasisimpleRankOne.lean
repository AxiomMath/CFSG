module

public import CFSG.LocalAnalysis.ComponentInitial.PerfectRankOneSylow
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Adapters.Involutions
public import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hsol
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  obtain ⟨n, hn⟩ := hsol.solvable
  have htop : ∀ m, derivedSeries Q m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [derivedSeries_succ, ih]
      exact hperf.commutator_eq_top
  rw [htop] at hn
  have hall : ∀ x : Q, x = 1 := fun x => mem_bot.1 (hn ▸ mem_top x)
  apply hab
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [hall a, hall b]

theorem quasisimple_rank_one_unique_central_involution {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (hr : CFSG.pRank 2 Q ≤ 1) :
    Even (Nat.card Q) ∧ (∃! z : Q, orderOf z = 2) ∧
      (∀ z : Q, orderOf z = 2 → z ∈ center Q) ∧
      ∀ T : Sylow 2 Q, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect Q := hQ.1
  have heven : Even (Nat.card Q) := by
    by_contra hodd
    exact not_isSolvable_of_isQuasisimple hQ
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 hodd))
  have hquat := perfect_rank_one_Sylow_quaternion heven hr
  let T : Sylow 2 Q := default
  obtain ⟨n, hn, ⟨e⟩⟩ := hquat T
  have hm : 0 < 2 ^ (n - 2) := Nat.two_pow_pos _
  set t : Q := (e.symm (QuaternionGroup.a ((2 ^ (n - 2) : ℕ) : ZMod (2 * 2 ^ (n - 2))))).1
    with htdef
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hm _).2 rfl
  have htT : t ∈ (T : Subgroup Q) := SetLike.coe_mem _
  have hTunique : ∀ w ∈ (T : Subgroup Q), orderOf w = 2 → w = t := by
    intro w hw hw2
    have h1 : orderOf (e ⟨w, hw⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw2]
    have h2 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hm _).1 h1
    rw [htdef, ← h2, MulEquiv.symm_apply_apply]
  obtain ⟨-, hcen⟩ := CFSG.Adapters.brauer_suzuki n hn T ⟨e⟩ t htT ht2
  have hOcen : CFSG.oddCore Q ≤ center Q := by
    rcases quasisimple_normal_subgroups hQ (inferInstance : (CFSG.oddCore Q).Normal) with
      h | h
    · exact absurd (h ▸ mem_top t) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ht2)
    · exact h
  have htZ : t ∈ center Q := by
    have hbar : (QuotientGroup.mk t : Q ⧸ center Q) ∈ center (Q ⧸ center Q) := by
      rw [mem_center_iff]
      intro gbar
      induction gbar using QuotientGroup.induction_on with | H g => ?_
      have h1 := mem_center_iff.1 hcen (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      have h2 := hOcen h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact h2
    obtain ⟨-, hsimple, a, b, hab⟩ := hQ
    have hZ : center (Q ⧸ center Q) = ⊥ := by
      rcases (inferInstance : (center (Q ⧸ center Q)).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        apply hab
        have hb : b ∈ center (Q ⧸ center Q) := h ▸ mem_top b
        exact mem_center_iff.1 hb a
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hbar
    exact hbar
  have hall : ∀ z : Q, orderOf z = 2 → z = t := by
    intro z hz
    have hzp : IsPGroup 2 (zpowers z) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hz, pow_one]
    obtain ⟨P, hP⟩ := hzp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q T P
    have hzP : z ∈ (P : Subgroup Q) := hP (mem_zpowers z)
    rw [← hg] at hzP
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hzP
    have hw2 : orderOf w = 2 := by
      rw [MulAut.smul_def, MulEquiv.orderOf_eq] at hz
      exact hz
    rw [hTunique w hw hw2, MulAut.smul_def, MulAut.conj_apply]
    rw [mem_center_iff] at htZ
    rw [htZ g, mul_inv_cancel_right]
  refine ⟨heven, ⟨t, ht2, fun z hz => hall z hz⟩, fun z hz => hall z hz ▸ htZ, hquat⟩

end CFSG.LocalAnalysis.ComponentInitial
