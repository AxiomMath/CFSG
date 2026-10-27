module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU2
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

theorem card_uU_two : Nat.card (uU h 2) = r ^ f * ((r ^ f + 1) * ((r ^ f) ^ 2 - 1)) := by
  have := h.finite
  have := Fintype.ofFinite K
  have hq : Fintype.card K = (r ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, h.card_eq_sq]
  have e := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hq (n := 2) (by norm_num)
  rw [statedGU_eq_uU h] at e
  have hq1 : 1 ≤ (r ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos h.prime.pos _)
  zify [hq1]
  rw [e, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num),
    Finset.prod_pair (by norm_num)]
  push_cast
  ring

theorem card_uU_three :
    Nat.card (uU h 3) = (r ^ f) ^ 3 * ((r ^ f + 1) * ((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 + 1)) := by
  have := h.finite
  have := Fintype.ofFinite K
  have hq : Fintype.card K = (r ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, h.card_eq_sq]
  have e := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hq (n := 3) (by norm_num)
  rw [statedGU_eq_uU h] at e
  have hq1 : 1 ≤ (r ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos h.prime.pos _)
  zify [hq1]
  rw [e, show Finset.Icc 1 3 = {1, 2, 3} by rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton, false_or, not_false_eq_true,
    Finset.prod_insert, Finset.prod_singleton, Nat.reduceEqDiff]
  push_cast
  ring

include h in
theorem card_statedSU_three_int :
    (Nat.card (StatedSU 3 (r ^ f) K) : ℤ) =
      ((r ^ f : ℕ) : ℤ) ^ 3 * ((((r ^ f : ℕ) : ℤ) ^ 2 - 1) * (((r ^ f : ℕ) : ℤ) ^ 3 + 1)) := by
  rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 3) (by norm_num),
    show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

@[expose] noncomputable def blkL (k m : ℕ) (hkm : k < m) :
    Subgroup (StatedProj (StatedSU m (r ^ f) K)) :=
  ((projH (StatedSU m (r ^ f) K)).comp (blkSU h 0 (by omega : 0 + k ≤ m))).range

@[expose] noncomputable def blkLEquiv (k m : ℕ) (hkm : k < m) :
    StatedSU k (r ^ f) K ≃* ↥(blkL h k m hkm) :=
  MonoidHom.ofInjective (proj_blkSU_injective h (by omega : 0 + k ≤ m) hkm)

include h in
theorem ne_top_of_card {m : ℕ} (hm : 1 ≤ m) {L : Subgroup (StatedProj (StatedSU m (r ^ f) K))}
    (hL : m * Nat.card L < Nat.card (StatedSU m (r ^ f) K)) : L ≠ ⊤ := by
  intro htop
  have e := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (r ^ f) K))
  rw [(CFSG.LinearGroups.unitary_scalar_kernel h.prime h.card_eq_sq hm).2.2] at e
  rw [htop, Subgroup.card_top] at hL
  have hg := Nat.gcd_le_left (r ^ f + 1) (show 0 < m by omega)
  have h1 : Nat.card (StatedSU m (r ^ f) K) ≤
      Nat.card (StatedProj (StatedSU m (r ^ f) K)) * m := by
    rw [e]
    exact Nat.mul_le_mul_left _ hg
  rw [mul_comm] at h1
  omega

theorem comp5Concl_of_le_normalizer {k m p : ℕ} [Fact p.Prime] [Fact r.Prime] (hkm : k < m)
    {Mt : Subgroup (StatedSU m (r ^ f) K)} (hidx : ¬ p ∣ Mt.index)
    (hMt : Mt ≤ normalizer ((blkSU h 0 (by omega : 0 + k ≤ m)).range : Set _))
    (hq : IsQuasisimple ↥(blkL h k m hkm))
    (hc : OddChev r (↥(blkL h k m hkm) ⧸ center ↥(blkL h k m hkm)))
    (hrL : r ∣ Nat.card (blkL h k m hkm))
    (hcard : m * Nat.card (StatedSU k (r ^ f) K) < Nat.card (StatedSU m (r ^ f) K))
    {y : StatedProj (StatedSU m (r ^ f) K)} (hy : orderOf y = p) (hyr : RFree r y) :
    Comp5Concl r y := by
  have := h.finite
  set π := projH (StatedSU m (r ^ f) K) with hπ
  have hL : blkL h k m hkm = (blkSU h 0 (by omega : 0 + k ≤ m)).range.map π :=
    MonoidHom.range_comp _ _
  have hM : ¬ p ∣ (Mt.map π).index := fun hd =>
    hidx (hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hML : Mt.map π ≤ normalizer (blkL h k m hkm : Set _) := by
    rw [hL]
    exact (Subgroup.map_mono hMt).trans (Subgroup.le_normalizer_map π)
  have hLt : blkL h k m hkm ≠ ⊤ := ne_top_of_card h (by omega) (by
    rw [← Nat.card_congr (blkLEquiv h k m hkm).toEquiv]
    exact hcard)
  exact comp5Concl_of_block hM hML hLt hq hc hrL hy hyr

end CFSG.OddStandard.GH71.S55.C5U
