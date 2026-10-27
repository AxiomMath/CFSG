module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Perfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Position
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.E6Pilot (IsAutConjIn)
open scoped MatrixGroups

variable {K : Type} [Field K]

section OrderThree

theorem mem_zpowers_zThreeSL_of_orderOf_eq_three [Finite K] (hK : Nat.card K = 2)
    {A : SL(2, K)} (hA : orderOf A = 3) : A ∈ zpowers (zThreeSL (K := K)) := by
  set N := zpowers (zThreeSL (K := K)) with hN
  have hN3 : Nat.card N = 3 := by rw [hN, Nat.card_zpowers, orderOf_zThreeSL]
  have hG : Nat.card SL(2, K) = 6 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hidx : N.index = 2 := by
    have h := N.card_mul_index
    rw [hN3, hG] at h
    omega
  have : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have h2 : (QuotientGroup.mk A : SL(2, K) ⧸ N) ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := SL(2, K) ⧸ N) (x := QuotientGroup.mk A)
    rwa [← Subgroup.index, hidx] at h
  have h3 : (QuotientGroup.mk A : SL(2, K) ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hA, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h1 : (QuotientGroup.mk A : SL(2, K) ⧸ N) = 1 := by
    calc (QuotientGroup.mk A : SL(2, K) ⧸ N) =
        (QuotientGroup.mk A : SL(2, K) ⧸ N) ^ 3 * ((QuotientGroup.mk A : SL(2, K) ⧸ N) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  exact (QuotientGroup.eq_one_iff A).1 h1

variable {m : ℕ}

theorem mem_nsTorusSp_of_mem_longRootSp2 [Finite K] (hK : Nat.card K = 2) {k : Fin m}
    {y : StatedSp m K} (hy : y ∈ longRootSp2 K m k) (h3 : orderOf y = 3) :
    y ∈ nsTorusSp K k := by
  obtain ⟨A, rfl⟩ := hy
  have hA : orderOf A = 3 := by rwa [orderOf_injective _ (longBlock_injective k)] at h3
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (mem_zpowers_zThreeSL_of_orderOf_eq_three hK hA)
  exact ⟨j, by simp [nsElt, map_zpow]⟩

theorem eq_nsTorusSp_of_le_longRootSp2 [Finite K] (hK : Nat.card K = 2) {k : Fin m}
    {Y : Subgroup (StatedSp m K)} (hY : Y ≤ longRootSp2 K m k) (h3 : Nat.card Y = 3) :
    Y = nsTorusSp K k := by
  have hle : Y ≤ nsTorusSp K k := by
    intro y hy
    have hdvd : orderOf y ∣ 3 := h3 ▸ Y.orderOf_dvd_natCard hy
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1]
      exact one_mem _
    · exact mem_nsTorusSp_of_mem_longRootSp2 hK (hY hy) h1
  have : Finite (StatedSp m K) := by
    have : Finite (GL (Fin m ⊕ Fin m) K) := inferInstance
    exact Subtype.finite
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_nsTorusSp, h3])

end OrderThree

section Centralizer

variable {m : ℕ} [Finite K] [CharP K 2]

theorem perfectCore_centralizer_nsTorusSp (hK : Nat.card K = 2) (hm : 3 ≤ m) (k : Fin (m + 1)) :
    perfectCore (centralizer (nsTorusSp K k : Set (StatedSp (m + 1) K))) = complSp K k := by
  have : Finite (StatedSp (m + 1) K) := by
    have : Finite (GL (Fin (m + 1) ⊕ Fin (m + 1)) K) := inferInstance
    exact Subtype.finite
  rw [(centralizer_nsTorusSp hK k).1]
  refine F4Pilot.perfectCore_sup_eq_of_le_centralizer (nsTorusSp_le_centralizer_self k) ?_
    (commutator_complSp_two hK hm k)
  intro x hx
  rw [mem_centralizer_iff]
  intro d hd
  exact (mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k hd) x hx).symm

end Centralizer

section F56

variable {n : ℕ} [Finite K] [CharP K 2]

theorem card_map_subgroupOf_of_mulEquiv {C : Type*} [Group C] {M M' H : Subgroup C} (hHM : H ≤ M)
    (ι : M ≃* M') :
    Nat.card (((H.subgroupOf M).map ι.toMonoidHom).map M'.subtype) = Nat.card H := by
  rw [Subgroup.card_map_of_injective M'.subtype_injective,
    Subgroup.card_map_of_injective ι.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv

omit [CharP K 2] in
theorem exists_conj_of_isAutConjIn_nsTorusSp (hK : Nat.card K = 2) {m : ℕ}
    {M : Subgroup (StatedSp m K)} {k : Fin m} (hM : IsAutConjIn M (longRootSp2 K m k))
    (hJM : longRootSp2 K m k ≤ M) (ι : M ≃* M) :
    ∃ s ∈ M, (((nsTorusSp K k).subgroupOf M).map ι.toMonoidHom).map M.subtype =
      (nsTorusSp K k).map (MulAut.conj s).toMonoidHom := by
  obtain ⟨s, hsM, hs⟩ := hM ι
  refine ⟨s, hsM, ?_⟩
  set Y := (((nsTorusSp K k).subgroupOf M).map ι.toMonoidHom).map M.subtype with hYdef
  have hXJ : nsTorusSp K k ≤ longRootSp2 K m k := nsTorusSp_le_longRootSp2 k
  have hXM : nsTorusSp K k ≤ M := hXJ.trans hJM
  have hYJ : Y ≤ (longRootSp2 K m k).map (MulAut.conj s).toMonoidHom := by
    rw [← hs, hYdef]
    exact map_mono (map_mono fun x hx => mem_subgroupOf.2 (hXJ (mem_subgroupOf.1 hx)))
  obtain ⟨Y', hY'J, hY'⟩ := F4Pilot.exists_le_map_eq_of_le_map (MulAut.conj s) hYJ
  have hY3 : Nat.card Y = 3 := by
    rw [hYdef, card_map_subgroupOf_of_mulEquiv hXM, card_nsTorusSp]
  have hY'3 : Nat.card Y' = 3 := by
    rw [← hY3, ← hY', Subgroup.card_map_of_injective (MulAut.conj s).injective]
  rw [← hY', eq_nsTorusSp_of_le_longRootSp2 hK hY'J hY'3]

theorem nonempty_perfectCore_centralizer_of_isAutConjIn (hK : Nat.card K = 2) (hn : 1 ≤ n)
    {M : Subgroup (StatedSp (n + 3) K)} (hM : IsAutConjIn M (longRootSp2 K (n + 3) 0))
    (hJM : longRootSp2 K (n + 3) 0 ≤ M) (ι : M ≃* M) :
    Nonempty (perfectCore (centralizer
      ((((nsTorusSp K (0 : Fin (n + 3))).subgroupOf M).map ι.toMonoidHom).map M.subtype :
        Set (StatedSp (n + 3) K))) ≃* complSp K (0 : Fin (n + 3))) := by
  have : Finite (StatedSp (n + 3) K) := by
    have : Finite (GL (Fin (n + 3) ⊕ Fin (n + 3)) K) := inferInstance
    exact Subtype.finite
  obtain ⟨s, -, hs⟩ := exists_conj_of_isAutConjIn_nsTorusSp hK hM hJM ι
  rw [hs]
  have h := F4Pilot.nonempty_perfectCore_centralizer_map_mulAut (MulAut.conj s)
    (nsTorusSp K (0 : Fin (n + 3)))
  rw [perfectCore_centralizer_nsTorusSp hK (m := n + 2) (by omega)] at h
  exact h

end F56

end CFSG.SeitzReduction.SymplecticPilot
