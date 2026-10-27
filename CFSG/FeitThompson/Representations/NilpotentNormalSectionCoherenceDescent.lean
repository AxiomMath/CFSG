module

public import CFSG.FeitThompson.Representations.CentralSectionThresholdWeightedCoherence
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.ChiefSectionsCentralNilpotent
import CFSG.FeitThompson.Foundations.SibleySqrtExtensionInequality
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientPrimeCommutator
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NilpotentSectionCoherence

open NormalInducedFamily WeightedFeitExtension CentralSectionCoherence
open Subgroup QuotientGroup

variable {L : Type*} [Group L]

theorem two_mul_mul_mul_sqrt_lt_mul_sub_one {e n t : ℝ} (hn : 2 * e * Real.sqrt n < n - 1)
    (ht : 1 ≤ t) : 2 * (t * e) * Real.sqrt n < n * t - 1 := by
  have h1 : t * (2 * e * Real.sqrt n) < t * (n - 1) := mul_lt_mul_of_pos_left hn (by linarith)
  nlinarith

theorem relIndex_ne_zero [Finite L] (A B : Subgroup L) : A.relIndex B ≠ 0 := by
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem commutator_le_of_forall_normal_not_lt_lt_of_isNilpotent_quotient [Finite L]
    {M H A B : Subgroup L} [M.Normal] [A.Normal] [B.Normal] (hH : H.Normal)
    (hnil : Group.IsNilpotent (↥H ⧸ M.subgroupOf H)) (hMB : M ≤ B) (hAH : A ≤ H) (hBA : B < A)
    (hchief : ∀ J : Subgroup L, J.Normal → B < J → ¬J < A) : ⁅H, A⁆ ≤ B := by
  have _ := hH
  have _ := hnil
  have hker : (mk' M).ker = M := ker_mk' M
  have hcomapmap : ∀ J : Subgroup L, M ≤ J → comap (mk' M) (map (mk' M) J) = J := fun J hJ => by
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hJ]
  have hnilbar : Group.IsNilpotent ↥(map (mk' M) H) :=
    Group.nilpotent_of_mulEquiv (subgroupQuotientEquivMapMk' H M)
  have hBAbar : map (mk' M) B < map (mk' M) A := by
    refine lt_of_le_of_ne (Subgroup.map_mono hBA.le) fun h => hBA.ne ?_
    rw [← hcomapmap B hMB, ← hcomapmap A (hMB.trans hBA.le), h]
  have hchiefbar : ∀ J : Subgroup (L ⧸ M), J.Normal → map (mk' M) B < J →
      ¬J < map (mk' M) A := by
    intro J hJ hBJ hJA
    have hmapcomap : map (mk' M) (comap (mk' M) J) = J :=
      Subgroup.map_comap_eq_self_of_surjective (mk'_surjective M) J
    have hBlt : B < comap (mk' M) J := by
      refine lt_of_le_of_ne ?_ fun h => hBJ.ne (by rw [h, hmapcomap])
      rw [← hcomapmap B hMB]
      exact Subgroup.comap_mono hBJ.le
    have hJltA : comap (mk' M) J < A := by
      refine lt_of_le_of_ne ?_ fun h => hJA.ne (by rw [← hmapcomap, h])
      rw [← hcomapmap A (hMB.trans hBA.le)]
      exact Subgroup.comap_mono hJA.le
    exact hchief _ (hJ.comap (mk' M)) hBlt hJltA
  have hkey := commutator_le_of_forall_normal_not_lt_lt (L := L ⧸ M)
    (H := map (mk' M) H) (A := map (mk' M) A) (B := map (mk' M) B)
    inferInstance hnilbar (Subgroup.map_mono hAH) hBAbar hchiefbar
  calc ⁅H, A⁆ ≤ comap (mk' M) (map (mk' M) ⁅H, A⁆) := Subgroup.le_comap_map _ _
    _ ≤ comap (mk' M) (map (mk' M) B) := Subgroup.comap_mono (by
        rw [Subgroup.map_commutator]; exact hkey)
    _ = B := hcomapmap B hMB

theorem map_subgroupOf_le_center_of_isNilpotent_quotient [Finite L]
    {M H A B : Subgroup L} [M.Normal] [A.Normal] [B.Normal] (hH : H.Normal)
    (hnil : Group.IsNilpotent (↥H ⧸ M.subgroupOf H)) (hMB : M ≤ B) (hAH : A ≤ H) (hBA : B < A)
    (hchief : ∀ J : Subgroup L, J.Normal → B < J → ¬J < A) :
    (A.subgroupOf H).map (mk' (B.subgroupOf H)) ≤ Subgroup.center (↥H ⧸ B.subgroupOf H) :=
  (map_subgroupOf_le_center_iff hAH).2
    (commutator_le_of_forall_normal_not_lt_lt_of_isNilpotent_quotient hH hnil hMB hAH hBA hchief)

section Main

variable {G : Type*} [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {K M H H1 : Subgroup L}

omit [Fintype G] in
theorem kerLayerIndFam_union_eq_of_le {A A' : Subgroup L} (h : A' ≤ A) :
    kerLayerIndFam A K ∪ kerLayerIndFam A' K = kerLayerIndFam A' K :=
  Set.union_eq_self_of_subset_left (kerLayerIndFam_mono h)

private theorem isCoherent_aux (hc : IsSubcoherent S tau R) [K.Normal] [Group.IsSolvable ↥K]
    [M.Normal] (hH : H.Normal)
    (hnil : Group.IsNilpotent (↥H ⧸ M.subgroupOf H)) (hH1H : H1 ≤ H) (hHK : H ≤ K)
    (hthr : 4 * K.index ^ 2 + 1 < H1.relIndex H)
    (hMS : kerLayerIndFam M K ⊆ (S : Set (L → ℂ))) :
    ∀ (n : ℕ) (A : Subgroup L), A.Normal → ∀ hMA : M ≤ A, A ≤ H1 → Nat.card ↥A ≤ n →
      IsCoherent (kerLayerIndFam A K) (subTauHom hc ((kerLayerIndFam_mono hMA).trans hMS)) →
      IsCoherent (kerLayerIndFam M K) (subTauHom hc hMS) := by
  intro n
  induction n with
  | zero =>
    intro A _ _ _ hcard _
    have : 0 < Nat.card ↥A := Nat.card_pos
    omega
  | succ n ih =>
    intro A hAn hMA hAH1 hcard hcohA
    have _ := hAn
    rcases eq_or_lt_of_le hMA with rfl | hlt
    · exact hcohA
    obtain ⟨B, hMB, hBmax⟩ := Finite.exists_le_maximal
      (p := fun J : Subgroup L => J.Normal ∧ M ≤ J ∧ J < A) (a := M)
      ⟨‹M.Normal›, le_rfl, hlt⟩
    obtain ⟨hBn, -, hBA⟩ := hBmax.1
    have _ := hBn
    have hchief : ∀ J : Subgroup L, J.Normal → B < J → ¬J < A := fun J hJ hBJ hJA =>
      absurd (hBmax.2 ⟨hJ, hMB.trans hBJ.le, hJA⟩ hBJ.le) hBJ.not_ge
    have hAH : A ≤ H := hAH1.trans hH1H
    have hnA : 4 * K.index ^ 2 + 1 < A.relIndex H := by
      have h := Subgroup.relIndex_mul_relIndex A H1 H hAH1 hH1H
      have h1 : 1 ≤ A.relIndex H1 := Nat.one_le_iff_ne_zero.2 (relIndex_ne_zero _ _)
      have : H1.relIndex H ≤ A.relIndex H := by
        rw [← h]
        exact Nat.le_mul_of_pos_left _ h1
      omega
    have hAltH : A < H := by
      have hnot : ¬H ≤ A := fun hHA => by
        have := Subgroup.relIndex_eq_one.2 hHA
        omega
      exact lt_of_le_of_ne hAH fun h => hnot h.ge
    have hAK : A < K := lt_of_lt_of_le hAltH hHK
    have hcomm : ⁅A, H⁆ ≤ B := by
      rw [Subgroup.commutator_comm]
      exact commutator_le_of_forall_normal_not_lt_lt_of_isNilpotent_quotient hH hnil hMB hAH
        hBA hchief
    have hthrR : 2 * (H.index : ℝ) * Real.sqrt (A.relIndex H) < (A.relIndex K : ℝ) - 1 := by
      have hHidx : H.index = H.relIndex K * K.index := (Subgroup.relIndex_mul_index hHK).symm
      have hAidx : A.relIndex K = A.relIndex H * H.relIndex K :=
        (Subgroup.relIndex_mul_relIndex A H K hAH hHK).symm
      have ht : 1 ≤ (H.relIndex K : ℝ) := by
        have := Nat.one_le_iff_ne_zero.2 (relIndex_ne_zero H K)
        exact_mod_cast this
      have hstep := two_mul_mul_mul_sqrt_lt_mul_sub_one (e := (K.index : ℝ))
        (n := (A.relIndex H : ℝ)) (t := (H.relIndex K : ℝ))
        (two_mul_mul_sqrt_lt_sub_one_of_lt hnA) ht
      rw [hHidx, hAidx]
      push_cast
      linarith
    have hcohB := isCoherent_kerLayerIndFam_of_lt hc (A := A) (B := B) (D := A) (C := H)
      hAK hBA.le hAH hHK hcomm ((kerLayerIndFam_mono hMA).trans hMS)
      ((kerLayerIndFam_mono hMB).trans hMS)
      (Set.union_subset ((kerLayerIndFam_mono hMA).trans hMS)
        ((kerLayerIndFam_mono hMB).trans hMS)) hcohA hthrR
    refine ih B hBn hMB (hBA.le.trans hAH1) ?_ hcohB
    have := natCard_lt_natCard_of_lt hBA
    omega

theorem isCoherent_kerLayerIndFam_of_isNilpotent_quotient (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [M.Normal] [H1.Normal] (hH : H.Normal)
    (hnil : Group.IsNilpotent (↥H ⧸ M.subgroupOf H))
    (hMH1 : M ≤ H1) (hH1H : H1 ≤ H) (hHK : H ≤ K)
    (hthr : 4 * K.index ^ 2 + 1 < H1.relIndex H)
    (hMS : kerLayerIndFam M K ⊆ (S : Set (L → ℂ)))
    (hcoh1 : IsCoherent (kerLayerIndFam H1 K)
      (subTauHom hc ((kerLayerIndFam_mono hMH1).trans hMS))) :
    IsCoherent (kerLayerIndFam M K) (subTauHom hc hMS) :=
  isCoherent_aux hc hH hnil hH1H hHK hthr hMS (Nat.card ↥H1) H1 ‹H1.Normal› hMH1 le_rfl le_rfl
    hcoh1

theorem isCoherent_kerLayerIndFam_union_of_isNilpotent_quotient (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [M.Normal] [H1.Normal] (hH : H.Normal)
    (hnil : Group.IsNilpotent (↥H ⧸ M.subgroupOf H))
    (hMH1 : M ≤ H1) (hH1H : H1 ≤ H) (hHK : H ≤ K)
    (hthr : 4 * K.index ^ 2 + 1 < H1.relIndex H)
    (hMS : kerLayerIndFam M K ⊆ (S : Set (L → ℂ)))
    (hUS : kerLayerIndFam H1 K ∪ kerLayerIndFam M K ⊆ (S : Set (L → ℂ)))
    (hcoh1 : IsCoherent (kerLayerIndFam H1 K)
      (subTauHom hc ((kerLayerIndFam_mono hMH1).trans hMS))) :
    IsCoherent (kerLayerIndFam H1 K ∪ kerLayerIndFam M K) (subTauHom hc hUS) :=
  isCoherent_of_eq (kerLayerIndFam_union_eq_of_le hMH1).symm (subTauHom_congr hc hMS hUS)
    (isCoherent_kerLayerIndFam_of_isNilpotent_quotient hc hH hnil hMH1 hH1H hHK hthr hMS hcoh1)

theorem isCoherent_kerLayerIndFam_restrict (hc : IsSubcoherent S tau R) (hMH1 : M ≤ H1)
    (hMS : kerLayerIndFam M K ⊆ (S : Set (L → ℂ)))
    (h : IsCoherent (kerLayerIndFam M K) (subTauHom hc hMS)) :
    IsCoherent (kerLayerIndFam H1 K) (subTauHom hc ((kerLayerIndFam_mono hMH1).trans hMS)) :=
  isCoherent_of_subset hc (kerLayerIndFam_mono hMH1) hMS _ h

theorem isCoherent_kerLayerIndFam_of_isNilpotent_quotient_of_eq_bot (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [M.Normal] [H1.Normal]
    (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K) (hH : H.Normal)
    (hnil : Group.IsNilpotent (↥H ⧸ M.subgroupOf H))
    (hMH1 : M ≤ H1) (hH1H : H1 ≤ H) (hHK : H ≤ K)
    (hthr : 4 * K.index ^ 2 + 1 < H1.relIndex H)
    (hcoh1 : IsCoherent (kerLayerIndFam H1 K)
      (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS H1))) :
    IsCoherent (kerLayerIndFam M K) (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS M)) :=
  isCoherent_kerLayerIndFam_of_isNilpotent_quotient hc hH hnil hMH1 hH1H hHK hthr _
    (isCoherent_of_eq rfl (subTauHom_congr hc _ _) hcoh1)

end Main

end NilpotentSectionCoherence

end CFSG.FeitThompson
