module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Abstract

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem a2l_finite_linearEquiv [Finite V] : Finite (V ≃ₗ[K] V) :=
  Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective

theorem a2l_coords_eq_zero (F : Frame Q) {x : V} (h1 : polar Q x F.f₁ = 0)
    (h2 : polar Q x F.f₂ = 0) (h3 : polar Q x F.e₂ = 0) (h4 : polar Q x F.e₁ = 0) :
    F.coords x = 0 := by
  rw [Frame.coords_apply, h1, h2, h3, h4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem a2l_La_neg_one_not_scalar (h2 : (2 : K) ≠ 0) (F : Frame Q) {v : V} (hv0 : v ≠ 0)
    (hv : F.coords v = 0) : F.La (-1) ∉ scalars K V := by
  intro hmem
  obtain ⟨c, hc⟩ := mem_scalars.1 hmem
  have h1 : c = 1 := by
    have := hc v
    rw [F.La_neg_one_apply, hv, map_zero, smul_zero, sub_zero] at this
    have h' : (1 - c) • v = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
    have := (smul_eq_zero.1 h').resolve_right hv0
    linear_combination -this
  have hw0 : F.incl 1 ≠ 0 := by
    intro h
    have := F.coords_incl (1 : Matrix (Fin 2) (Fin 2) K)
    rw [h, map_zero] at this
    have h' := congrFun (congrFun this 0) 0
    simp at h'
  have h3 : c = -1 := by
    have := hc (F.incl 1)
    rw [F.La_neg_one_apply, F.coords_incl] at this
    have h' : (c + 1) • F.incl 1 = 0 := by
      rw [add_smul, one_smul, ← this]
      module
    have := (smul_eq_zero.1 h').resolve_right hw0
    linear_combination this
  apply h2
  rw [h1] at h3
  linear_combination h3

end Abstract

section Datum

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Finite V]
  {Q : QuadraticForm K V}

theorem a2lDatum_projElementary_of_frame (hodd : Odd (Nat.card K)) (h9 : 9 ≤ Nat.card K)
    (F : Frame Q) {v : V} (hv0 : v ≠ 0) (hv : F.coords v = 0) :
    a2lDatum (ProjElementary Q) := by
  haveI : Finite (V ≃ₗ[K] V) := a2l_finite_linearEquiv
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hfund : IsFundamental Q F.La.range (F.La (-1)) := IsFundamental.of_frame F
  have hLE : F.La.range ≤ elementaryGroup Q := hfund.le_elementaryGroup
  let t : elementaryGroup Q := ⟨F.La (-1), hLE hfund.mem⟩
  let J : Subgroup (elementaryGroup Q) := F.La.range.subgroupOf (elementaryGroup Q)
  haveI := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ : ∃ s ⊆ (Finset.univ : Finset K), s.card = 4 :=
    Finset.exists_subset_card_eq (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  have hq : CFSG.IsQuasisimple SL(2, K) := CFSG.RankThree.Classical.isQuasisimple_SL2 ⟨s, hs⟩
  obtain ⟨eL⟩ := hfund.nonempty_mulEquiv
  let eJ : SL(2, K) ≃* J := eL.trans (Subgroup.subgroupOfEquivOfLe hLE).symm
  have hN : HarrisLit.IsSLTwoOver (Nat.card K) ↥J :=
    ⟨K, inferInstance, inferInstance, (Nat.card_eq_fintype_card).symm, ⟨eJ.symm⟩⟩
  refine a2lDatum_of_block (P := elementaryGroup Q) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hodd (by omega) (t := t) (J := J) (N := J)
    (Subtype.ext F.La_neg_one_mul_self) ?_ le_rfl ⟨-1, rfl⟩ ?_ ?_
    (CFSG.IsQuasisimple.of_mulEquiv eJ.symm hq) ?_ hN (a2l_typU_of_isSLTwoOver hodd h9 hN)
  · intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (commute_of_mem_scalars hx y.1).symm
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact a2l_La_neg_one_not_scalar h2 F hv0 hv h
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1
      (hfund.le_centralizer (Subgroup.mem_subgroupOf.1 hx)) _ (Set.mem_singleton _))
  · have h1 : CFSG.Assembly.IsSubnormal F.La.range (centralizerΩ Q (F.La (-1))) :=
      (CFSG.Assembly.IsSubnormal.iff_subgroupOf hfund.le_centralizerΩ).2
        (hfund.isSubnormal hodd (by omega))
    have h3 := h1.comap (elementaryGroup Q).subtype
    have hc : (centralizerΩ Q (F.La (-1))).comap (elementaryGroup Q).subtype =
        centralizer ({t} : Set (elementaryGroup Q)) := by
      ext x
      rw [Subgroup.mem_comap, centralizerΩ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨-, hx⟩ y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subtype.ext (hx _ (Set.mem_singleton _))
      · intro hx
        refine ⟨x.2, fun y hy => ?_⟩
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact congrArg Subtype.val (hx t (Set.mem_singleton _))
    rw [hc] at h3
    exact h3
  · intro x hx hπ
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hπ
    obtain ⟨c, hc⟩ := mem_scalars.1 hπ
    obtain ⟨A, hA⟩ := Subgroup.mem_subgroupOf.1 hx
    have hxv : (x : V ≃ₗ[K] V) v = v := by
      rw [← hA]
      exact F.La_apply_of_coords_eq_zero A hv
    have hc1 : c = 1 := by
      have := hc v
      rw [hxv] at this
      have h' : (1 - c) • v = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
      have := (smul_eq_zero.1 h').resolve_right hv0
      linear_combination -this
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    have h1 : (x : V ≃ₗ[K] V) w = w := by rw [hc w, hc1, one_smul]
    exact h1

theorem a2lDatum_projElementary_of_pairs (hodd : Odd (Nat.card K)) (h9 : 9 ≤ Nat.card K)
    {P P' P'' : HypPair Q} (h : P.Orth P') (h0 : P''.Orth P) (h1 : P''.Orth P') :
    a2lDatum (ProjElementary Q) :=
  a2lDatum_projElementary_of_frame hodd h9 (⟨P, P', h⟩ : Frame Q) P''.e_ne_zero
    (a2l_coords_eq_zero (⟨P, P', h⟩ : Frame Q) h0.ef h1.ef h1.ee h0.ee)

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
