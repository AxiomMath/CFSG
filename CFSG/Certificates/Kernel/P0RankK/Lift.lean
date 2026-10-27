
module

public import CFSG.Certificates.Kernel.P0RankK.PmulFacts

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.KC.BvecLoop CFSG.KC.P0Vis

theorem layer_liftPm (hbd : bdOK p0Data = true) {E : Subgroup Dfull} (hE : IsElemAbelian 2 E)
    (ds ks : List ℕ) (hds : ∀ δ ∈ ds, δ ∈ layerD E) (hks : ∀ κ ∈ ks, κ ∈ layerW E) :
    ∃ X, LiftPm p0Data ds ks X := by
  classical
  have hgetW : ∀ j (hj : j < ks.length), ks.getD j 0 ∈ ks := by
    intro j hj
    rw [List.getD_eq_getElem ks 0 hj]
    exact List.getElem_mem hj
  have hgetD : ∀ i (hi : i < ds.length), ds.getD i 0 ∈ ds := by
    intro i hi
    rw [List.getD_eq_getElem ds 0 hi]
    exact List.getElem_mem hi
  have hks_bound : ∀ j (hj : j < ks.length), ks.getD j 0 < 2 ^ 10 := by
    intro j hj
    exact Finset.mem_range.1 (Finset.mem_filter.1 (hks _ (hgetW j hj))).1
  have hds_bound : ∀ i (hi : i < ds.length), ds.getD i 0 < 2 ^ 16 := by
    intro i hi
    exact Finset.mem_range.1 (Finset.mem_filter.1 (hds _ (hgetD i hi))).1
  let g : ℕ → P0 := fun j =>
    if h : j < ks.length then
      Classical.choose ((Finset.mem_filter.1 (hks (ks.getD j 0) (hgetW j h))).2)
    else 1
  have hgE : ∀ j (hj : j < ks.length), (g j : Dfull) ∈ E := by
    intro j hj
    dsimp [g]
    rw [dif_pos hj]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hks (ks.getD j 0) (hgetW j hj))).2)).1
  have hgcoord : ∀ j (hj : j < ks.length),
      uCoord (g j) = Multiplicative.ofAdd (bvec 10 (ks.getD j 0)) := by
    intro j hj
    dsimp [g]
    rw [dif_pos hj]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hks (ks.getD j 0) (hgetW j hj))).2)).2
  have hexNF : ∀ j, ∃ p : ℕ × ℕ × ℕ, p.1 < 2 ^ 16 ∧ p.2.1 < 2 ^ 9 ∧ p.2.2 < 2 ^ 10 ∧
      (g j : Dfull) = lD p.1 * tD p.2.1 * uE p.2.2 := by
    intro j
    obtain ⟨σ, hσ, τ, hτ, κ, hκ, heq⟩ := exists_nf (g j).2
    exact ⟨(σ, τ, κ), hσ, hτ, hκ, heq⟩
  let p : ℕ → ℕ × ℕ × ℕ := fun j => Classical.choose (hexNF j)
  have hp : ∀ j, (p j).1 < 2 ^ 16 ∧ (p j).2.1 < 2 ^ 9 ∧ (p j).2.2 < 2 ^ 10 ∧
      (g j : Dfull) = lD (p j).1 * tD (p j).2.1 * uE (p j).2.2 :=
    fun j => Classical.choose_spec (hexNF j)
  have hκ_eq : ∀ j (hj : j < ks.length), (p j).2.2 = ks.getD j 0 := by
    intro j hj
    have hcoord := hgcoord j hj
    have hP0L : lD (p j).1 * tD (p j).2.1 ∈ Lgrp :=
      Lgrp.mul_mem (lD_mem_Lgrp (p j).1) (T9_le_Lgrp (tD_mem_T9 (p j).2.1))
    have hP : g j = (⟨lD (p j).1 * tD (p j).2.1, Lgrp_le_P0 hP0L⟩ : P0) *
        ⟨uE (p j).2.2, uE_mem_P0 (p j).2.2⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul]; exact (hp j).2.2.2)
    rw [hP, map_mul, (uCoord_eq_one_iff _).2 hP0L, uCoord_uE, one_mul] at hcoord
    have hb : bvec 10 (p j).2.2 = bvec 10 (ks.getD j 0) :=
      Multiplicative.ofAdd.injective hcoord
    exact bvec_inj (hp j).2.2.1 (hks_bound j hj) hb
  let y : ℕ → Lgrp := fun i =>
    if h : i < ds.length then
      Classical.choose ((Finset.mem_filter.1 (hds (ds.getD i 0) (hgetD i h))).2)
    else 1
  have hyE : ∀ i (hi : i < ds.length), (y i : Dfull) ∈ E := by
    intro i hi
    dsimp [y]
    rw [dif_pos hi]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hds (ds.getD i 0) (hgetD i hi))).2)).1
  have hysCoord : ∀ i (hi : i < ds.length),
      sCoord (y i) = Multiplicative.ofAdd (bvec 16 (ds.getD i 0)) := by
    intro i hi
    dsimp [y]
    rw [dif_pos hi]
    exact (Classical.choose_spec ((Finset.mem_filter.1 (hds (ds.getD i 0) (hgetD i hi))).2)).2
  have hexNFx : ∀ i, ∃ q : ℕ × ℕ, q.1 < 2 ^ 16 ∧ q.2 < 2 ^ 9 ∧
      (y i : Dfull) = lD q.1 * tD q.2 := by
    intro i
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := exists_lD_mul_tD (y i).2
    exact ⟨(σ, τ), hσ, hτ, heq⟩
  let q : ℕ → ℕ × ℕ := fun i => Classical.choose (hexNFx i)
  have hq : ∀ i, (q i).1 < 2 ^ 16 ∧ (q i).2 < 2 ^ 9 ∧
      (y i : Dfull) = lD (q i).1 * tD (q i).2 :=
    fun i => Classical.choose_spec (hexNFx i)
  have hδ_eq : ∀ i (hi : i < ds.length), (q i).1 = ds.getD i 0 := by
    intro i hi
    have hcoord := hysCoord i hi
    have hmemL : lD (q i).1 * tD (q i).2 ∈ Lgrp :=
      Lgrp.mul_mem (lD_mem_Lgrp (q i).1) (T9_le_Lgrp (tD_mem_T9 (q i).2))
    have hP : y i = (⟨lD (q i).1 * tD (q i).2, hmemL⟩ : Lgrp) :=
      Subtype.ext (hq i).2.2
    rw [hP, sCoord_lD_mul (hq i).1 (tD_mem_T9 (q i).2) hmemL] at hcoord
    have hb : bvec 16 (q i).1 = bvec 16 (ds.getD i 0) :=
      Multiplicative.ofAdd.injective hcoord
    exact bvec_inj (hq i).1 (hds_bound i hi) hb
  let X : ℕ → ℕ := fun n =>
    if h : n < ks.length then (p n).1
    else if h' : n - ks.length < ds.length then (q (n - ks.length)).2 else 0
  have hX1 : ∀ j (hj : j < ks.length), X j = (p j).1 := by
    intro j hj
    dsimp [X]
    rw [if_pos hj]
  have hX2 : ∀ i (hi : i < ds.length), X (ks.length + i) = (q i).2 := by
    intro i hi
    dsimp [X]
    rw [if_neg (by omega), if_pos (by simpa [Nat.add_sub_cancel_left] using hi),
      Nat.add_sub_cancel_left]
  refine ⟨X, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hX1 j hj]
    exact (hp j).1
  · intro i hi
    rw [hX2 i hi]
    exact (hq i).2.1
  · intro j hj
    rw [hX1 j hj, ← hκ_eq j hj]
    obtain ⟨t, hfact, hsb⟩ := pm_sq hbd (hp j).2.2.1
    exact sq_coord_eq hE (hgE j hj) (hp j).1 hsb (hp j).2.2.2 hfact
  · intro j k hjk hk
    rw [hX1 j (by omega), hX1 k hk, ← hκ_eq k hk, ← hκ_eq j (by omega)]
    obtain ⟨t, hfact, hsb⟩ := pm_comm hbd (hp j).2.2.1 (hp k).2.2.1
    exact comm_coord_eq hE (hgE j (by omega)) (hgE k hk) (hp j).1 (hp k).1 hsb
      (hp j).2.2.2 (hp k).2.2.2 hfact
  · intro i hi j hj
    rw [hX1 j hj, hX2 i hi, ← hκ_eq j hj, ← hδ_eq i hi]
    have hfix : actK p0Data.aCols (p j).2.2 (q i).1 = (q i).1 := by
      rw [hκ_eq j hj, hδ_eq i hi]
      exact actK_eq_of_mem_layerW hE _ (hks _ (hgetW j hj)) _ (hds _ (hgetD i hi))
    obtain ⟨hfact, hcb⟩ := pm_conj hbd (hp j).2.2.1 (hq i).1 hfix
    exact conj_coord_eq hE (hgE j hj) (hyE i hi) (hp j).1 (hq i).1 (hq i).2.1
      (hp j).2.2.2 (hq i).2.2 hfact hcb

end CFSG.Monster.B.TwoA.Sp8.WordRel
