module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import CFSG.GroupTheory.TwoWeightData
public import Certificates.Data.GH74.Ivk8Two
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.Certificates Certificates.Odd87F3 Certificates.Ivk8Weak
  Certificates.Ivk8Two CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GroupTheory.TwoWeights

section Spec

variable {n : ℕ}

theorem allDistinct_nodup {l : List Table} {lp : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) l lp) (hd : allDistinct n l = true) : lp.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons t g ts gs hab hr ih =>
    simp only [allDistinct, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hd
    refine List.nodup_cons.2 ⟨fun hg => ?_, ih hd.2⟩
    obtain ⟨s, hs, hrs⟩ := exists_of_mem_right_forall₂ hr hg
    have := (tblEq_eq_iff hab hrs).2 rfl
    rw [hd.1 s hs] at this
    exact Bool.false_ne_true this

theorem forall₂_flatMap_compT {W : List Table} {Wp : List (Equiv.Perm (Fin n))}
    (hW : List.Forall₂ (Rep n) W Wp) {V : List Table} {Vp : List (Equiv.Perm (Fin n))}
    (hV : List.Forall₂ (Rep n) V Vp) :
    List.Forall₂ (Rep n) (W.flatMap fun w => V.map (compT n w))
      (Wp.flatMap fun w => Vp.map (w * ·)) := by
  induction hW with
  | nil => exact .nil
  | cons hab _ ih =>
    exact List.rel_append (forall₂_map_comp hab hV) ih

theorem mem_flatMap_mul {G : Type*} [Group G] (B : Subgroup G) {Wp Vp : List G}
    (hW : ∀ w ∈ Wp, w ∈ B) (hV : ∀ v ∈ Vp, v ∈ B) :
    ∀ g ∈ Wp.flatMap (fun w => Vp.map (w * ·)), g ∈ B := by
  intro g hg
  simp only [List.mem_flatMap, List.mem_map] at hg
  obtain ⟨w, hw, v, hv, rfl⟩ := hg
  exact B.mul_mem (hW w hw) (hV v hv)

theorem two_spec (hn : n < 2 ^ 32) {gT : List Table} {gG : List (Equiv.Perm (Fin n))}
    (hgT : List.Forall₂ (Rep n) gT gG) {N : Subgroup (Equiv.Perm (Fin n))}
    (hgN : ∀ g ∈ gG, g ∈ N) {wa w₁ w₂ w₃ wx wy : List ℤ}
    (h : twoOKT n gT wa w₁ w₂ w₃ wx wy = true) :
    ∃ a u₁ u₂ u₃ x y : Equiv.Perm (Fin n), a ∈ N ∧ u₁ ∈ N ∧ u₂ ∈ N ∧ u₃ ∈ N ∧ x ∈ N ∧ y ∈ N ∧
      a ≠ 1 ∧ a = evalCodes gG wa ∧ Data a u₁ u₂ u₃ x y ∧
        128 ≤ Nat.card ↥(closure {u₁, u₂, u₃, a, x, y}) := by
  classical
  simp only [twoOKT, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hginv, htinv⟩, hrels⟩, hne1⟩, hlen⟩, hdist⟩ := h
  have hgI := forall₂_inv_of_invOK hgT hginv
  set a := evalCodes gG wa with ha
  set u₁ := evalCodes gG w₁ with hu₁
  set u₂ := evalCodes gG w₂ with hu₂
  set u₃ := evalCodes gG w₃ with hu₃
  set x := evalCodes gG wx with hx
  set y := evalCodes gG wy with hy
  set ts := twoTables n gT wa w₁ w₂ w₃ wx wy with hts
  have ra := rep_evalT hn hgT hgI wa
  have r₁ := rep_evalT hn hgT hgI w₁
  have r₂ := rep_evalT hn hgT hgI w₂
  have r₃ := rep_evalT hn hgT hgI w₃
  have rx := rep_evalT hn hgT hgI wx
  have ry := rep_evalT hn hgT hgI wy
  have hrep : List.Forall₂ (Rep n) ts [a, u₁, u₂, u₃, x, y] := by
    simp only [hts, twoTables]
    exact .cons ra (.cons r₁ (.cons r₂ (.cons r₃ (.cons rx (.cons ry .nil)))))
  have hrep4 : List.Forall₂ (Rep n) (ts.take 4) [a, u₁, u₂, u₃] := by
    simp only [hts, twoTables, List.take]
    exact .cons ra (.cons r₁ (.cons r₂ (.cons r₃ .nil)))
  have hrepi := forall₂_inv_of_invOK hrep htinv
  have haN : a ∈ N := evalCodes_mem N hgN wa
  have hu₁N : u₁ ∈ N := evalCodes_mem N hgN w₁
  have hu₂N : u₂ ∈ N := evalCodes_mem N hgN w₂
  have hu₃N : u₃ ∈ N := evalCodes_mem N hgN w₃
  have hxN : x ∈ N := evalCodes_mem N hgN wx
  have hyN : y ∈ N := evalCodes_mem N hgN wy
  have R : ∀ r ∈ dataRels, evalCodes [a, u₁, u₂, u₃, x, y] r.1 =
      evalCodes [a, u₁, u₂, u₃, x, y] r.2 := fun r hr =>
    (tblEq_eq_iff (rep_evalT hn hrep hrepi r.1) (rep_evalT hn hrep hrepi r.2)).1 (hrels r hr)
  have hane : a ≠ 1 := by
    intro h1
    have h2 : tblEq n (ts.headD (idT n)) (idT n) = true :=
      (tblEq_eq_iff (by simpa [hts, twoTables] using ra) (Rep.idT hn)).2 h1
    rw [h2] at hne1
    exact absurd hne1 (by decide)
  refine ⟨a, u₁, u₂, u₃, x, y, haN, hu₁N, hu₂N, hu₃N, hxN, hyN, hane, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [evalCodes] using R ([1, 1], []) (by decide +kernel)
    · simpa [evalCodes] using R ([2, 2], []) (by decide +kernel)
    · simpa [evalCodes] using R ([3, 3], []) (by decide +kernel)
    · simpa [evalCodes] using R ([4, 4], []) (by decide +kernel)
    · simpa [evalCodes] using R ([2, 3], [3, 2]) (by decide +kernel)
    · simpa [evalCodes] using R ([2, 4], [4, 2]) (by decide +kernel)
    · simpa [evalCodes] using R ([2, 1], [1, 2]) (by decide +kernel)
    · simpa [evalCodes] using R ([3, 4], [4, 3]) (by decide +kernel)
    · simpa [evalCodes] using R ([3, 1], [1, 3]) (by decide +kernel)
    · simpa [evalCodes] using R ([4, 1], [1, 4]) (by decide +kernel)
    · simpa [evalCodes] using R ([1, 5], [5, 1]) (by decide +kernel)
    · simpa [evalCodes] using R ([1, 6], [6, 1]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([5, 2], [2, 1, 5]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([5, 3], [4, 1, 5]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([5, 4], [3, 1, 5]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([-5, 2], [2, 1, -5]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([-5, 3], [4, 1, -5]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([-5, 4], [3, 1, -5]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([6, 2], [2, 6]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([6, 3], [3, 1, 6]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([6, 4], [2, 4, 1, 6]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([-6, 2], [2, -6]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([-6, 3], [3, 1, -6]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([-6, 4], [2, 4, 1, -6]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([5, 5], [1]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([6, 6], [1]) (by decide +kernel)
    · simpa [evalCodes, mul_assoc] using R ([5, 6, 5, 6, 5, 6, 5, 6], [1]) (by decide +kernel)
  ·
    set B : Subgroup (Equiv.Perm (Fin n)) := closure {u₁, u₂, u₃, a, x, y} with hB
    have hgsB : ∀ g ∈ [a, u₁, u₂, u₃, x, y], g ∈ B := by
      intro g hg
      apply Subgroup.subset_closure
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h | h <;> simp [h]
    have hW : List.Forall₂ (Rep n) (w8Words.map (evalT n ts (ts.map (invT n))))
        (w8Words.map (evalCodes [a, u₁, u₂, u₃, x, y])) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.2 fun w _ => rep_evalT hn hrep hrepi w
    have hV := forall₂_subprods hn hrep4
    have hL := forall₂_flatMap_compT hW hV
    set Lp : List (Equiv.Perm (Fin n)) := (w8Words.map (evalCodes [a, u₁, u₂, u₃, x, y])).flatMap
      fun w => (subprodsP [a, u₁, u₂, u₃]).map (w * ·) with hLp
    have hL' : List.Forall₂ (Rep n) (twoProds n ts) Lp := hL
    have hnodup : Lp.Nodup := allDistinct_nodup hL' hdist
    have hlen128 : Lp.length = 128 := by
      rw [← hL'.length_eq]
      exact hlen
    have hWB : ∀ w ∈ w8Words.map (evalCodes [a, u₁, u₂, u₃, x, y]), w ∈ B := by
      intro w hw
      obtain ⟨w', -, rfl⟩ := List.mem_map.1 hw
      exact evalCodes_mem B hgsB w'
    have hVB : ∀ v ∈ subprodsP [a, u₁, u₂, u₃], v ∈ B := by
      refine mem_subprodsP (fun b hb => hgsB b ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
      rcases hb with h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
        Or.inr (Or.inr (Or.inr (Or.inl h)))]
    have hmemB : ∀ g ∈ Lp, g ∈ B := mem_flatMap_mul B hWB hVB
    have hsub : (↑Lp.toFinset : Set (Equiv.Perm (Fin n))) ⊆ (B : Set (Equiv.Perm (Fin n))) :=
      fun g hg => hmemB g (List.mem_toFinset.1 hg)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hlen128] at h1
    have h2 : Nat.card ↥B = (B : Set (Equiv.Perm (Fin n))).ncard :=
      Nat.card_coe_set_eq (B : Set (Equiv.Perm (Fin n)))
    omega

theorem central_spec (hn : n < 2 ^ 32) {gT : List Table} {gG : List (Equiv.Perm (Fin n))}
    (hgT : List.Forall₂ (Rep n) gT gG) {w : List ℤ} (h : centralOKT n gT w = true) :
    ∀ g ∈ gG, evalCodes gG w * g = g * evalCodes gG w := by
  simp only [centralOKT, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hginv, hc⟩ := h
  have hgI := forall₂_inv_of_invOK hgT hginv
  have hw := rep_evalT hn hgT hgI w
  intro g hg
  obtain ⟨s, hs, hrs⟩ := exists_of_mem_right_forall₂ hgT hg
  exact (tblEq_eq_iff (hw.compT hrs) (hrs.compT hw)).1 (hc s hs)

end Spec

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
