module

public import CFSG.Combinatorics.QuadrangleGraph
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Combinatorics.QuadrangleGraph

variable {α : Type*}

theorem card_biUnion_add_card_mul {ι : Type*} [DecidableEq α] {S : Finset ι}
    {L : ι → Finset α} {C : Finset α} {m : ℕ} (hS : S.Nonempty) (hC : ∀ i ∈ S, C ⊆ L i)
    (hL : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → L i ∩ L j ⊆ C) (hm : ∀ i ∈ S, (L i).card = m) :
    (S.biUnion L).card + S.card * C.card = C.card + S.card * m := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  have hU : S.biUnion L = C ∪ S.biUnion (fun i => L i \ C) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
      by_cases hxC : x ∈ C
      · exact Finset.mem_union.2 (Or.inl hxC)
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_biUnion.2
          ⟨i, hi, Finset.mem_sdiff.2 ⟨hxi, hxC⟩⟩))
    · intro hx
      rcases Finset.mem_union.1 hx with hxC | hx
      · exact Finset.mem_biUnion.2 ⟨i₀, hi₀, hC i₀ hi₀ hxC⟩
      · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
        exact Finset.mem_biUnion.2 ⟨i, hi, (Finset.mem_sdiff.1 hxi).1⟩
  have hdisj : Disjoint C (S.biUnion fun i => L i \ C) := by
    rw [Finset.disjoint_left]
    intro x hxC hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    exact (Finset.mem_sdiff.1 hxi).2 hxC
  have hpd : (S : Set ι).PairwiseDisjoint fun i => L i \ C := by
    intro i hi j hj hij
    change Disjoint (L i \ C) (L j \ C)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact (Finset.mem_sdiff.1 hxi).2
      (hL i hi j hj hij (Finset.mem_inter.2
        ⟨(Finset.mem_sdiff.1 hxi).1, (Finset.mem_sdiff.1 hxj).1⟩))
  have hsd : ∀ i ∈ S, (L i \ C).card + C.card = m := fun i hi =>
    (Finset.card_sdiff_add_card_eq_card (hC i hi)).trans (hm i hi)
  have hsum : (∑ i ∈ S, ((L i \ C).card + C.card)) = ∑ _i ∈ S, m :=
    Finset.sum_congr rfl hsd
  rw [Finset.sum_add_distrib,
    Finset.sum_const_nat (m := C.card) (f := fun _ => C.card) (fun _ _ => rfl),
    Finset.sum_const_nat (m := m) (f := fun _ => m) (fun _ _ => rfl)] at hsum
  rw [hU, Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hpd]
  linarith

theorem IsQuadrangle.nbhd_eq_biUnion [Fintype α] [DecidableEq α] {adj : α → α → Prop}
    (h : IsQuadrangle adj) {x y : α} (hne : (perp2 adj x y).Nonempty) :
    nbhd adj x = (perp2 adj x y).biUnion fun u => perp2 adj x u := by
  ext z
  constructor
  · intro hz
    rw [mem_nbhd] at hz
    by_cases hzx : z = x
    · subst z
      obtain ⟨u, hu⟩ := hne
      refine Finset.mem_biUnion.2 ⟨u, hu, ?_⟩
      rw [mem_perp2]
      exact ⟨h.refl x, h.symm (mem_perp2.1 hu).1⟩
    · obtain ⟨w, hwx, hwz, hyw⟩ := h.meets y (Ne.symm hzx) hz
      refine Finset.mem_biUnion.2 ⟨w, ?_, ?_⟩
      · rw [mem_perp2]
        exact ⟨hwx, h.symm hyw⟩
      · rw [mem_perp2]
        exact ⟨h.symm hz, h.symm hwz⟩
  · intro hz
    obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.1 hz
    rw [mem_nbhd]
    exact h.symm (mem_perp2.1 hzu).1

namespace IsQuadrangleOfOrder

variable [Fintype α] {adj : α → α → Prop} {s t : ℕ}

theorem card_nbhd (h : IsQuadrangleOfOrder adj s t) (x : α) :
    (nbhd adj x).card = (t + 1) * s + 1 := by
  classical
  obtain ⟨y, hy⟩ := h.exists_not_adj x
  have hne : (perp2 adj x y).Nonempty :=
    Finset.card_pos.1 (by rw [h.card_perp (x := x) (y := y) hy]; omega)
  rw [h.toIsQuadrangle.nbhd_eq_biUnion (x := x) (y := y) hne]
  have hmain := card_biUnion_add_card_mul
    (S := perp2 adj x y) (L := fun u => perp2 adj x u) (C := {x}) (m := s + 1)
    hne
    (fun u hu => by
      intro z hz
      rw [Finset.mem_singleton] at hz
      subst z
      exact h.toIsQuadrangle.left_mem_perp2 (h.toIsQuadrangle.symm (mem_perp2.1 hu).1))
    (fun u hu v hv huv z hz => by
      rw [Finset.mem_singleton]
      by_contra hzx
      rw [mem_perp2] at hu hv
      rw [Finset.mem_inter] at hz
      obtain ⟨hzu, hzv⟩ := hz
      rw [mem_perp2] at hzu hzv
      exact (h.toIsQuadrangle.not_adj_of_not_adj hy hu.1 hu.2 hv.1 hv.2 huv)
        (h.toIsQuadrangle.clique (Ne.symm hzx) (h.toIsQuadrangle.symm hzu.1) hu.1
          (h.toIsQuadrangle.symm hzu.2) hv.1 (h.toIsQuadrangle.symm hzv.2)))
    (fun u hu => by
      rw [mem_perp2] at hu
      have hxu : x ≠ u := fun e => hy (e ▸ hu.2)
      exact h.card_line (x := x) (y := u) hxu (h.toIsQuadrangle.symm hu.1))
  rw [h.card_perp (x := x) (y := y) hy, Finset.card_singleton, Nat.mul_one] at hmain
  rw [Nat.mul_succ] at hmain
  have hmain' : ((perp2 adj x y).biUnion (fun u => perp2 adj x u)).card + (t + 1) =
      ((t + 1) * s + 1) + (t + 1) := by
    rw [hmain]
    ring
  exact Nat.add_right_cancel hmain'

theorem card_mul_of_mem_iff_not_adj (h : IsQuadrangleOfOrder adj s t) {x : α} {F : Finset α}
    (hF : ∀ w, w ∈ F ↔ ¬ adj x w) :
    F.card * (t + 1) = ((t + 1) * s) * (t * s) := by
  classical
  have hxmem : x ∈ nbhd adj x := h.mem_nbhd_self x
  have h1 : ∀ u ∈ (nbhd adj x).erase x,
      (F.bipartiteAbove (fun u w => adj u w) u).card = t * s := by
    intro u hu
    obtain ⟨hux_ne, hux_mem⟩ := Finset.mem_erase.1 hu
    have hxu : adj x u := mem_nbhd.1 hux_mem
    have hset : F.bipartiteAbove (fun u w => adj u w) u = nbhd adj u \ perp2 adj u x := by
      ext w
      rw [Finset.mem_bipartiteAbove, Finset.mem_sdiff, mem_nbhd, mem_perp2, hF w]
      constructor
      · rintro ⟨hwF, huw⟩
        exact ⟨huw, fun hwu => hwF (h.symm hwu.2)⟩
      · rintro ⟨huw, hnot⟩
        exact ⟨fun hxw => hnot ⟨h.symm huw, h.symm hxw⟩, huw⟩
    rw [hset]
    have hsub : perp2 adj u x ⊆ nbhd adj u := fun z hz =>
      mem_nbhd.2 (h.symm (mem_perp2.1 hz).1)
    have hEq : (nbhd adj u \ perp2 adj u x).card + (s + 1) = t * s + (s + 1) := by
      have h0 : (nbhd adj u \ perp2 adj u x).card + (s + 1) = (nbhd adj u).card := by
        rw [← h.card_line (x := u) (y := x) hux_ne (h.symm hxu)]
        exact Finset.card_sdiff_add_card_eq_card hsub
      rw [h0, h.card_nbhd u]
      ring
    exact Nat.add_right_cancel hEq
  have h2 : ∀ w ∈ F,
      (((nbhd adj x).erase x).bipartiteBelow (fun u w => adj u w) w).card = t + 1 := by
    intro w hwF
    have hxw : ¬ adj x w := (hF w).1 hwF
    have hset : ((nbhd adj x).erase x).bipartiteBelow (fun u w => adj u w) w =
        perp2 adj x w := by
      ext u
      rw [Finset.mem_bipartiteBelow, Finset.mem_erase, mem_nbhd, mem_perp2]
      constructor
      · rintro ⟨⟨_hux, hxu⟩, huw⟩
        exact ⟨h.symm hxu, huw⟩
      · rintro ⟨hxu, huw⟩
        exact ⟨⟨fun hux => hxw (hux ▸ huw), h.symm hxu⟩, huw⟩
    rw [hset, h.card_perp (x := x) (y := w) hxw]
  have hcard : ((nbhd adj x).erase x).card = (t + 1) * s := by
    rw [Finset.card_erase_of_mem hxmem, h.card_nbhd x, Nat.add_sub_cancel]
  have hmul := Finset.card_mul_eq_card_mul
    (s := (nbhd adj x).erase x) (t := F) (r := fun u w => adj u w) h1 h2
  rw [hcard] at hmul
  exact hmul.symm

theorem fintype_card_eq (h : IsQuadrangleOfOrder adj s t) [Nonempty α] :
    Fintype.card α = (s + 1) * (s * t + 1) := by
  classical
  obtain ⟨x⟩ := ‹Nonempty α›
  let F : Finset α := Finset.univ.filter fun w => ¬ adj x w
  have hF : ∀ w, w ∈ F ↔ ¬ adj x w := by
    intro w
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  have hFcard : F.card = s * s * t := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < t + 1 by omega)
    calc F.card * (t + 1) = ((t + 1) * s) * (t * s) :=
          h.card_mul_of_mem_iff_not_adj (x := x) (F := F) hF
      _ = (s * s * t) * (t + 1) := by ring
  have hnbhd : nbhd adj x = Finset.univ.filter (fun w => adj x w) := by
    ext w
    rw [mem_nbhd, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun w => adj x w)
  rw [show Finset.univ.filter (fun w => adj x w) = nbhd adj x from hnbhd.symm,
    show Finset.univ.filter (fun w => ¬ adj x w) = F from rfl,
    Finset.card_univ, h.card_nbhd x, hFcard] at hsum
  rw [← hsum]
  ring

end IsQuadrangleOfOrder

end CFSG.Combinatorics.QuadrangleGraph
