module

public import CFSG.Combinatorics.QuadrangleGraphCount
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Combinatorics.QuadrangleGraph

variable {α : Type*} {adj : α → α → Prop}

theorem sum_sq_card_filter_adj [DecidableRel adj] (O Z : Finset α) :
    ∑ w ∈ O, (Z.filter (adj w)).card ^ 2 =
      ∑ z ∈ Z, ∑ z' ∈ Z, (O.filter fun w => adj w z ∧ adj w z').card := by
  classical
  simp only [Finset.card_filter, sq, Finset.sum_mul_sum, ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact Finset.sum_comm

namespace IsQuadrangleOfOrder

variable [Fintype α] {s t p : ℕ}

private theorem exists_ne_mem_perp2 (h : IsQuadrangleOfOrder adj s t) (ht : 1 ≤ t)
    {x y : α} (hxy : ¬ adj x y) :
    ∃ z ∈ perp2 adj x y, ∃ z' ∈ perp2 adj x y, z ≠ z' := by
  have h2 : 2 ≤ (perp2 adj x y).card := by
    rw [h.card_perp hxy]
    exact Nat.succ_le_succ ht
  simpa using Finset.one_lt_card.1 h2

theorem not_adj_of_mem_span2 (h : IsQuadrangleOfOrder adj s t) (ht : 1 ≤ t) {x y u v : α}
    (hxy : ¬ adj x y) (hu : u ∈ span2 adj x y) (hv : v ∈ span2 adj x y) (huv : u ≠ v) :
    ¬ adj u v := by
  obtain ⟨z, hz, z', hz', hzz'⟩ := exists_ne_mem_perp2 h ht hxy
  have hzx : adj z x := (mem_perp2.1 hz).1
  have hzy : adj z y := (mem_perp2.1 hz).2
  have hz'x : adj z' x := (mem_perp2.1 hz').1
  have hz'y : adj z' y := (mem_perp2.1 hz').2
  have hzu : adj z u := h.toIsQuadrangle.symm ((mem_span2.1 hu) z hzx hzy)
  have hzv : adj z v := h.toIsQuadrangle.symm ((mem_span2.1 hv) z hzx hzy)
  have hz'u : adj z' u := h.toIsQuadrangle.symm ((mem_span2.1 hu) z' hz'x hz'y)
  have hz'v : adj z' v := h.toIsQuadrangle.symm ((mem_span2.1 hv) z' hz'x hz'y)
  exact fun huv' => h.toIsQuadrangle.not_adj_of_not_adj hxy hzx hzy hz'x hz'y hzz'
    (h.toIsQuadrangle.clique huv huv' hzu hzv hz'u hz'v)

theorem notMem_span2_of_mem_perp2 (h : IsQuadrangleOfOrder adj s t) (ht : 1 ≤ t) {x y z : α}
    (hxy : ¬ adj x y) (hz : z ∈ perp2 adj x y) : z ∉ span2 adj x y := by
  intro hzs
  have hzx : adj z x := (mem_perp2.1 hz).1
  have hzy : adj z y := (mem_perp2.1 hz).2
  have hzxne : z ≠ x := fun e => hxy (e ▸ hzy)
  exact (h.not_adj_of_mem_span2 ht hxy hzs
    (h.toIsQuadrangle.left_mem_span2 x y) hzxne) hzx

theorem perp2_eq_of_mem_span2 (h : IsQuadrangleOfOrder adj s t) (ht : 1 ≤ t) {x y u v : α}
    (hxy : ¬ adj x y) (hu : u ∈ span2 adj x y) (hv : v ∈ span2 adj x y) (huv : u ≠ v) :
    perp2 adj u v = perp2 adj x y := by
  have hsub : perp2 adj x y ⊆ perp2 adj u v := by
    intro z hz
    rw [mem_perp2] at hz ⊢
    exact ⟨h.toIsQuadrangle.symm ((mem_span2.1 hu) z hz.1 hz.2),
      h.toIsQuadrangle.symm ((mem_span2.1 hv) z hz.1 hz.2)⟩
  have hcard : (perp2 adj u v).card = (perp2 adj x y).card := by
    rw [h.card_perp (x := u) (y := v) (h.not_adj_of_mem_span2 ht hxy hu hv huv),
      h.card_perp (x := x) (y := y) hxy]
  exact (Finset.eq_of_subset_of_card_le hsub hcard.le).symm

theorem card_far (h : IsQuadrangleOfOrder adj s t) (ht : 1 ≤ t) {x y : α}
    (hxy : ¬ adj x y) (hp : (span2 adj x y).card = p + 1) {O : Finset α}
    (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) :
    O.card + (t + 1) + (p + 1) * ((t + 1) * s + 1) =
      (s + 1) * (s * t + 1) + (p + 1) * (t + 1) := by
  classical
  haveI : Nonempty α := ⟨x⟩
  have hVne : (span2 adj x y).Nonempty := ⟨x, h.toIsQuadrangle.left_mem_span2 x y⟩
  have hC : ∀ u ∈ span2 adj x y, perp2 adj x y ⊆ nbhd adj u := by
    intro u hu z hz
    rw [mem_nbhd]
    exact (mem_span2.1 hu) z (mem_perp2.1 hz).1 (mem_perp2.1 hz).2
  have hL : ∀ u ∈ span2 adj x y, ∀ v ∈ span2 adj x y, u ≠ v →
      nbhd adj u ∩ nbhd adj v ⊆ perp2 adj x y := by
    intro u hu v hv huv z hz
    rw [Finset.mem_inter] at hz
    have hzuv : z ∈ perp2 adj u v :=
      mem_perp2.2 ⟨h.toIsQuadrangle.symm (mem_nbhd.1 hz.1),
        h.toIsQuadrangle.symm (mem_nbhd.1 hz.2)⟩
    rw [h.perp2_eq_of_mem_span2 ht hxy hu hv huv] at hzuv
    exact hzuv
  have hm : ∀ u ∈ span2 adj x y, (nbhd adj u).card = (t + 1) * s + 1 :=
    fun u _ => h.card_nbhd u
  have hsun := card_biUnion_add_card_mul (S := span2 adj x y) (L := fun u => nbhd adj u)
    (C := perp2 adj x y) (m := (t + 1) * s + 1) hVne hC hL hm
  rw [h.card_perp hxy, hp] at hsun
  have hOeq : O = Finset.univ \ (span2 adj x y).biUnion (fun u => nbhd adj u) := by
    ext w
    simp only [hO w, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
      mem_nbhd]
    constructor
    · intro hw hne
      obtain ⟨u, hu, hwu⟩ := hne
      exact hw u hu (h.toIsQuadrangle.symm hwu)
    · intro hne u hu hwu
      exact hne ⟨u, hu, h.toIsQuadrangle.symm hwu⟩
  have hOcard : O.card +
      ((span2 adj x y).biUnion fun u => nbhd adj u).card = Fintype.card α := by
    rw [hOeq, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
  rw [h.fintype_card_eq] at hOcard
  linarith

theorem card_filter_adj_of_mem_perp2 [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    (ht : 1 ≤ t) {x y : α} (hxy : ¬ adj x y) (hp : (span2 adj x y).card = p + 1)
    {O : Finset α} (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) {z : α}
    (hz : z ∈ perp2 adj x y) :
    (O.filter fun w => adj w z).card + (p + 1) * s = (t + 1) * s := by
  classical
  have hzx : adj z x := (mem_perp2.1 hz).1
  have hzy : adj z y := (mem_perp2.1 hz).2
  have hVne : (span2 adj x y).Nonempty := ⟨x, h.toIsQuadrangle.left_mem_span2 x y⟩
  have hC : ∀ u ∈ span2 adj x y, ({z} : Finset α) ⊆ perp2 adj z u := by
    intro u hu w hw
    rw [Finset.mem_singleton] at hw
    subst w
    exact mem_perp2.2 ⟨h.toIsQuadrangle.refl z,
      h.toIsQuadrangle.symm ((mem_span2.1 hu) z hzx hzy)⟩
  have hL : ∀ u ∈ span2 adj x y, ∀ v ∈ span2 adj x y, u ≠ v →
      perp2 adj z u ∩ perp2 adj z v ⊆ ({z} : Finset α) := by
    intro u hu v hv huv w hw
    rw [Finset.mem_inter, mem_perp2, mem_perp2] at hw
    obtain ⟨⟨hwz, hwu⟩, ⟨-, hwv⟩⟩ := hw
    by_contra hwne
    rw [Finset.mem_singleton] at hwne
    exact (h.not_adj_of_mem_span2 ht hxy hu hv huv)
      (h.toIsQuadrangle.clique (Ne.symm hwne) (h.toIsQuadrangle.symm hwz)
        ((mem_span2.1 hu) z hzx hzy) (h.toIsQuadrangle.symm hwu)
        ((mem_span2.1 hv) z hzx hzy) (h.toIsQuadrangle.symm hwv))
  have hm : ∀ u ∈ span2 adj x y, (perp2 adj z u).card = s + 1 := by
    intro u hu
    have hzu : z ≠ u := fun e => (h.notMem_span2_of_mem_perp2 ht hxy hz) (e.symm ▸ hu)
    exact h.card_line hzu (h.toIsQuadrangle.symm ((mem_span2.1 hu) z hzx hzy))
  have hsun := card_biUnion_add_card_mul (S := span2 adj x y) (L := fun u => perp2 adj z u)
    (C := ({z} : Finset α)) (m := s + 1) hVne hC hL hm
  rw [Finset.card_singleton, Nat.mul_one, hp, Nat.mul_succ] at hsun
  have hUsub : (span2 adj x y).biUnion (fun u => perp2 adj z u) ⊆ nbhd adj z := by
    intro w hw
    obtain ⟨u, -, hwu⟩ := Finset.mem_biUnion.1 hw
    rw [mem_nbhd]
    exact h.toIsQuadrangle.symm (mem_perp2.1 hwu).1
  have hfilter : O.filter (fun w => adj w z) =
      nbhd adj z \ (span2 adj x y).biUnion (fun u => perp2 adj z u) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_sdiff, mem_nbhd, Finset.mem_biUnion, hO w]
    constructor
    · rintro ⟨hOw, hwz⟩
      exact ⟨h.toIsQuadrangle.symm hwz, fun hwu => by
        obtain ⟨u, hu, hwu'⟩ := hwu
        exact hOw u hu (mem_perp2.1 hwu').2⟩
    · rintro ⟨hzw, hnot⟩
      refine ⟨fun u hu hwu => hnot ⟨u, hu, mem_perp2.2 ⟨h.toIsQuadrangle.symm hzw, hwu⟩⟩,
        h.toIsQuadrangle.symm hzw⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hUsub
  rw [← hfilter, h.card_nbhd z] at hcard
  linarith

theorem card_filter_adj_adj_of_mem_perp2 [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    {x y : α} (hxy : ¬ adj x y) (hp : (span2 adj x y).card = p + 1) {O : Finset α}
    (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) {z z' : α}
    (hz : z ∈ perp2 adj x y) (hz' : z' ∈ perp2 adj x y) (hzz' : z ≠ z') :
    (O.filter fun w => adj w z ∧ adj w z').card + (p + 1) = t + 1 := by
  classical
  have hzx : adj z x := (mem_perp2.1 hz).1
  have hzy : adj z y := (mem_perp2.1 hz).2
  have hz'x : adj z' x := (mem_perp2.1 hz').1
  have hz'y : adj z' y := (mem_perp2.1 hz').2
  have hzz'_not : ¬ adj z z' :=
    h.toIsQuadrangle.not_adj_of_not_adj hxy hzx hzy hz'x hz'y hzz'
  have hVsub : span2 adj x y ⊆ perp2 adj z z' := by
    intro u hu
    rw [mem_perp2]
    exact ⟨(mem_span2.1 hu) z hzx hzy, (mem_span2.1 hu) z' hz'x hz'y⟩
  have hfilter : O.filter (fun w => adj w z ∧ adj w z') =
      perp2 adj z z' \ span2 adj x y := by
    ext w
    rw [Finset.mem_filter, Finset.mem_sdiff, mem_perp2, hO w]
    constructor
    · rintro ⟨hOw, hwz, hwz'⟩
      exact ⟨⟨hwz, hwz'⟩, fun hwV => hOw w hwV (h.toIsQuadrangle.refl w)⟩
    · rintro ⟨⟨hwz, hwz'⟩, hwV⟩
      refine ⟨fun u hu hwu => ?_, hwz, hwz'⟩
      exact (h.toIsQuadrangle.not_adj_of_not_adj hzz'_not hwz hwz'
        ((mem_span2.1 hu) z hzx hzy) ((mem_span2.1 hu) z' hz'x hz'y)
        (fun hwu' => hwV (hwu'.symm ▸ hu))) hwu
  have hcard := Finset.card_sdiff_add_card_eq_card hVsub
  rw [← hfilter, hp, h.card_perp hzz'_not] at hcard
  exact hcard

theorem sum_card_filter_adj_adj_row [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    (ht : 1 ≤ t) {x y : α} (hxy : ¬ adj x y) (hp : (span2 adj x y).card = p + 1)
    {O : Finset α} (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) {z : α}
    (hz : z ∈ perp2 adj x y) :
    ∑ z' ∈ perp2 adj x y, (O.filter fun w => adj w z ∧ adj w z').card + t * (p + 1) +
      (p + 1) * s = (t + 1) * s + t * (t + 1) := by
  classical
  rw [← Finset.add_sum_erase (perp2 adj x y)
    (fun z' => (O.filter fun w => adj w z ∧ adj w z').card) hz]
  have hzterm : (O.filter fun w => adj w z ∧ adj w z).card =
      (O.filter fun w => adj w z).card := by
    congr 1
    exact Finset.filter_congr fun w _ => by simp
  rw [hzterm]
  have hzrow := h.card_filter_adj_of_mem_perp2 ht hxy hp hO hz
  have herase : ∀ z' ∈ (perp2 adj x y).erase z,
      (O.filter fun w => adj w z ∧ adj w z').card + (p + 1) = t + 1 := by
    intro z' hz'
    have hz'ne : z' ≠ z := (Finset.mem_erase.1 hz').1
    exact h.card_filter_adj_adj_of_mem_perp2 hxy hp hO hz (Finset.mem_erase.1 hz').2
      (Ne.symm hz'ne)
  have hsum : (∑ z' ∈ (perp2 adj x y).erase z,
      (O.filter fun w => adj w z ∧ adj w z').card) +
      ((perp2 adj x y).erase z).card * (p + 1) =
      ((perp2 adj x y).erase z).card * (t + 1) := by
    have hconst : ((perp2 adj x y).erase z).card * (p + 1) =
        ∑ _z' ∈ (perp2 adj x y).erase z, (p + 1) :=
      (Finset.sum_const_nat (m := p + 1) (f := fun _ => p + 1) (fun _ _ => rfl)).symm
    rw [hconst, ← Finset.sum_add_distrib, Finset.sum_congr rfl herase]
    rw [Finset.sum_const_nat (m := t + 1) (f := fun _ => t + 1) (fun _ _ => rfl)]
  rw [Finset.card_erase_of_mem hz, h.card_perp hxy, Nat.add_sub_cancel] at hsum
  linarith

end IsQuadrangleOfOrder

end CFSG.Combinatorics.QuadrangleGraph
