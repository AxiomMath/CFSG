module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting

public section

namespace CFSG.Combinatorics.QuadrangleGraph

variable {α : Type*}

@[expose] noncomputable def perp2 [Fintype α] (adj : α → α → Prop) (x y : α) : Finset α := by
  classical
  exact Finset.univ.filter fun z => adj z x ∧ adj z y

@[expose] noncomputable def span2 [Fintype α] (adj : α → α → Prop) (x y : α) : Finset α := by
  classical
  exact Finset.univ.filter fun z => ∀ w, adj w x → adj w y → adj z w

@[expose] noncomputable def nbhd [Fintype α] (adj : α → α → Prop) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (adj x)

structure IsQuadrangle (adj : α → α → Prop) : Prop where
  refl : ∀ x : α, adj x x
  symm : ∀ {x y : α}, adj x y → adj y x
  clique : ∀ {x y u v : α}, x ≠ y → adj x y → adj u x → adj u y → adj v x → adj v y → adj u v
  meets : ∀ {x y : α} (z : α), x ≠ y → adj x y →
    ∃ w, adj w x ∧ adj w y ∧ adj z w

structure IsThickQuadrangle (adj : α → α → Prop) : Prop extends IsQuadrangle adj where
  thick_line : ∀ {x y : α}, x ≠ y → adj x y →
    ∃ z, adj z x ∧ adj z y ∧ z ≠ x ∧ z ≠ y
  thick_point : ∀ x : α, ∃ y, ¬ adj x y ∧ ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
    adj u x ∧ adj u y ∧ adj v x ∧ adj v y ∧ adj w x ∧ adj w y

structure IsQuadrangleOfOrder [Fintype α] (adj : α → α → Prop) (s t : ℕ) : Prop
    extends IsQuadrangle adj where
  card_line : ∀ {x y : α}, x ≠ y → adj x y → (perp2 adj x y).card = s + 1
  card_perp : ∀ {x y : α}, ¬ adj x y → (perp2 adj x y).card = t + 1
  exists_not_adj : ∀ x : α, ∃ y, ¬ adj x y

@[simp] theorem mem_perp2 [Fintype α] {adj : α → α → Prop} {x y z : α} :
    z ∈ perp2 adj x y ↔ adj z x ∧ adj z y := by
  classical
  simp [perp2]

@[simp] theorem mem_span2 [Fintype α] {adj : α → α → Prop} {x y z : α} :
    z ∈ span2 adj x y ↔ ∀ w, adj w x → adj w y → adj z w := by
  classical
  simp [span2]

@[simp] theorem mem_nbhd [Fintype α] {adj : α → α → Prop} {x z : α} :
    z ∈ nbhd adj x ↔ adj x z := by
  classical
  simp [nbhd]

theorem perp2_comm [Fintype α] (adj : α → α → Prop) (x y : α) :
    perp2 adj x y = perp2 adj y x := by
  ext z
  simp only [mem_perp2]
  exact and_comm

namespace IsQuadrangle

variable {adj : α → α → Prop}

theorem not_adj_of_not_adj (h : IsQuadrangle adj) {x y u v : α} (hxy : ¬ adj x y)
    (hux : adj u x) (huy : adj u y) (hvx : adj v x) (hvy : adj v y) (huv : u ≠ v) :
    ¬ adj u v :=
  fun huv' => hxy (h.clique huv huv' (h.symm hux) (h.symm hvx) (h.symm huy) (h.symm hvy))

theorem unique_adj (h : IsQuadrangle adj) {x y z w w' : α} (hxy : x ≠ y) (hadj : adj x y)
    (hz : ¬ (adj z x ∧ adj z y)) (hw : adj w x) (hw' : adj w y) (hzw : adj z w)
    (hw'x : adj w' x) (hw'y : adj w' y) (hzw' : adj z w') : w = w' := by
  by_contra hne
  have hww' : adj w w' := h.clique hxy hadj hw hw' hw'x hw'y
  exact hz ⟨h.clique hne hww' hzw hzw' (h.symm hw) (h.symm hw'x),
    h.clique hne hww' hzw hzw' (h.symm hw') (h.symm hw'y)⟩

theorem existsUnique_adj (h : IsQuadrangle adj) {x y z : α} (hxy : x ≠ y) (hadj : adj x y)
    (hz : ¬ (adj z x ∧ adj z y)) : ∃! w, adj w x ∧ adj w y ∧ adj z w := by
  obtain ⟨w, hw⟩ := h.meets z hxy hadj
  exact ⟨w, hw, fun w' hw' =>
    (h.unique_adj hxy hadj hz hw.1 hw.2.1 hw.2.2 hw'.1 hw'.2.1 hw'.2.2).symm⟩

theorem left_mem_perp2 (h : IsQuadrangle adj) [Fintype α] {x y : α} (hxy : adj x y) :
    x ∈ perp2 adj x y :=
  mem_perp2.2 ⟨h.refl x, hxy⟩

theorem right_mem_perp2 (h : IsQuadrangle adj) [Fintype α] {x y : α} (hxy : adj x y) :
    y ∈ perp2 adj x y :=
  mem_perp2.2 ⟨h.symm hxy, h.refl y⟩

theorem left_mem_span2 (h : IsQuadrangle adj) [Fintype α] (x y : α) : x ∈ span2 adj x y :=
  mem_span2.2 fun _ hw _ => h.symm hw

theorem mem_nbhd_self (h : IsQuadrangle adj) [Fintype α] (x : α) : x ∈ nbhd adj x :=
  mem_nbhd.2 (h.refl x)

theorem card_perp2_eq_of_not_adj (h : IsQuadrangle adj) [Fintype α] {b x y : α}
    (hx : ¬ adj b x) (hy : ¬ adj b y) :
    (perp2 adj b x).card = (perp2 adj b y).card := by
  classical
  have h1 : ∀ u ∈ perp2 adj b x,
      ((perp2 adj b y).bipartiteAbove (fun u w => adj u w) u).card = 1 := by
    intro u hu
    rw [mem_perp2] at hu
    have hbu : b ≠ u := fun e => hx (e ▸ hu.2)
    rw [Finset.card_eq_one_iff_existsUnique]
    simp only [Finset.mem_bipartiteAbove, mem_perp2]
    refine (existsUnique_congr (fun w => ?_)).2
      (h.existsUnique_adj hbu (h.symm hu.1) (z := y) fun hy' => hy (h.symm hy'.1))
    constructor
    · rintro ⟨⟨hwb, hwy⟩, huw⟩
      exact ⟨hwb, h.symm huw, h.symm hwy⟩
    · rintro ⟨hwb, hwu, hyw⟩
      exact ⟨⟨hwb, h.symm hyw⟩, h.symm hwu⟩
  have h2 : ∀ w ∈ perp2 adj b y,
      ((perp2 adj b x).bipartiteBelow (fun u w => adj u w) w).card = 1 := by
    intro w hw
    rw [mem_perp2] at hw
    have hbw : b ≠ w := fun e => hy (e ▸ hw.2)
    rw [Finset.card_eq_one_iff_existsUnique]
    simp only [Finset.mem_bipartiteBelow, mem_perp2]
    refine (existsUnique_congr (fun u => ?_)).2
      (h.existsUnique_adj hbw (h.symm hw.1) (z := x) fun hx' => hx (h.symm hx'.1))
    constructor
    · rintro ⟨⟨hub, hux⟩, huw⟩
      exact ⟨hub, huw, h.symm hux⟩
    · rintro ⟨hub, huw, hxu⟩
      exact ⟨⟨hub, h.symm hxu⟩, huw⟩
  have hmul := Finset.card_mul_eq_card_mul
    (s := perp2 adj b x) (t := perp2 adj b y) (r := fun u w => adj u w) h1 h2
  simpa using hmul

theorem isThickQuadrangle_of_base (h : IsQuadrangle adj) [Fintype α]
    (hline : ∀ {x y : α}, x ≠ y → adj x y →
      ∃ z, adj z x ∧ adj z y ∧ z ≠ x ∧ z ≠ y)
    (hbase : ∀ x, ∃ b, ¬ adj x b ∧ ∃ b', ¬ adj b b' ∧ 2 < (perp2 adj b b').card) :
    IsThickQuadrangle adj := by
  refine { toIsQuadrangle := h, thick_line := hline, thick_point := ?_ }
  intro x
  obtain ⟨b, hxb, b', hbb', hc⟩ := hbase x
  have hxb' : ¬ adj b x := fun hbx => hxb (h.symm hbx)
  have hcard : 2 < (perp2 adj x b).card := by
    rw [perp2_comm adj x b, h.card_perp2_eq_of_not_adj hxb' hbb']
    exact hc
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := Finset.two_lt_card_iff.1 hcard
  rw [mem_perp2] at hu hv hw
  exact ⟨b, hxb, u, v, w, huv, huw, hvw, hu.1, hu.2, hv.1, hv.2, hw.1, hw.2⟩

end IsQuadrangle

end CFSG.Combinatorics.QuadrangleGraph
