module

public import CFSG.Combinatorics.QuadrangleGraph
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Combinatorics.QuadrangleGraph

variable {α : Type*} {adj : α → α → Prop}

namespace IsQuadrangle

private theorem card_perp2_eq_aux [Fintype α] (h : IsQuadrangle adj) {a b c d : α}
    (hab : ¬ adj a b) (hcd : ¬ adj c d) (hac : ¬ adj a c) :
    (perp2 adj a b).card = (perp2 adj c d).card := by
  rw [h.card_perp2_eq_of_not_adj hab hac, perp2_comm adj a c,
    h.card_perp2_eq_of_not_adj (fun hca => hac (h.symm hca)) hcd]

theorem card_perp2_eq_of_disjoint [Fintype α] (h : IsQuadrangle adj) {x y u v : α}
    (hxy : x ≠ y) (hadj : adj x y) (huv : u ≠ v) (hadj' : adj u v)
    (hdisj : Disjoint (perp2 adj x y) (perp2 adj u v)) :
    (perp2 adj x y).card = (perp2 adj u v).card := by
  classical
  have h1 : ∀ a ∈ perp2 adj x y,
      ((perp2 adj u v).bipartiteAbove (fun a w => adj a w) a).card = 1 := by
    intro a ha
    have hna : ¬ (adj a u ∧ adj a v) := fun hau =>
      (Finset.disjoint_left.1 hdisj) ha (mem_perp2.2 hau)
    rw [Finset.card_eq_one_iff_existsUnique]
    simp only [Finset.mem_bipartiteAbove, mem_perp2]
    refine (existsUnique_congr (fun w => ?_)).2
      (h.existsUnique_adj huv hadj' (z := a) hna)
    constructor
    · rintro ⟨⟨hwu, hwv⟩, haw⟩
      exact ⟨hwu, hwv, haw⟩
    · rintro ⟨hwu, hwv, haw⟩
      exact ⟨⟨hwu, hwv⟩, haw⟩
  have h2 : ∀ b ∈ perp2 adj u v,
      ((perp2 adj x y).bipartiteBelow (fun a b => adj a b) b).card = 1 := by
    intro b hb
    have hnb : ¬ (adj b x ∧ adj b y) := fun hbx =>
      (Finset.disjoint_left.1 hdisj) (mem_perp2.2 hbx) hb
    rw [Finset.card_eq_one_iff_existsUnique]
    simp only [Finset.mem_bipartiteBelow, mem_perp2]
    refine (existsUnique_congr (fun a => ?_)).2
      (h.existsUnique_adj hxy hadj (z := b) hnb)
    constructor
    · rintro ⟨⟨hax, hay⟩, hab⟩
      exact ⟨hax, hay, h.symm hab⟩
    · rintro ⟨hax, hay, hba⟩
      exact ⟨⟨hax, hay⟩, h.symm hba⟩
  have hmul := Finset.card_mul_eq_card_mul
    (s := perp2 adj x y) (t := perp2 adj u v) (r := fun a b => adj a b) h1 h2
  simpa using hmul

theorem not_adj_of_adj_of_adj (h : IsQuadrangle adj) {z y₁ e u u' : α}
    (hzy : ¬ adj z y₁) (hu : adj u z) (huy : adj u y₁) (hu' : adj u' z) (hu'y : adj u' y₁)
    (huu' : u ≠ u') (hze : z ≠ e) (hez : adj e z) (hue : adj u e) : ¬ adj u' e :=
  fun hu'e => h.not_adj_of_not_adj hzy hu huy hu' hu'y huu'
    (h.clique hze (h.symm hez) hu hue hu' hu'e)

end IsQuadrangle

theorem IsThickQuadrangle.exists_adj_not_adj_not_adj (h : IsThickQuadrangle adj) {z a b : α}
    (hza : z ≠ a) (haz : adj a z) (hzb : z ≠ b) (hbz : adj b z) :
    ∃ n, adj n z ∧ n ≠ z ∧ ¬ adj n a ∧ ¬ adj n b := by
  obtain ⟨y, hzy, u, v, w, huv, huw, hvw, huz, huy, hvz, hvy, hwz, hwy⟩ := h.thick_point z
  have huz' : u ≠ z := fun e => hzy (e ▸ huy)
  have hvz' : v ≠ z := fun e => hzy (e ▸ hvy)
  have hwz' : w ≠ z := fun e => hzy (e ▸ hwy)
  have hnot : ∀ {p q e : α}, p ≠ q → adj p z → adj p y → adj q z → adj q y →
      adj e z → z ≠ e → adj p e → ¬ adj q e :=
    fun hpq hpz hpy hqz hqy hez hze hpe =>
      h.toIsQuadrangle.not_adj_of_adj_of_adj hzy hpz hpy hqz hqy hpq hze hez hpe
  by_cases hua : adj u a
  · by_cases hub : adj u b
    · exact ⟨v, hvz, hvz', hnot huv huz huy hvz hvy haz hza hua,
        hnot huv huz huy hvz hvy hbz hzb hub⟩
    · by_cases hvb : adj v b
      · exact ⟨w, hwz, hwz', hnot huw huz huy hwz hwy haz hza hua,
          hnot hvw hvz hvy hwz hwy hbz hzb hvb⟩
      · exact ⟨v, hvz, hvz', hnot huv huz huy hvz hvy haz hza hua, hvb⟩
  · by_cases hub : adj u b
    · by_cases hva : adj v a
      · exact ⟨w, hwz, hwz', hnot hvw hvz hvy hwz hwy haz hza hva,
          hnot huw huz huy hwz hwy hbz hzb hub⟩
      · exact ⟨v, hvz, hvz', hva, hnot huv huz huy hvz hvy hbz hzb hub⟩
    · exact ⟨u, huz, huz', hua, hub⟩

theorem IsThickQuadrangle.exists_not_adj_not_adj (h : IsThickQuadrangle adj) {x y : α}
    (hxy : adj x y) : ∃ z, ¬ adj z x ∧ ¬ adj z y := by
  obtain ⟨e, hxe, -⟩ := h.thick_point x
  by_cases hye : adj y e
  · have hey : e ≠ y := fun heq => hxe (by rw [heq]; exact hxy)
    obtain ⟨u, hue, hune, huy, -⟩ :=
      h.exists_adj_not_adj_not_adj (z := e) (a := y) (b := y) hey hye hey hye
    by_cases hux : adj u x
    · obtain ⟨f, hfe, hfu, hfe', hfu'⟩ := h.thick_line (Ne.symm hune) (h.symm hue)
      refine ⟨f, ?_, ?_⟩
      · intro hfx
        exact (h.toIsQuadrangle.not_adj_of_not_adj hxe hfx hfe hux hue hfu') hfu
      · intro hfy
        exact (h.toIsQuadrangle.not_adj_of_not_adj (x := y) (y := u)
          (fun hyu => huy (h.symm hyu)) (h.symm hye) (h.symm hue) hfy hfu
          (Ne.symm hfe')) (h.symm hfe)
    · exact ⟨u, hux, huy⟩
  · exact ⟨e, fun hex => hxe (h.symm hex), fun hey => hye (h.symm hey)⟩

theorem IsThickQuadrangle.exists_point_off_lines (h : IsThickQuadrangle adj) (x y : α)
    {u v : α} (huv : u ≠ v) (hadj' : adj u v) :
    ∃ z, ¬ (adj z x ∧ adj z y) ∧ ¬ (adj z u ∧ adj z v) := by
  obtain ⟨b, hbu, hbv, hxb⟩ := h.meets x huv hadj'
  obtain ⟨z, hzx, hzb⟩ := h.exists_not_adj_not_adj hxb
  exact ⟨z, fun hz => hzx hz.1, fun hz => hzb (h.clique huv hadj' hz.1 hz.2 hbu hbv)⟩

theorem IsThickQuadrangle.exists_line_disjoint [Fintype α] (h : IsThickQuadrangle adj)
    {x y u v : α} (hxy : x ≠ y) (hadj : adj x y) (huv : u ≠ v) (hadj' : adj u v) :
    ∃ n₁ n₂, n₁ ≠ n₂ ∧ adj n₁ n₂ ∧ Disjoint (perp2 adj n₁ n₂) (perp2 adj x y) ∧
      Disjoint (perp2 adj n₁ n₂) (perp2 adj u v) := by
  obtain ⟨z, hz1, hz2⟩ := h.exists_point_off_lines x y huv hadj'
  obtain ⟨a, hax, hay, hza⟩ := h.meets z hxy hadj
  obtain ⟨b, hbu, hbv, hzb⟩ := h.meets z huv hadj'
  have hza' : z ≠ a := by
    intro e
    rw [e] at hz1
    exact hz1 ⟨hax, hay⟩
  have hzb' : z ≠ b := by
    intro e
    rw [e] at hz2
    exact hz2 ⟨hbu, hbv⟩
  obtain ⟨n, hnz, hnz', hna, hnb⟩ :=
    h.exists_adj_not_adj_not_adj hza' (h.symm hza) hzb' (h.symm hzb)
  refine ⟨z, n, Ne.symm hnz', h.symm hnz, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro p hp hpq
    rw [mem_perp2] at hp hpq
    have hEq : p = a :=
      h.toIsQuadrangle.unique_adj hxy hadj hz1 hpq.1 hpq.2 (h.symm hp.1) hax hay hza
    exact hna (hEq ▸ h.symm hp.2)
  · rw [Finset.disjoint_left]
    intro p hp hpq
    rw [mem_perp2] at hp hpq
    have hEq : p = b :=
      h.toIsQuadrangle.unique_adj huv hadj' hz2 hpq.1 hpq.2 (h.symm hp.1) hbu hbv hzb
    exact hnb (hEq ▸ h.symm hp.2)

theorem IsThickQuadrangle.card_line_eq [Fintype α] (h : IsThickQuadrangle adj) {x y u v : α}
    (hxy : x ≠ y) (hadj : adj x y) (huv : u ≠ v) (hadj' : adj u v) :
    (perp2 adj x y).card = (perp2 adj u v).card := by
  obtain ⟨n₁, n₂, hn₁n₂, hadj'', hd₁, hd₂⟩ := h.exists_line_disjoint hxy hadj huv hadj'
  exact (h.toIsQuadrangle.card_perp2_eq_of_disjoint hxy hadj hn₁n₂ hadj'' hd₁.symm).trans
    (h.toIsQuadrangle.card_perp2_eq_of_disjoint hn₁n₂ hadj'' huv hadj' hd₂)

theorem IsThickQuadrangle.card_perp2_eq [Fintype α] (h : IsThickQuadrangle adj) {a b c d : α}
    (hab : ¬ adj a b) (hcd : ¬ adj c d) : (perp2 adj a b).card = (perp2 adj c d).card := by
  by_cases hac : adj a c
  · obtain ⟨z, hza, hzc⟩ := h.exists_not_adj_not_adj hac
    exact (IsQuadrangle.card_perp2_eq_aux h.toIsQuadrangle hab hza
      (fun haz => hza (h.toIsQuadrangle.symm haz))).trans
      (IsQuadrangle.card_perp2_eq_aux h.toIsQuadrangle hza hcd hzc)
  · exact IsQuadrangle.card_perp2_eq_aux h.toIsQuadrangle hab hcd hac

theorem IsThickQuadrangle.exists_order [Fintype α] [Nonempty α] (h : IsThickQuadrangle adj) :
    ∃ s t, 2 ≤ s ∧ 2 ≤ t ∧ IsQuadrangleOfOrder adj s t := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty α›
  obtain ⟨y₀, hx₀y₀, u, v, w, huv, huw, hvw, hux₀, huy₀, hvx₀, hvy₀, hwx₀, hwy₀⟩ :=
    h.thick_point x₀
  have hx₀u : x₀ ≠ u := fun e => hx₀y₀ (by rw [e]; exact huy₀)
  obtain ⟨z, hzx₀, hzu, hzx₀', hzu'⟩ := h.thick_line hx₀u (h.symm hux₀)
  have hcardy : 2 < (perp2 adj x₀ y₀).card :=
    Finset.two_lt_card_iff.2
      ⟨u, v, w, mem_perp2.2 ⟨hux₀, huy₀⟩, mem_perp2.2 ⟨hvx₀, hvy₀⟩,
        mem_perp2.2 ⟨hwx₀, hwy₀⟩, huv, huw, hvw⟩
  have hcardu : 2 < (perp2 adj x₀ u).card :=
    Finset.two_lt_card_iff.2
      ⟨x₀, u, z, mem_perp2.2 ⟨h.refl x₀, h.symm hux₀⟩,
        mem_perp2.2 ⟨hux₀, h.refl u⟩, mem_perp2.2 ⟨hzx₀, hzu⟩,
        hx₀u, Ne.symm hzx₀', Ne.symm hzu'⟩
  let s := (perp2 adj x₀ u).card - 1
  let t := (perp2 adj x₀ y₀).card - 1
  have hs : s + 1 = (perp2 adj x₀ u).card := by
    dsimp only [s]
    omega
  have ht : t + 1 = (perp2 adj x₀ y₀).card := by
    dsimp only [t]
    omega
  refine ⟨s, t, by omega, by omega, ?_⟩
  refine
    { toIsQuadrangle := h.toIsQuadrangle
      card_line := ?_
      card_perp := ?_
      exists_not_adj := ?_ }
  · intro x y hxy hadj
    rw [h.card_line_eq hxy hadj hx₀u (h.symm hux₀), hs]
  · intro x y hxy
    rw [h.card_perp2_eq hxy hx₀y₀, ht]
  · intro x
    obtain ⟨y, hy, -⟩ := h.thick_point x
    exact ⟨y, hy⟩

end CFSG.Combinatorics.QuadrangleGraph
