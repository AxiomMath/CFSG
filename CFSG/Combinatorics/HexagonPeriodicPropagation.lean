module

public import CFSG.Combinatorics.HexagonPeriodicPropagationLocal

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath

namespace CFSG.Combinatorics.HexagonPeriodicPropagation

theorem periodic_opposite_component_six_cycle_propagation {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
    (hdata : IsFrameData G col w p z q c ε) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    ∀ Q : (Γ.induce O).ConnectedComponent,
      let QP : Set {v : V // col v = false} :=
        {x | ∃ h : x ∈ O, (Γ.induce O).connectedComponentMk ⟨x, h⟩ = Q}
      let hexagon : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
        Function.Injective x ∧ (∀ n, x n ∈ QP) ∧ ∀ n, Γ.Adj (x n) (x (n + 1))
      let periodic : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
        ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n
      let cycles : Set (Finset (Sym2 {v : V // col v = false})) :=
        {C | ∃ x, hexagon x ∧ C = univ.image fun n => s(x n, x (n + 1))}
      (∃ x, hexagon x ∧ periodic x) →
        (∀ x, hexagon x → periodic x) ∧
        (∀ a ∈ QP, ∀ b ∈ QP, Γ.Adj a b → {C ∈ cycles | s(a, b) ∈ C}.ncard = 2) ∧
        (∀ a ∈ QP, ∀ b ∈ QP, ∀ d ∈ QP, Γ.Adj a b → Γ.Adj b d → a ≠ d →
          {C ∈ cycles | s(a, b) ∈ C ∧ s(b, d) ∈ C}.ncard = 1) := by
  intro Γ O Q QP hexagon periodic cycles hper
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have hQO : ∀ {x}, x ∈ QP → x ∈ O := fun hx => hx.1
  have hQadj : ∀ {x y}, x ∈ QP → y ∈ O → Γ.Adj x y → y ∈ QP := by
    rintro x y ⟨hx, hxQ⟩ hy hxy
    exact ⟨hy, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := Γ.induce O) (v := ⟨x, hx⟩) (w := ⟨y, hy⟩) hxy).symm.trans hxQ⟩
  have hhexO : ∀ {x}, hexagon x → IsHex G col w x :=
    fun hx => ⟨hx.1, fun n => hQO (hx.2.1 n), hx.2.2⟩
  have hhexQ : ∀ {E}, IsHex G col w E → E 1 ∈ QP → hexagon E := by
    intro E hE h1
    have h2 : E 2 ∈ QP := hQadj (y := E 2) h1 (hE.2.1 2) (hE.2.2 1)
    have h3 : E 3 ∈ QP := hQadj (y := E 3) h2 (hE.2.1 3) (hE.2.2 2)
    have h4 : E 4 ∈ QP := hQadj (y := E 4) h3 (hE.2.1 4) (hE.2.2 3)
    have h5 : E 5 ∈ QP := hQadj (y := E 5) h4 (hE.2.1 5) (hE.2.2 4)
    have h0 : E 0 ∈ QP := hQadj (y := E 0) h5 (hE.2.1 0) (hE.2.2 5)
    refine ⟨hE.1, fun n => ?_, hE.2.2⟩
    fin_cases n
    exacts [h0, h1, h2, h3, h4, h5]
  let good : {v : V // col v = false} → Prop := fun v => ∀ a d, a ∈ O → d ∈ O →
    Γ.Adj v a → Γ.Adj v d → a ≠ d →
      ∃ E, IsHex G col w E ∧ IsPeriodic c E ∧ E 0 = a ∧ E 1 = v ∧ E 2 = d
  have hgood_mem : ∀ {C}, IsHex G col w C → IsPeriodic c C → ∀ m, good (C m) :=
    fun hC hCp m a d ha hd hma hmd had => F.exists_periodic_of_mem hC hCp m ha hd hma hmd had
  have hgood_adj : ∀ {v v'}, v ∈ O → v' ∈ O → Γ.Adj v v' → good v → good v' := by
    intro v v' hv hv' hvv' hgv
    obtain ⟨a, ha, hva, hca⟩ := F.exists_colour hv (c v v' + 1)
    have hav' : a ≠ v' := by
      rintro rfl
      have key : ∀ t : Fin 3, t + 1 ≠ t := by decide
      exact key _ hca.symm
    obtain ⟨E, hE, hEp, -, -, hE2⟩ := hgv a v' ha hv' hva hvv' hav'
    rw [← hE2]
    exact hgood_mem hE hEp 2
  obtain ⟨x₀, hx₀, hx₀p⟩ := hper
  have hgood : ∀ {v}, v ∈ QP → good v := by
    rintro v ⟨hv, hvQ⟩
    obtain ⟨h₀, h₀Q⟩ := hx₀.2.1 0
    obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact (h₀Q.trans hvQ.symm)
    have key : ∀ {u u' : O} (W : (Γ.induce O).Walk u u'), good u.1 → good u'.1 := by
      intro u u' W
      induction W with
      | nil => exact id
      | @cons u₀ u₁ u₂ h W ih => exact fun hgu => ih (hgood_adj u₀.2 u₁.2 h hgu)
    exact key W (hgood_mem (hhexO hx₀) hx₀p 0)
  have hone : ∀ a ∈ QP, ∀ b ∈ QP, ∀ d ∈ QP, Γ.Adj a b → Γ.Adj b d → a ≠ d →
      ∃ E, IsHex G col w E ∧ IsPeriodic c E ∧ E 0 = a ∧ E 1 = b ∧ E 2 = d ∧
        {C ∈ cycles | s(a, b) ∈ C ∧ s(b, d) ∈ C} = {hexEdges E} := by
    intro a ha b hb d hd hab hbd had
    obtain ⟨E, hE, hEp, hE0, hE1, hE2⟩ := hgood hb a d (hQO ha) (hQO hd) hab.symm hbd had
    refine ⟨E, hE, hEp, hE0, hE1, hE2, ?_⟩
    ext C
    rw [Set.mem_sep_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨D, hD, rfl⟩, hDab, hDbd⟩
      obtain ⟨D', hD', hD'e, hD'0, hD'1, hD'2⟩ := exists_normal (hhexO hD) hDab hDbd had
      have hDE := F.eq_of_periodic hE hEp hD' (hD'0.trans hE0.symm) (hD'1.trans hE1.symm)
        (hD'2.trans hE2.symm)
      show hexEdges D = hexEdges E
      rw [← hD'e, hDE]
    · rintro rfl
      refine ⟨⟨E, hhexQ hE (by rw [hE1]; exact hb), rfl⟩, ?_, ?_⟩
      · rw [← hE0, ← hE1]
        exact Finset.mem_image_of_mem _ (mem_univ 0)
      · rw [← hE1, ← hE2]
        exact Finset.mem_image_of_mem _ (mem_univ 1)
  refine ⟨fun x hx => ?_, fun a ha b hb hab => ?_, fun a ha b hb d hd hab hbd had => ?_⟩
  ·
    obtain ⟨E, hE, hEp, hE0, hE1, hE2⟩ := hgood (hx.2.1 1) (x 0) (x 2) (hQO (hx.2.1 0))
      (hQO (hx.2.1 2)) (hx.2.2 0).symm (hx.2.2 1) (fun h => absurd (hx.1 h) (by decide))
    have hxE := F.eq_of_periodic hE hEp (hhexO hx) hE0.symm hE1.symm hE2.symm
    rw [hxE]
    exact hEp
  ·
    have hbO := hQO hb
    obtain ⟨d₁, hd₁, hbd₁, hc₁⟩ := F.exists_colour hbO (c b a + 1)
    obtain ⟨d₂, hd₂, hbd₂, hc₂⟩ := F.exists_colour hbO (c b a + 2)
    have k1 : ∀ t : Fin 3, t + 1 ≠ t := by decide
    have k2 : ∀ t : Fin 3, t + 2 ≠ t := by decide
    have k3 : ∀ t : Fin 3, t + 2 ≠ t + 1 := by decide
    have k4 : ∀ t s : Fin 3, s = t ∨ s = t + 1 ∨ s = t + 2 := by decide
    have had₁ : a ≠ d₁ := by
      rintro rfl
      exact k1 _ hc₁.symm
    have had₂ : a ≠ d₂ := by
      rintro rfl
      exact k2 _ hc₂.symm
    have hd₁₂ : d₁ ≠ d₂ := by
      rintro rfl
      exact k3 _ (hc₂.symm.trans hc₁)
    obtain ⟨E₁, hE₁, -, hE₁0, hE₁1, hE₁2, hS₁⟩ :=
      hone a ha b hb d₁ (hQadj hb hd₁ hbd₁) hab hbd₁ had₁
    obtain ⟨E₂, -, -, -, hE₂1, hE₂2, hS₂⟩ := hone a ha b hb d₂ (hQadj hb hd₂ hbd₂) hab hbd₂ had₂
    have hsplit : {C ∈ cycles | s(a, b) ∈ C} =
        {C ∈ cycles | s(a, b) ∈ C ∧ s(b, d₁) ∈ C} ∪ {C ∈ cycles | s(a, b) ∈ C ∧ s(b, d₂) ∈ C} := by
      ext C
      rw [Set.mem_union, Set.mem_sep_iff, Set.mem_sep_iff, Set.mem_sep_iff]
      constructor
      · rintro ⟨hC, hCab⟩
        obtain ⟨D, hD, rfl⟩ := hC
        obtain ⟨t, ht, hbt, htD, hta⟩ := exists_other_edge (hhexO hD) hCab
        rcases k4 (c b a) (c b t) with h | h | h
        · exact absurd (F.unique hbO ht (hQO ha) hbt hab.symm h) hta
        · refine Or.inl ⟨⟨D, hD, rfl⟩, hCab, ?_⟩
          rw [F.unique hbO hd₁ ht hbd₁ hbt (hc₁.trans h.symm)]
          exact htD
        · refine Or.inr ⟨⟨D, hD, rfl⟩, hCab, ?_⟩
          rw [F.unique hbO hd₂ ht hbd₂ hbt (hc₂.trans h.symm)]
          exact htD
      · rintro (⟨hC, hCab, -⟩ | ⟨hC, hCab, -⟩) <;> exact ⟨hC, hCab⟩
    have hne : hexEdges E₁ ≠ hexEdges E₂ := by
      intro heq
      have hmem : s(b, d₂) ∈ hexEdges E₁ := by
        rw [heq, ← hE₂1, ← hE₂2]
        exact Finset.mem_image_of_mem _ (mem_univ 1)
      obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hmem
      rcases Sym2.eq_iff.mp hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn1 : n = 1 := hE₁.1 (h1.trans hE₁1.symm)
        rw [hn1] at h2
        exact hd₁₂ (hE₁2.symm.trans h2)
      · have hn0 : n = 0 := by
          have hn1 : n + 1 = 0 + 1 := hE₁.1 (h2.trans hE₁1.symm)
          exact add_right_cancel hn1
        rw [hn0] at h1
        exact had₂ (hE₁0.symm.trans h1)
    rw [hsplit, hS₁, hS₂, Set.singleton_union, Set.ncard_pair hne]
  ·
    obtain ⟨E, -, -, -, -, -, hS⟩ := hone a ha b hb d hd hab hbd had
    rw [hS, Set.ncard_singleton]

end CFSG.Combinatorics.HexagonPeriodicPropagation
