module

public import CFSG.Geometry.GeneralizedPolygons.Basic

public section

namespace CFSG.Geometry.GeneralizedPolygons

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {m : ℕ} [Fintype V] [DecidableRel G.Adj]

namespace IsGeneralizedPolygon

variable (hG : IsGeneralizedPolygon G m)
include hG

theorem degree_le_of_dist_eq (hm : 2 ≤ m) {x y : V} (hxy : G.dist x y = m) :
    G.degree x ≤ G.degree y := by
  classical
  have hyx : G.dist y x = m := by rw [dist_comm]; exact hxy
  have hpos : ∀ x', G.Adj x x' → G.dist x' y + 1 = m := fun x' hx' => by
    have := hG.dist_succ_of_dist_eq (by omega) hyx hx'
    rw [dist_comm]
    omega
  let f : V → V := fun x' =>
    if h : 0 < G.dist x' y then (hG.exists_adj_dist_succ h).choose else x'
  have hf : ∀ x', G.Adj x x' → G.Adj y (f x') ∧ G.dist x' (f x') + 1 = G.dist x' y :=
    fun x' hx' => by
      have h : 0 < G.dist x' y := by have := hpos x' hx'; omega
      simp only [f]
      rw [dite_eq_left h]
      exact (hG.exists_adj_dist_succ h).choose_spec
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn f (fun x' hx' => ?_) (fun x₁ h₁ x₂ h₂ e => ?_)
  · rw [Finset.mem_coe, mem_neighborFinset] at hx' ⊢
    exact (hf x' hx').1
  · rw [Finset.mem_coe, mem_neighborFinset] at h₁ h₂
    obtain ⟨hy₁, hd₁⟩ := hf x₁ h₁
    obtain ⟨hy₂, hd₂⟩ := hf x₂ h₂
    rw [← e] at hy₂ hd₂
    have hxy' : G.dist (f x₁) x + 1 = m := by
      have := hG.dist_succ_of_dist_eq (by omega) hxy hy₁
      rw [dist_comm]
      omega
    have e₁ : G.dist (f x₁) x₁ = G.dist x₁ (f x₁) := dist_comm
    have e₂ : G.dist (f x₁) x₂ = G.dist x₂ (f x₁) := dist_comm
    have := hpos x₁ h₁
    have := hpos x₂ h₂
    exact hG.eq_of_adj_of_dist_succ (y := f x₁) (v := x) (by omega) h₁ h₂ (by omega) (by omega)

theorem degree_eq_of_dist_eq (hm : 2 ≤ m) {x y : V} (hxy : G.dist x y = m) :
    G.degree x = G.degree y :=
  le_antisymm (hG.degree_le_of_dist_eq hm hxy)
    (hG.degree_le_of_dist_eq hm (by rw [dist_comm]; exact hxy))

theorem exists_dist_eq_dist_eq (hm : 2 ≤ m) (hthick : IsThick G) {w x z : V} (hx : G.Adj w x)
    (hz : G.Adj w z) : ∃ y, G.dist x y = m ∧ G.dist z y = m := by
  classical
  obtain ⟨u, hu, hux, huz⟩ : ∃ u, G.Adj w u ∧ u ≠ x ∧ u ≠ z := by
    have h3 := hthick w
    have : 0 < (((G.neighborFinset w).erase x).erase z).card := by
      have h1 := Finset.pred_card_le_card_erase (s := G.neighborFinset w) (a := x)
      have h2 := Finset.pred_card_le_card_erase (s := (G.neighborFinset w).erase x) (a := z)
      rw [card_neighborFinset_eq_degree] at h1
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.1 this
    simp only [Finset.mem_erase, mem_neighborFinset] at hu
    exact ⟨u, hu.2.2, hu.2.1, hu.1⟩
  obtain ⟨y, hwy, huy⟩ := hG.exists_dist_eq hthick hu (m - 1) (by omega) (by omega)
  have hyw : G.dist y w = m - 1 := by rw [dist_comm]; exact hwy
  have hyu : G.dist y u + 1 = G.dist y w := by rw [dist_comm, hyw]; omega
  have key : ∀ x', G.Adj w x' → x' ≠ u → G.dist x' y = m := fun x' hx' hne => by
    rcases hG.dist_adj hx' y with h | h
    · rw [dist_comm, h, hyw]
      omega
    · exact absurd (hG.eq_of_adj_of_dist_succ (by omega) hx' hu h.symm hyu) hne
  exact ⟨y, key x hx (Ne.symm hux), key z hz (Ne.symm huz)⟩

theorem degree_eq_of_adj_of_adj (hm : 2 ≤ m) (hthick : IsThick G) {w x z : V}
    (hx : G.Adj w x) (hz : G.Adj w z) : G.degree x = G.degree z := by
  obtain ⟨y, hxy, hzy⟩ := hG.exists_dist_eq_dist_eq hm hthick hx hz
  rw [hG.degree_eq_of_dist_eq hm hxy, hG.degree_eq_of_dist_eq hm hzy]

theorem degree_eq_of_coloring_eq (hm : 2 ≤ m) (hthick : IsThick G) (c : G.Coloring (Fin 2))
    {x x' : V} (h : c x = c x') : G.degree x = G.degree x' := by
  obtain ⟨p, -⟩ := hG.connected.exists_walk_length_eq_dist x x'
  have heven : Even p.length := (eq_iff_even_length c p).1 h
  have step : ∀ i, i + 2 ≤ p.length → G.degree (p.getVert i) = G.degree (p.getVert (i + 2)) :=
    fun i hi => hG.degree_eq_of_adj_of_adj hm hthick (p.adj_getVert_succ (by omega)).symm
      (p.adj_getVert_succ (by omega))
  have hj : ∀ j, 2 * j ≤ p.length → G.degree (p.getVert (2 * j)) = G.degree x := by
    intro j
    induction j with
    | zero => intro _; rw [Nat.mul_zero, Walk.getVert_zero]
    | succ j ih =>
      intro hj
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, ← step _ (by omega), ih (by omega)]
  obtain ⟨j, hj'⟩ := heven
  have := hj j (by omega)
  rw [show 2 * j = p.length by omega, Walk.getVert_length] at this
  exact this.symm

theorem exists_order (hm : 2 ≤ m) (hthick : IsThick G) (c : G.Coloring (Fin 2)) :
    ∃ s t : ℕ, 2 ≤ s ∧ 2 ≤ t ∧ (Odd m → s = t) ∧
      ∀ v, G.degree v = if c v = 0 then t + 1 else s + 1 := by
  classical
  have hfin2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hne : Nonempty V := by
    have := nontrivial_of_diam_ne_zero (G := G) (by rw [hG.diam_eq]; omega)
    infer_instance
  obtain ⟨v₀⟩ := id hne
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, G.Adj v₀ v₁ := by
    have h3 := hthick v₀
    obtain ⟨v₁, hv₁⟩ := Finset.card_pos.1
      (show 0 < (G.neighborFinset v₀).card by rw [card_neighborFinset_eq_degree]; omega)
    exact ⟨v₁, (mem_neighborFinset _ _ _).1 hv₁⟩
  have hc := c.valid hv₁
  obtain ⟨x₀, x₁, hx₀, hx₁⟩ : ∃ x₀ x₁, c x₀ = 0 ∧ c x₁ = 1 := by
    rcases hfin2 (c v₀) with h | h
    · rcases hfin2 (c v₁) with h' | h'
      · exact absurd (h.trans h'.symm) hc
      · exact ⟨v₀, v₁, h, h'⟩
    · rcases hfin2 (c v₁) with h' | h'
      · exact ⟨v₁, v₀, h', h⟩
      · exact absurd (h.trans h'.symm) hc
  have hdeg : ∀ v, G.degree v = if c v = 0 then G.degree x₀ else G.degree x₁ := fun v => by
    split_ifs with h
    · exact hG.degree_eq_of_coloring_eq hm hthick c (h.trans hx₀.symm)
    · have h1 : c v = 1 := (hfin2 (c v)).resolve_left h
      exact hG.degree_eq_of_coloring_eq hm hthick c (h1.trans hx₁.symm)
  have h0 := hthick x₀
  have h1 := hthick x₁
  refine ⟨G.degree x₁ - 1, G.degree x₀ - 1, by omega, by omega, fun hodd => ?_, fun v => ?_⟩
  · obtain ⟨x, y, hxy⟩ := exists_dist_eq_diam (G := G)
    rw [hG.diam_eq] at hxy
    have hcxy : c x ≠ c y := fun e => by
      rw [hG.eq_iff_even_dist c, hxy] at e
      exact Nat.not_even_iff_odd.2 hodd e
    have hd := hG.degree_eq_of_dist_eq hm hxy
    rw [hdeg x, hdeg y] at hd
    rcases hfin2 (c x) with h | h
    · have h' : c y ≠ 0 := fun e => hcxy (h.trans e.symm)
      rw [ite_eq_left h, ite_eq_right h'] at hd
      omega
    · have h' : c y = 0 := (hfin2 (c y)).resolve_right fun e => hcxy (h.trans e.symm)
      rw [ite_eq_right (by rw [h]; decide), ite_eq_left h'] at hd
      omega
  · rw [hdeg v]
    split_ifs <;> omega

end IsGeneralizedPolygon

end CFSG.Geometry.GeneralizedPolygons
