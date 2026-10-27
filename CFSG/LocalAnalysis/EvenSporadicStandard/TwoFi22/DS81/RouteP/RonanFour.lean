module

public import CFSG.Monster.B.GSide.HomotopyRonan

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.GMS CFSG.Monster.B.GSide

variable {V : Type*} {G : SimpleGraph V}

theorem exists_adj_dist_eq_of_dist_eq_succ {v h : V} {m : ℕ} (hvh : G.dist v h = m + 1) :
    ∃ c, G.Adj v c ∧ G.dist c h = m := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (G := G) (u := v) (v := h)
    (by rw [hvh]; omega)
  cases p with
  | nil => rw [Walk.length_nil] at hp; omega
  | @cons _ c _ hvc p' =>
    refine ⟨c, hvc, ?_⟩
    have hle : G.dist c h ≤ m := by
      have h₁ := SimpleGraph.dist_le p'
      rw [Walk.length_cons, hvh] at hp
      omega
    have hdiff := hvc.diff_dist_adj (u := h)
    rw [SimpleGraph.dist_comm (u := h) (v := v), hvh,
      SimpleGraph.dist_comm (u := h) (v := c)] at hdiff
    omega

theorem triangulable_of_ronan_of_common_lower {d : ℕ} (hd : ∀ x y : V, G.dist x y ≤ d)
    (hnbrs : ∀ i, 2 ≤ i → i ≤ d → ∀ a b, G.dist a b = i →
      (G.induce {c | G.Adj a c ∧ G.dist c b = i - 1}).Preconnected)
    (hlow : ∀ i, 2 ≤ i → i ≤ d → ∀ a x y, G.dist a x = i → G.dist a y = i → G.Adj x y →
      ∃ h, G.dist a h = i - 1 ∧ G.Adj h x ∧ G.Adj h y) :
    Triangulable G := by
  refine triangulable_of_ronan hd hnbrs (fun i hi hi' a b g hab hag hbg => ?_)
  obtain ⟨w, haw, hwb, hwg⟩ := hlow i hi hi' a b g hab hag hbg
  have hne : G.dist a w ≠ 0 := by omega
  have hawr : G.Reachable a w := Reachable.of_dist_ne_zero hne
  have hsucc : G.dist a w = (i - 2) + 1 := by omega
  obtain ⟨c, hac, hcw⟩ :=
    exists_adj_dist_eq_of_dist_eq_succ (v := a) (h := w) (m := i - 2) hsucc
  have hcwr : G.Reachable c w := hac.symm.reachable.trans hawr
  obtain ⟨δ, hδ⟩ := hcwr.exists_walk_length_eq_dist
  have key : ∀ {z : V}, G.Adj w z → G.dist a z = i → G.dist c z = i - 1 := by
    intro z hwz haz
    have hle : G.dist c z ≤ i - 1 := by
      have h₁ := SimpleGraph.dist_le (δ.append (Walk.cons hwz Walk.nil))
      rw [Walk.length_append, Walk.length_cons, Walk.length_nil, hδ, hcw] at h₁
      omega
    have hdiff := hac.diff_dist_adj (u := z)
    rw [SimpleGraph.dist_comm (u := z) (v := a), haz,
      SimpleGraph.dist_comm (u := z) (v := c)] at hdiff
    omega
  exact ⟨c, c, hac, key hwb hab, hac, key hwg hag, Or.inl rfl⟩

theorem triangulable_of_dist_le_four (hD : ∀ x y : V, G.dist x y ≤ 4)
    (h2 : ∀ v w : V, G.dist v w = 2 → (G.induce (G.commonNeighbors v w)).Preconnected)
    (h2t : ∀ v x y : V, G.dist v x = 2 → G.dist v y = 2 → G.Adj x y →
      ∃ c, G.Adj v c ∧ G.Adj c x ∧ G.Adj c y)
    (h3 : ∀ v u : V, G.dist v u = 3 →
      (G.induce {c | G.Adj u c ∧ G.dist v c = 2}).Preconnected)
    (h3t : ∀ v x y : V, G.dist v x = 3 → G.dist v y = 3 → G.Adj x y →
      ∃ h, G.dist v h = 2 ∧ G.Adj h x ∧ G.Adj h y)
    (h4 : ∀ v u : V, G.dist v u = 4 →
      (G.induce {c | G.Adj u c ∧ G.dist v c = 3}).Preconnected)
    (h4t : ∀ v x y : V, G.dist v x = 4 → G.dist v y = 4 → G.Adj x y →
      ∃ h, G.dist v h = 3 ∧ G.Adj h x ∧ G.Adj h y) :
    Triangulable G := by
  refine triangulable_of_ronan_of_common_lower (d := 4) hD
    (fun i hi hi' a b hab => ?_) (fun i hi hi' a x y hax hay hxy => ?_)
  · interval_cases i
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 1}).Preconnected
      rw [setOf_adj_dist_eq_one]
      exact h2 a b hab
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 2}).Preconnected
      have e : {c | G.Adj a c ∧ G.dist c b = 2} = {c | G.Adj a c ∧ G.dist b c = 2} := by
        ext c
        exact and_congr_right fun _ => by rw [SimpleGraph.dist_comm]
      rw [e]
      exact h3 b a (by rwa [SimpleGraph.dist_comm])
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 3}).Preconnected
      have e : {c | G.Adj a c ∧ G.dist c b = 3} = {c | G.Adj a c ∧ G.dist b c = 3} := by
        ext c
        exact and_congr_right fun _ => by rw [SimpleGraph.dist_comm]
      rw [e]
      exact h4 b a (by rwa [SimpleGraph.dist_comm])
  · interval_cases i
    · obtain ⟨c, hac, hcx, hcy⟩ := h2t a x y hax hay hxy
      exact ⟨c, dist_eq_one_iff_adj.mpr hac, hcx, hcy⟩
    · obtain ⟨w, haw, hwx, hwy⟩ := h3t a x y hax hay hxy
      exact ⟨w, haw, hwx, hwy⟩
    · obtain ⟨w, haw, hwx, hwy⟩ := h4t a x y hax hay hxy
      exact ⟨w, haw, hwx, hwy⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
