module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Level2
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.RonanFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Spheres

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open SimpleGraph CFSG.Monster.B.Recog
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Transport


theorem commonNeighbors_smul (g : Q3) (a b : Ω) :
    Δ.commonNeighbors (g • a) (g • b) = (g • ·) '' Δ.commonNeighbors a b := by
  ext c
  constructor
  · intro h
    rw [SimpleGraph.mem_commonNeighbors] at h
    refine ⟨g⁻¹ • c, ?_, smul_inv_smul g c⟩
    rw [SimpleGraph.mem_commonNeighbors]
    constructor
    · rw [← Δ_adj_smul g, smul_inv_smul]
      exact h.1
    · rw [← Δ_adj_smul g, smul_inv_smul]
      exact h.2
  · rintro ⟨c', hc', rfl⟩
    rw [SimpleGraph.mem_commonNeighbors] at hc' ⊢
    exact ⟨(Δ_adj_smul g _ _).2 hc'.1, (Δ_adj_smul g _ _).2 hc'.2⟩

theorem nbrs_smul (g : Q3) (u v : Ω) (k : ℕ) :
    {c | Δ.Adj (g • u) c ∧ Δ.dist (g • v) c = k} =
      (g • ·) '' {c | Δ.Adj u c ∧ Δ.dist v c = k} := by
  ext c
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ • c, ⟨?_, ?_⟩, smul_inv_smul g c⟩
    · rw [← Δ_adj_smul g, smul_inv_smul]
      exact h1
    · rw [← dist_smul Δ_adj_smul g, smul_inv_smul]
      exact h2
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩
    exact ⟨(Δ_adj_smul g _ _).2 h1, by rw [dist_smul Δ_adj_smul]; exact h2⟩

theorem preconnected_forall_rep {S : Ω → Ω → Set Ω} {n : ℕ}
    (hS : ∀ (g : Q3) (a b : Ω), S (g • a) (g • b) = (g • ·) '' S a b) {R : List Ω}
    (hR : ∀ w, Δ.dist x0 w = n → ∃ r ∈ R, ∃ k ∈ Zp, k • r = w)
    (h : ∀ r ∈ R, Δ.dist x0 r = n → (Δ.induce (S x0 r)).Preconnected) :
    ∀ v w : Ω, Δ.dist v w = n → (Δ.induce (S v w)).Preconnected := by
  refine forall_imp_of_forall_rep (W := Ω) (a₀ := x0) Zp (fun k hk => Zp_smul_x0 hk)
    (H := fun a w => Δ.dist a w = n) (C := fun a w => (Δ.induce (S a w)).Preconnected)
    (fun g a w => by rw [dist_smul Δ_adj_smul]) (fun g a w hw => ?_) hR h
  rw [hS]
  exact preconnected_induce_image Δ_adj_smul g hw

theorem tri_smul {n : ℕ} {L : Ω → Ω → Prop} (hL : ∀ (g : Q3) (a c : Ω), L (g • a) (g • c) ↔ L a c)
    (g : Q3) {a x : Ω}
    (h : ∀ y, Δ.dist a y = n → Δ.Adj x y → ∃ c, L a c ∧ Δ.Adj c x ∧ Δ.Adj c y) :
    ∀ y, Δ.dist (g • a) y = n → Δ.Adj (g • x) y →
      ∃ c, L (g • a) c ∧ Δ.Adj c (g • x) ∧ Δ.Adj c y := by
  intro y hy hxy
  have hy' : Δ.dist a (g⁻¹ • y) = n := by
    rw [← dist_smul_left Δ_adj_smul]
    exact hy
  obtain ⟨c, hLc, hcx, hcy⟩ := h _ hy' ((adj_smul_left_iff Δ_adj_smul g x y).1 hxy)
  refine ⟨g • c, (hL g a c).2 hLc, (Δ_adj_smul g _ _).2 hcx, ?_⟩
  have := (Δ_adj_smul g _ _).2 hcy
  rwa [smul_inv_smul] at this

theorem tri_forall_rep {n : ℕ} {L : Ω → Ω → Prop}
    (hL : ∀ (g : Q3) (a c : Ω), L (g • a) (g • c) ↔ L a c) {R : List Ω}
    (hR : ∀ w, Δ.dist x0 w = n → ∃ r ∈ R, ∃ k ∈ Zp, k • r = w)
    (h : ∀ r ∈ R, Δ.dist x0 r = n → ∀ y, Δ.dist x0 y = n → Δ.Adj r y →
      ∃ c, L x0 c ∧ Δ.Adj c r ∧ Δ.Adj c y) :
    ∀ v x y : Ω, Δ.dist v x = n → Δ.dist v y = n → Δ.Adj x y →
      ∃ c, L v c ∧ Δ.Adj c x ∧ Δ.Adj c y := by
  have key := forall_imp_of_forall_rep (W := Ω) (a₀ := x0) Zp (fun k hk => Zp_smul_x0 hk)
    (H := fun a x => Δ.dist a x = n)
    (C := fun a x => ∀ y, Δ.dist a y = n → Δ.Adj x y → ∃ c, L a c ∧ Δ.Adj c x ∧ Δ.Adj c y)
    (fun g a x => by rw [dist_smul Δ_adj_smul]) (fun g a x hx => tri_smul hL g hx) hR h
  exact fun v x y hx hy hxy => key v x hx y hy hxy

end Transport

section Ronan


theorem ronan_h2 : ∀ v w : Ω, Δ.dist v w = 2 →
    (Δ.induce (Δ.commonNeighbors v w)).Preconnected :=
  preconnected_forall_rep (S := Δ.commonNeighbors) commonNeighbors_smul (R := [y2])
    (fun _ hw => exists_mem_repsDist_two hw) fun r hr _ => by
      obtain rfl := List.mem_singleton.1 hr
      exact Q_connected

theorem ronan_h2t : ∀ v x y : Ω, Δ.dist v x = 2 → Δ.dist v y = 2 → Δ.Adj x y →
    ∃ c, Δ.Adj v c ∧ Δ.Adj c x ∧ Δ.Adj c y :=
  tri_forall_rep (L := Δ.Adj) Δ_adj_smul (R := [y2]) (fun _ hw => exists_mem_repsDist_two hw)
    fun r hr _ y hy hadj => by
      obtain rfl := List.mem_singleton.1 hr
      exact P_witness hy hadj

theorem ronan_h3 : ∀ v u : Ω, Δ.dist v u = 3 →
    (Δ.induce {c | Δ.Adj u c ∧ Δ.dist v c = 2}).Preconnected :=
  preconnected_forall_rep (S := fun v u => {c | Δ.Adj u c ∧ Δ.dist v c = 2})
    (fun g a b => nbrs_smul g b a 2) (R := [y3a, y3b])
    (fun _ hw => exists_mem_repsDist_three hw) fun r hr _ => by
      rcases List.mem_pair.1 hr with rfl | rfl
      · exact A3_connected_a
      · exact A3_connected_b

theorem ronan_h3t : ∀ v x y : Ω, Δ.dist v x = 3 → Δ.dist v y = 3 → Δ.Adj x y →
    ∃ h, Δ.dist v h = 2 ∧ Δ.Adj h x ∧ Δ.Adj h y :=
  tri_forall_rep (L := fun a c => Δ.dist a c = 2) (fun g a c => by rw [dist_smul Δ_adj_smul])
    (R := [y3a, y3b]) (fun _ hw => exists_mem_repsDist_three hw) fun r hr _ y hy hadj => by
      rcases List.mem_pair.1 hr with rfl | rfl
      · exact Hp_witness_a hy hadj
      · exact Hp_witness_b hy hadj

theorem ronan_h4 : ∀ v u : Ω, Δ.dist v u = 4 →
    (Δ.induce {c | Δ.Adj u c ∧ Δ.dist v c = 3}).Preconnected :=
  preconnected_forall_rep (S := fun v u => {c | Δ.Adj u c ∧ Δ.dist v c = 3})
    (fun g a b => nbrs_smul g b a 3) (R := [y4a, y4b])
    (fun _ hw => exists_mem_repsDist_four hw) fun r hr _ => by
      rcases List.mem_pair.1 hr with rfl | rfl
      · exact A4_connected_a
      · exact A4_connected_b

theorem ronan_h4t : ∀ v x y : Ω, Δ.dist v x = 4 → Δ.dist v y = 4 → Δ.Adj x y →
    ∃ h, Δ.dist v h = 3 ∧ Δ.Adj h x ∧ Δ.Adj h y :=
  tri_forall_rep (L := fun a c => Δ.dist a c = 3) (fun g a c => by rw [dist_smul Δ_adj_smul])
    (R := [y4a, y4b]) (fun _ hw => exists_mem_repsDist_four hw) fun r hr _ y hy hadj => by
      rcases List.mem_pair.1 hr with rfl | rfl
      · exact absurd (hy.symm.trans (dist_x0_eq_three_of_adj_y4a hadj)) (by omega)
      · exact absurd (hy.symm.trans (dist_x0_eq_three_of_adj_y4b hadj)) (by omega)

theorem Δ_triangulable : CFSG.Monster.B.Recog.Triangulable Δ :=
  triangulable_of_dist_le_four Δ_dist_le_four ronan_h2 ronan_h2t ronan_h3 ronan_h3t ronan_h4
    ronan_h4t

end Ronan

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
