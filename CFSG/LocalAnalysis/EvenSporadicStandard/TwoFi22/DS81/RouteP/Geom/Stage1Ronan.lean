module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Stage1Graph
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.OrbitRepsRonan
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Stage1Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Monster.B.Recog CFSG.Monster.GMS
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Levels

open Classical in
@[expose] noncomputable def lvl (v : Zp ⧸ XpZ) : ℕ :=
  if pt v = x1 then 0 else if Δ.Adj x1 (pt v) then 1 else 2

theorem lvl_eq_zero_iff {v : Zp ⧸ XpZ} : lvl v = 0 ↔ pt v = x1 := by
  by_cases h1 : pt v = x1
  · simp [lvl, h1]
  · by_cases h2 : Δ.Adj x1 (pt v) <;> simp [lvl, h1, h2]

theorem lvl_eq_one_iff {v : Zp ⧸ XpZ} : lvl v = 1 ↔ Δ.Adj x1 (pt v) := by
  by_cases h1 : pt v = x1
  · simp [lvl, h1]
  · by_cases h2 : Δ.Adj x1 (pt v) <;> simp [lvl, h1, h2]

theorem lvl_eq_two_iff {v : Zp ⧸ XpZ} : lvl v = 2 ↔ pt v ≠ x1 ∧ ¬ Δ.Adj x1 (pt v) := by
  by_cases h1 : pt v = x1
  · simp [lvl, h1]
  · by_cases h2 : Δ.Adj x1 (pt v) <;> simp [lvl, h1, h2]

theorem lvl_le_two (v : Zp ⧸ XpZ) : lvl v ≤ 2 := by
  unfold lvl
  split_ifs <;> omega

@[expose] def Rset (y : Ω) : Set (Zp ⧸ XpZ) := {v | pt v = x1 ∨ pt v = x2 ∨ pt v = y}

end Levels

section Subgroup

@[expose] noncomputable def KZ : Subgroup Zp := A1gen.subgroupOf Zp

theorem mem_KZ_iff {z : Zp} : z ∈ KZ ↔ (z : Q3) ∈ A1gen := Subgroup.mem_subgroupOf

theorem KZ_smul_x1 {k : Zp} (hk : k ∈ KZ) : (k : Q3) • x1 = x1 :=
  L0_smul_x1 (A1gen_le_L0 (mem_KZ_iff.1 hk))

theorem KZ_smul_base {k : Zp} (hk : k ∈ KZ) : k • base = base :=
  pt_injective (by rw [pt_smul, pt_base, KZ_smul_x1 hk])

theorem lvl_smul {k : Zp} (hk : k ∈ KZ) (v : Zp ⧸ XpZ) : lvl (k • v) = lvl v := by
  have hk1 := KZ_smul_x1 hk
  have e : pt (k • v) = (k : Q3) • pt v := pt_smul k v
  have h1 : pt (k • v) = x1 ↔ pt v = x1 := by
    rw [e]
    constructor
    · intro h
      apply smul_left_cancel (k : Q3)
      rw [h, hk1]
    · intro h
      rw [h, hk1]
  have h2 : Δ.Adj x1 (pt (k • v)) ↔ Δ.Adj x1 (pt v) := by
    have := Δ_adj_smul (k : Q3) x1 (pt v)
    rw [hk1] at this
    rw [e]
    exact this
  by_cases hv : pt v = x1
  · have h3 : pt (k • v) = x1 := h1.2 hv
    simp [lvl, hv, h3]
  · have h3 : ¬ pt (k • v) = x1 := fun h => hv (h1.1 h)
    by_cases ha : Δ.Adj x1 (pt v)
    · simp [lvl, hv, h3, ha, h2.2 ha]
    · simp [lvl, hv, h3, ha, mt h2.1 ha]

theorem exists_rep {y w : Ω} (S : Stage1Sem y w) (v : Zp ⧸ XpZ) :
    ∃ r ∈ Rset y, ∃ k ∈ KZ, k • r = v := by
  have hv0 := Δ_adj_x0_pt v
  rcases S.cover (pt v) hv0 with h | h | h
  · exact ⟨v, Or.inl h, 1, KZ.one_mem, one_smul _ _⟩
  · have hmem : pt v ∈ MulAction.orbit A1gen x2 := by
      rw [← commonNeighbors_x0_x1_eq, SimpleGraph.mem_commonNeighbors]
      exact ⟨hv0, h⟩
    obtain ⟨⟨a, ha⟩, hax⟩ := hmem
    have haZ : a ∈ Zp := (mem_L0_iff.1 (A1gen_le_L0 ha)).1
    have hr2 : pt ((s2Z : Zp) : Zp ⧸ XpZ) = x2 := by rw [pt_mk, s2Z_smul_x1]
    refine ⟨((s2Z : Zp) : Zp ⧸ XpZ), Or.inr (Or.inl hr2), ⟨a, haZ⟩, mem_KZ_iff.2 ha,
      pt_injective ?_⟩
    rw [pt_smul, hr2]
    exact hax
  · obtain ⟨⟨a, ha⟩, hay⟩ := h
    obtain ⟨ry, hry⟩ := exists_pt S.adj_x0_y
    have haZ : a ∈ Zp := (mem_L0_iff.1 (A1gen_le_L0 ha)).1
    refine ⟨ry, Or.inr (Or.inr hry), ⟨a, haZ⟩, mem_KZ_iff.2 ha, pt_injective ?_⟩
    rw [pt_smul, hry]
    exact hay

end Subgroup

section Distances

theorem dist_eq_lvl_of_sem {y w : Ω} (S : Stage1Sem y w) :
    (∀ v, Γ23.Reachable base v) ∧ ∀ v, Γ23.dist base v = lvl v := by
  refine dist_eq_of_level_of_reps Γ23_adj_smul KZ (a := base) (f := lvl) (R := Rset y)
    (fun k hk => KZ_smul_base hk) (fun k hk v => lvl_smul hk v) (exists_rep S)
    (lvl_eq_zero_iff.2 pt_base) ?_ ?_ ?_
  · intro r _ hr
    exact pt_injective ((lvl_eq_zero_iff.1 hr).trans pt_base.symm)
  · intro r hr k hk
    rcases hr with h | h | h
    · have := lvl_eq_zero_iff.2 h
      omega
    · have h1 : lvl r = 1 := lvl_eq_one_iff.2 (by rw [h]; exact Δ_adj_x1_x2)
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨base, (Γ23_adj_iff r base).2 (by rw [h, pt_base]; exact Δ_adj_x1_x2.symm),
        lvl_eq_zero_iff.2 pt_base⟩
    · have h2 : lvl r = 2 :=
        lvl_eq_two_iff.2 ⟨by rw [h]; exact S.ne_x1, by rw [h]; exact S.not_adj_x1_y⟩
      have hk1 : k = 1 := by omega
      subst hk1
      obtain ⟨n, hn⟩ := exists_pt S.adj_x0_w
      exact ⟨n, (Γ23_adj_iff r n).2 (by rw [h, hn]; exact S.adj_y_w),
        lvl_eq_one_iff.2 (by rw [hn]; exact S.adj_x1_w)⟩
  · intro r _ v hrv
    by_cases h0 : lvl r = 0
    · have h1 : pt r = x1 := lvl_eq_zero_iff.1 h0
      have h2 : Δ.Adj x1 (pt v) := by
        rw [← h1]
        exact (Γ23_adj_iff r v).1 hrv
      have := lvl_eq_one_iff.2 h2
      omega
    · have := lvl_le_two v
      omega

theorem pt_eq_of_rep_dist_two {y w : Ω} (S : Stage1Sem y w) {r : Zp ⧸ XpZ} (hr : r ∈ Rset y)
    (hdr : Γ23.dist base r = 2) : pt r = y := by
  have h2 : lvl r = 2 := ((dist_eq_lvl_of_sem S).2 r).symm.trans hdr
  obtain ⟨hne, hnadj⟩ := lvl_eq_two_iff.1 h2
  rcases hr with h | h | h
  · exact absurd h hne
  · exact absurd (by rw [h]; exact Δ_adj_x1_x2) hnadj
  · exact h

theorem Q_base_of_sem {y w : Ω} (S : Stage1Sem y w) {r : Zp ⧸ XpZ} (hr : pt r = y) :
    (Γ23.induce {c | Γ23.Adj base c ∧ Γ23.dist c r = 2 - 1}).Preconnected := by
  obtain ⟨r0, rk, ⟨hr0a, hr0b, hr0c⟩, hdesc⟩ := S.tree
  obtain ⟨n0, hn0⟩ := exists_pt hr0a
  have hmem : ∀ c, (Γ23.Adj base c ∧ Γ23.dist c r = 2 - 1) ↔
      (Δ.Adj x1 (pt c) ∧ Δ.Adj y (pt c)) := by
    intro c
    rw [Γ23_adj_base_iff, show (2 - 1 : ℕ) = 1 from rfl, SimpleGraph.dist_eq_one_iff_adj,
      Γ23_adj_iff, hr]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
  refine preconnected_induce_of_descent (r := n0)
    ((hmem n0).2 ⟨by rw [hn0]; exact hr0b, by rw [hn0]; exact hr0c⟩) (fun v => rk (pt v)) ?_
  intro v hv
  obtain ⟨hv1, hv2⟩ := (hmem v).1 hv
  rcases hdesc (pt v) (Δ_adj_x0_pt v) hv1 hv2 with h | ⟨p, ⟨hp0, hp1, hp2⟩, hvp, hlt⟩
  · exact Or.inl (pt_injective (h.trans hn0.symm))
  · obtain ⟨p', hp'⟩ := exists_pt hp0
    refine Or.inr ⟨p', (hmem p').2 ⟨by rw [hp']; exact hp1, by rw [hp']; exact hp2⟩, ?_, ?_⟩
    · exact (Γ23_adj_iff v p').2 (by rw [hp']; exact hvp)
    · show rk (pt p') < rk (pt v)
      rw [hp']
      exact hlt

theorem P_base_of_sem {y w : Ω} (S : Stage1Sem y w) {r g : Zp ⧸ XpZ} (hr : pt r = y)
    (hg : Γ23.dist base g = 2) (hrg : Γ23.Adj r g) :
    ∃ c, Γ23.Adj base c ∧ Γ23.Adj c r ∧ Γ23.Adj c g := by
  have hlvl : lvl g = 2 := ((dist_eq_lvl_of_sem S).2 g).symm.trans hg
  obtain ⟨hne, hnadj⟩ := lvl_eq_two_iff.1 hlvl
  have hyg : Δ.Adj y (pt g) := by
    have := (Γ23_adj_iff r g).1 hrg
    rwa [hr] at this
  rcases S.pick (pt g) (Δ_adj_x0_pt g) hyg with h | h | ⟨c, ⟨hc0, hc1, hc2⟩, hcg⟩
  · exact absurd h hne
  · exact absurd h hnadj
  · obtain ⟨c', hc'⟩ := exists_pt hc0
    exact ⟨c', (Γ23_adj_base_iff c').2 (by rw [hc']; exact hc1),
      (Γ23_adj_iff c' r).2 (by rw [hc', hr]; exact hc2.symm),
      (Γ23_adj_iff c' g).2 (by rw [hc']; exact hcg)⟩

end Distances

section Consequences

theorem Γ23_reachable_base (v : Zp ⧸ XpZ) : Γ23.Reachable base v := by
  obtain ⟨y, w, S⟩ := stage1_sem
  exact (dist_eq_lvl_of_sem S).1 v

theorem Γ23_connected : Γ23.Connected :=
  haveI : Nonempty (Zp ⧸ XpZ) := ⟨base⟩
  ⟨fun u v => (Γ23_reachable_base u).symm.trans (Γ23_reachable_base v)⟩

theorem Γ23_triangulable : Triangulable Γ23 := by
  obtain ⟨y, w, S⟩ := stage1_sem
  have hdist := dist_eq_lvl_of_sem S
  refine triangulable_of_ronan_of_reps (X := Zp) (V := Zp ⧸ XpZ) Γ23_adj_smul KZ (a₀ := base)
    (fun k hk => KZ_smul_base hk) (d := 2) (fun v => by rw [hdist.2 v]; exact lvl_le_two v)
    (R := Rset y) (exists_rep S) ?_ ?_
  · intro i hi2 hid r hr hdr
    obtain rfl : i = 2 := by omega
    exact Q_base_of_sem S (pt_eq_of_rep_dist_two S hr hdr)
  · intro i hi2 hid r hr hdr g hdg hrg
    obtain rfl : i = 2 := by omega
    obtain ⟨c, h1, h2, h3⟩ := P_base_of_sem S (pt_eq_of_rep_dist_two S hr hdr) hdg hrg
    refine ⟨c, c, h1, ?_, h1, ?_, Or.inl rfl⟩
    · exact SimpleGraph.dist_eq_one_iff_adj.2 h2
    · exact SimpleGraph.dist_eq_one_iff_adj.2 h3

end Consequences

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
