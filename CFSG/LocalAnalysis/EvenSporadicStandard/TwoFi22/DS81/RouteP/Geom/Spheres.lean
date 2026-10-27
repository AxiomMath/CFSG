module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Dist

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native

section Spheres


theorem orbLabel_eq_iff (i : Fin 7) (v : Ω) :
    orbLabel v = i.val ↔ v ∈ MulAction.orbit Zp (repPt i) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_mem_orbit_repPt v
    have h' : orbLabel v = j.val := by
      rw [orbLabel_eq_of_mem_orbit hj, orbLabel_repPt]
    have : j = i := Fin.ext (h'.symm.trans h)
    exact this ▸ hj
  · intro h
    rw [orbLabel_eq_of_mem_orbit h, orbLabel_repPt]

theorem distLevel_eq_iff (n : ℕ) (v : Ω) :
    distLevel v = n ↔
      ∃ i : Fin 7, geomLevels[i.val]! = n ∧ v ∈ MulAction.orbit Zp (repPt i) := by
  constructor
  · intro h
    refine ⟨⟨orbLabel v, orbLabel_lt v⟩, h, ?_⟩
    exact (orbLabel_eq_iff ⟨orbLabel v, orbLabel_lt v⟩ v).1 rfl
  · rintro ⟨i, hi, hv⟩
    rw [distLevel_eq_of_mem_orbit hv, distLevel_repPt, hi]

theorem eq_of_mem_orbit_repPt_of_size_one {i : Fin 7} (hi : geomSizes[i.val]! = 1) {v : Ω}
    (hv : v ∈ MulAction.orbit Zp (repPt i)) : v = repPt i := by
  have h1 := card_orbit_repPt i
  rw [hi, Nat.card_eq_one_iff_unique] at h1
  obtain ⟨h1, -⟩ := h1
  exact congrArg Subtype.val (h1.elim ⟨v, hv⟩ ⟨repPt i, MulAction.mem_orbit_self _⟩)

theorem dist_x0_eq_zero_iff (v : Ω) : Δ.dist x0 v = 0 ↔ v = x0 := by
  rw [(Δ_reachable_x0 v).dist_eq_zero_iff]
  exact eq_comm

theorem dist_x0_eq_one_iff (v : Ω) : Δ.dist x0 v = 1 ↔ v ∈ MulAction.orbit Zp x1 := by
  rw [SimpleGraph.dist_eq_one_iff_adj, Δ_adj_x0_iff]

theorem dist_x0_eq_two_iff (v : Ω) : Δ.dist x0 v = 2 ↔ v ∈ MulAction.orbit Zp y2 := by
  rw [Δ_dist_x0, distLevel_eq_iff]
  have key : ∀ i : Fin 7, geomLevels[i.val]! = 2 → i = 2 := by decide
  constructor
  · rintro ⟨i, hi, hv⟩
    obtain rfl := key i hi
    exact hv
  · intro hv
    exact ⟨2, by decide, hv⟩

theorem dist_x0_eq_three_iff (v : Ω) :
    Δ.dist x0 v = 3 ↔ v ∈ MulAction.orbit Zp y3a ∨ v ∈ MulAction.orbit Zp y3b := by
  rw [Δ_dist_x0, distLevel_eq_iff]
  have key : ∀ i : Fin 7, geomLevels[i.val]! = 3 → i = 3 ∨ i = 4 := by decide
  constructor
  · rintro ⟨i, hi, hv⟩
    rcases key i hi with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (hv | hv)
    · exact ⟨3, by decide, hv⟩
    · exact ⟨4, by decide, hv⟩

theorem eq_y4a_of_mem_orbit {v : Ω} (hv : v ∈ MulAction.orbit Zp y4a) : v = y4a :=
  eq_of_mem_orbit_repPt_of_size_one (i := 5) (by decide) hv

theorem eq_y4b_of_mem_orbit {v : Ω} (hv : v ∈ MulAction.orbit Zp y4b) : v = y4b :=
  eq_of_mem_orbit_repPt_of_size_one (i := 6) (by decide) hv

theorem dist_x0_eq_four_iff (v : Ω) : Δ.dist x0 v = 4 ↔ v = y4a ∨ v = y4b := by
  rw [Δ_dist_x0, distLevel_eq_iff]
  have key : ∀ i : Fin 7, geomLevels[i.val]! = 4 → i = 5 ∨ i = 6 := by decide
  constructor
  · rintro ⟨i, hi, hv⟩
    rcases key i hi with rfl | rfl
    · exact Or.inl (eq_y4a_of_mem_orbit hv)
    · exact Or.inr (eq_y4b_of_mem_orbit hv)
  · rintro (rfl | rfl)
    · exact ⟨5, by decide, MulAction.mem_orbit_self _⟩
    · exact ⟨6, by decide, MulAction.mem_orbit_self _⟩

theorem dist_x0_ne_of_four_lt {n : ℕ} (hn : 4 < n) (v : Ω) : Δ.dist x0 v ≠ n := by
  have := Δ_dist_x0_le_four v
  omega

theorem dist_x0_x1 : Δ.dist x0 x1 = 1 := (dist_x0_eq_one_iff x1).2 (MulAction.mem_orbit_self _)

theorem dist_x0_y2 : Δ.dist x0 y2 = 2 := (dist_x0_eq_two_iff y2).2 (MulAction.mem_orbit_self _)

theorem dist_x0_y3a : Δ.dist x0 y3a = 3 :=
  (dist_x0_eq_three_iff y3a).2 (Or.inl (MulAction.mem_orbit_self _))

theorem dist_x0_y3b : Δ.dist x0 y3b = 3 :=
  (dist_x0_eq_three_iff y3b).2 (Or.inr (MulAction.mem_orbit_self _))

theorem dist_x0_y4a : Δ.dist x0 y4a = 4 := (dist_x0_eq_four_iff y4a).2 (Or.inl rfl)

theorem dist_x0_y4b : Δ.dist x0 y4b = 4 := (dist_x0_eq_four_iff y4b).2 (Or.inr rfl)

theorem exists_mem_repsDist_two {b : Ω} (hb : Δ.dist x0 b = 2) :
    ∃ r ∈ [y2], ∃ k ∈ Zp, k • r = b := by
  obtain ⟨⟨k, hk⟩, hkb⟩ := (dist_x0_eq_two_iff b).1 hb
  exact ⟨y2, List.mem_singleton_self _, k, hk, hkb⟩

theorem exists_mem_repsDist_three {b : Ω} (hb : Δ.dist x0 b = 3) :
    ∃ r ∈ [y3a, y3b], ∃ k ∈ Zp, k • r = b := by
  rcases (dist_x0_eq_three_iff b).1 hb with ⟨⟨k, hk⟩, hkb⟩ | ⟨⟨k, hk⟩, hkb⟩
  · exact ⟨y3a, by simp, k, hk, hkb⟩
  · exact ⟨y3b, by simp, k, hk, hkb⟩

theorem exists_mem_repsDist_four {b : Ω} (hb : Δ.dist x0 b = 4) :
    ∃ r ∈ [y4a, y4b], ∃ k ∈ Zp, k • r = b := by
  rcases (dist_x0_eq_four_iff b).1 hb with rfl | rfl
  · exact ⟨y4a, by simp, 1, Subgroup.one_mem _, one_smul _ _⟩
  · exact ⟨y4b, by simp, 1, Subgroup.one_mem _, one_smul _ _⟩

theorem ncard_dist_x0_eq_zero : {v : Ω | Δ.dist x0 v = 0}.ncard = 1 := by
  have : {v : Ω | Δ.dist x0 v = 0} = {x0} := Set.ext fun v => dist_x0_eq_zero_iff v
  rw [this, Set.ncard_singleton]

theorem ncard_dist_x0_eq_one : {v : Ω | Δ.dist x0 v = 1}.ncard = 31671 := by
  have : {v : Ω | Δ.dist x0 v = 1} = MulAction.orbit Zp (repPt 1) := by
    ext v
    rw [repPt_one]
    exact dist_x0_eq_one_iff v
  rw [this, ← Nat.card_coe_set_eq]
  exact card_orbit_repPt 1

theorem ncard_dist_x0_eq_two : {v : Ω | Δ.dist x0 v = 2}.ncard = 825792 := by
  have : {v : Ω | Δ.dist x0 v = 2} = MulAction.orbit Zp (repPt 2) :=
    Set.ext fun v => dist_x0_eq_two_iff v
  rw [this, ← Nat.card_coe_set_eq]
  exact card_orbit_repPt 2

theorem ncard_dist_x0_eq_three : {v : Ω | Δ.dist x0 v = 3}.ncard = 63342 := by
  have hset : {v : Ω | Δ.dist x0 v = 3} =
      MulAction.orbit Zp (repPt 3) ∪ MulAction.orbit Zp (repPt 4) :=
    Set.ext fun v => dist_x0_eq_three_iff v
  have hdisj : Disjoint (MulAction.orbit Zp (repPt 3) : Set Ω)
      (MulAction.orbit Zp (repPt 4) : Set Ω) := by
    rw [Set.disjoint_left]
    intro v hv3 hv4
    have h3 := (orbLabel_eq_iff 3 v).2 hv3
    have h4 := (orbLabel_eq_iff 4 v).2 hv4
    omega
  rw [hset, Set.ncard_union_eq hdisj, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    card_orbit_repPt, card_orbit_repPt]
  rfl

theorem ncard_dist_x0_eq_four : {v : Ω | Δ.dist x0 v = 4}.ncard = 2 := by
  have : {v : Ω | Δ.dist x0 v = 4} = {y4a, y4b} := by
    ext v
    simpa using dist_x0_eq_four_iff v
  have hne : y4a ≠ y4b := by
    intro h
    have := congrArg Fin.val h
    revert this
    decide
  rw [this, Set.ncard_pair hne]

theorem Δ_dist_distribution :
    (List.range 5).map (fun n => {v : Ω | Δ.dist x0 v = n}.ncard) =
      [1, 31671, 825792, 63342, 2] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.map_append, ncard_dist_x0_eq_zero, ncard_dist_x0_eq_one, ncard_dist_x0_eq_two,
    ncard_dist_x0_eq_three, ncard_dist_x0_eq_four]
  rfl

end Spheres

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
