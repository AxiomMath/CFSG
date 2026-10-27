module

public import CFSG.Certificates.Kernel.SporLatDc2Lev1

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (sumN sortedLt_iff_pairwise)
open MulAction

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

theorem meets_smul {j : ℕ} (hj : j < P.D.bo.length) {g : Γ} (hg : g ∈ P.S) (y : PtL n) :
    P.meets (g • y) j ↔ P.meets y j := by
  have hb := P.parts.2.1 j hj
  constructor
  · rintro ⟨q, hq, hi⟩
    obtain ⟨p, hp, rfl⟩ := mem_smul_val.1 hq
    refine ⟨p, hp, ?_⟩
    rw [← act_val (y.valid.2 p hp), P.inO_smul_iff hb hg] at hi
    exact hi
  · rintro ⟨p, hp, hi⟩
    refine ⟨act n g p, mem_smul_val.2 ⟨p, hp, rfl⟩, ?_⟩
    rw [← act_val (y.valid.2 p hp), P.inO_smul_iff hb hg]
    exact hi

theorem mode_spec {r : Rec1} (hr : rec1OK P.C P.D r = true) :
    (r.mode = 0 → ∀ j < P.D.bo.length, ¬ P.meets (P.xr r) j) ∧
    (∀ i, r.mode = i + 1 →
      i < P.D.bo.length ∧ (∀ j < i, ¬ P.meets (P.xr r) j) ∧ P.meets (P.xr r) i) := by
  obtain ⟨-, -, h0, hi⟩ := P.rec1_facts hr
  refine ⟨fun h => (P.modeE_facts (h0 h)).1, fun i h => ?_⟩
  obtain ⟨hiB, hmiss, hpos, -⟩ := P.modeB_facts (hi i h)
  exact ⟨hiB, hmiss, P.meets_of_pos hpos⟩

theorem mode_eq {r r' : Rec1} (hr : rec1OK P.C P.D r = true) (hr' : rec1OK P.C P.D r' = true)
    (h : P.xr r' ∈ orbit P.S (P.xr r)) : r.mode = r'.mode := by
  obtain ⟨⟨g, hg⟩, he⟩ := h
  have hm : ∀ j < P.D.bo.length, (P.meets (P.xr r') j ↔ P.meets (P.xr r) j) := fun j hj => by
    rw [← he]
    exact P.meets_smul hj hg _
  obtain ⟨a0, ai⟩ := P.mode_spec hr
  obtain ⟨b0, bi⟩ := P.mode_spec hr'
  rcases h1 : r.mode with _ | i <;> rcases h2 : r'.mode with _ | i'
  · rfl
  · obtain ⟨hB, -, hmt⟩ := bi i' h2
    exact absurd ((hm _ hB).1 hmt) (a0 h1 _ hB)
  · obtain ⟨hB, -, hmt⟩ := ai i h1
    exact absurd ((hm _ hB).2 hmt) (b0 h2 _ hB)
  · obtain ⟨hB1, hmiss1, hmt1⟩ := ai i h1
    obtain ⟨hB2, hmiss2, hmt2⟩ := bi i' h2
    rcases lt_trichotomy i i' with hlt | rfl | hgt
    · exact absurd ((hm _ hB1).2 hmt1) (hmiss2 _ hlt)
    · rfl
    · exact absurd ((hm _ hB2).1 hmt2) (hmiss1 _ hgt)

theorem key_eq {r r' : Rec1} (hr : rec1OK P.C P.D r = true) (hr' : rec1OK P.C P.D r' = true)
    (h : P.xr r' ∈ orbit P.S (P.xr r)) : r.key = r'.key := by
  have hmode := P.mode_eq hr hr' h
  have horb : orbit P.S (P.xr r') = orbit P.S (P.xr r) := orbit_eq_iff.2 h
  have hcl : clSet n r.cl = clSet n r'.cl := by
    rcases hm : r.mode with _ | i
    · rw [P.clSet_mode0 hr hm, P.clSet_mode0 hr' (hmode.symm.trans hm), horb]
    · rw [P.clSet_modeB hr hm, P.clSet_modeB hr' (hmode.symm.trans hm), horb]
  obtain ⟨-, hk, -⟩ := P.rec1_facts hr
  obtain ⟨-, hk', -⟩ := P.rec1_facts hr'
  obtain ⟨hp, hs, -, hpos, hv⟩ := P.cl_facts hr
  obtain ⟨hp', hs', -, -, hv'⟩ := P.cl_facts hr'
  rw [hk, hk', hmode]
  congr 1
  refine headL_eq_of_mem_iff hs hs' (List.ne_nil_of_length_pos (by rw [hp.length_eq]; exact hpos))
    fun y => ?_
  rw [hp.mem_iff, hp'.mem_iff]
  constructor
  · intro hy
    obtain ⟨z, rfl⟩ := hv _ hy
    have h1 : z ∈ clSet n r.cl := hy
    rw [hcl] at h1
    exact h1
  · intro hy
    obtain ⟨z, rfl⟩ := hv' _ hy
    have h1 : z ∈ clSet n r'.cl := hy
    rw [← hcl] at h1
    exact h1

@[expose] def U1 (l : List Rec1) : Set (PtL n) := {y | ∃ r ∈ l, y ∈ orbit P.S (P.xr r)}

theorem U1_sub (l : List Rec1) : P.U1 l ⊆ orbit Γ P.Λl := by
  rintro y ⟨r, -, ⟨⟨g, -⟩, rfl⟩⟩
  exact ⟨g * P.elt r.u, mul_smul _ _ _⟩

theorem ncard_U1 (l : List Rec1) (h : ∀ r ∈ l, rec1OK P.C P.D r = true)
    (hp : (l.map Rec1.key).Pairwise (· < ·)) : (P.U1 l).ncard = sumN (l.map Rec1.m) := by
  induction l with
  | nil => simp [U1, sumN]
  | cons a l ih =>
    have hU : P.U1 (a :: l) = orbit P.S (P.xr a) ∪ P.U1 l := by
      ext y
      simp only [U1, List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨r, rfl | hr, hy⟩
        exacts [Or.inl hy, Or.inr ⟨r, hr, hy⟩]
      · rintro (hy | ⟨r, hr, hy⟩)
        exacts [⟨a, Or.inl rfl, hy⟩, ⟨r, Or.inr hr, hy⟩]
    rw [List.map_cons, List.pairwise_cons] at hp
    have hdisj : Disjoint (orbit P.S (P.xr a)) (P.U1 l) := by
      rw [Set.disjoint_left]
      rintro y hy ⟨r, hr, hy'⟩
      have e : orbit P.S (P.xr r) = orbit P.S (P.xr a) :=
        (orbit_eq_iff.2 hy').symm.trans (orbit_eq_iff.2 hy)
      have hk := P.key_eq (h a List.mem_cons_self) (h r (List.mem_cons_of_mem _ hr))
        (orbit_eq_iff.1 e)
      have hlt := hp.1 r.key (List.mem_map_of_mem hr)
      rw [hk] at hlt
      exact lt_irrefl _ hlt
    rw [hU, Set.ncard_union_eq hdisj (Set.finite_range _)
      ((Set.finite_range _).subset (P.U1_sub l)), P.ncard_orbit_xr (h a List.mem_cons_self),
      ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) hp.2]
    rfl

theorem rec1OK_of_mem {r : Rec1} (hr : r ∈ P.D.R1) : rec1OK P.C P.D r = true := by
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hr
  have e := P.parts.2.2.1 c hc
  rwa [List.getD_eq_getElem _ _ hc] at e

theorem ncard_lev1 : (P.U1 P.D.R1).ncard = P.C.N1 := by
  rw [P.ncard_U1 _ (fun r hr => P.rec1OK_of_mem hr)
    ((sortedLt_iff_pairwise _).1 P.glob.2.2.2.2.2.2.2.2.2.1), P.glob.2.2.2.2.2.2.2.2.2.2]

end Dc2SoundCtx

end CFSG.KC.SLD2

end
