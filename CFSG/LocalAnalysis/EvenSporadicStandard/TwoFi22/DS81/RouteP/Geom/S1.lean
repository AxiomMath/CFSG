module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Dist

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem s1OK_spec {objs : Array Table} {trees : Array CFSG.Perm.Native.Tree}
    {atree : CFSG.Perm.Native.Tree} (h : s1OK objs trees atree = true) :
    (∀ l ∈ geomA1Letters, ap objs[l]! 0 = 0 ∧ ap objs[l]! 1479 = 1479) ∧
      atree.pts.size = 3510 ∧
      CFSG.Perm.Native.treeOK degree 99705 atree objs geomA1Letters = true ∧
      ∀ c ∈ trees[1]!.pts, memTree trees[1]! (ap objs[tauReg]! c.toNat) = true →
        memTree atree (ap objs[tauReg]! c.toNat) = true := by
  unfold s1OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun l hl => ?_, h2, h3, fun c hc hm => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hl
    simpa using h1 j hj
  · obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hc
    have := h4 j hj
    simpa [hm] using this

theorem memTree_of_exists {T : CFSG.Perm.Native.Tree}
    (hpos : ∀ k < T.pts.size, ap T.pos (ap T.pts k) = k) {p : ℕ}
    (h : ∃ k < T.pts.size, ap T.pts k = p) : memTree T p = true := by
  obtain ⟨k, hk, rfl⟩ := h
  simp only [memTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [hpos k hk]
  exact ⟨hk, rfl⟩

section Soundness

@[expose] noncomputable def A1gen : Subgroup Q3 :=
  CFSG.Perm.lettersGroup geomA1Letters objElt

theorem rep_objElt_of_mem {l : ℕ} (hl : l ∈ geomA1Letters) :
    CFSG.Sporadic.Th.Rep 920808 objTabs[l]! (objElt l) :=
  rep_objElt (by simp [geomA1Letters] at hl; omega)

theorem objElt_smul_x0_x1 {l : ℕ} (hl : l ∈ geomA1Letters) :
    objElt l • x0 = x0 ∧ objElt l • x1 = x1 := by
  obtain ⟨h0, h1⟩ := (s1OK_spec geomFacts.s1_ok).1 l hl
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · rw [smul_val_of_rep (rep_objElt_of_mem hl) x0, x0_val]
    exact h0
  · rw [smul_val_of_rep (rep_objElt_of_mem hl) x1, x1_val]
    exact h1

theorem A1gen_le_L0 : A1gen ≤ L0 := by
  unfold A1gen CFSG.Perm.lettersGroup
  rw [Subgroup.closure_le]
  rintro g ⟨l, hl, rfl⟩
  obtain ⟨h0, h1⟩ := objElt_smul_x0_x1 hl
  exact mem_L0_iff.2 ⟨by rw [Zp_eq_stabilizer]; exact h0, h1⟩

theorem L0_smul_x0 {a : Q3} (ha : a ∈ L0) : a • x0 = x0 := Zp_smul_x0 (mem_L0_iff.1 ha).1

theorem L0_smul_x1 {a : Q3} (ha : a ∈ L0) : a • x1 = x1 := (mem_L0_iff.1 ha).2

theorem a1TreeFacts :
    CFSG.Perm.TreeFacts 920808 gA1Tree geomA1Letters objElt 99705 :=
  CFSG.Perm.treeOK_facts (n := 920808) (fun _ hl => rep_objElt_of_mem hl)
    (s1OK_spec geomFacts.s1_ok).2.2.1

theorem mem_orbit_A1gen_x2_iff (d : Ω) :
    d ∈ MulAction.orbit A1gen x2 ↔ ∃ k < gA1Tree.pts.size, ap gA1Tree.pts k = d.val :=
  a1TreeFacts.mem_orbit_iff d

theorem exists_mem_A1gen_smul_x2 {d : Ω} (h0 : Δ.Adj x0 d) (h1 : Δ.Adj x1 d) :
    ∃ a ∈ A1gen, a • x2 = d := by
  have hd : d ∈ MulAction.orbit Zp x1 := Δ_adj_x0_iff.1 h0
  have hc' : tauElt⁻¹ • d ∈ MulAction.orbit Zp x1 := by
    rw [← tauElt_smul_x0, Δ_adj_smul_x0_iff] at h1
    exact h1
  obtain ⟨k, hk, hkc⟩ := (mem_orbit_x1_iff _).1 hc'
  have hmemG : memTree gTrees[1]! d.val = true :=
    memTree_of_exists (treeFacts 1).pos_pts ((mem_orbit_x1_iff d).1 hd)
  have htau : ap objTabs[tauReg]! (gTrees[1]!.pts[k]).toNat = d.val := by
    rw [← ap_getElem _ hk, hkc, ← smul_val_of_rep rep_tauElt, smul_inv_smul]
  have h := (s1OK_spec geomFacts.s1_ok).2.2.2 gTrees[1]!.pts[k] (Array.getElem_mem hk)
    (by rw [htau]; exact hmemG)
  rw [htau] at h
  obtain ⟨j, hj, hjd⟩ := memTree_spec h
  obtain ⟨⟨a, ha⟩, hax⟩ := (mem_orbit_A1gen_x2_iff d).2 ⟨j, hj, hjd⟩
  exact ⟨a, ha, hax⟩

theorem commonNeighbors_x0_x1_eq :
    Δ.commonNeighbors x0 x1 = MulAction.orbit A1gen x2 := by
  ext d
  rw [SimpleGraph.mem_commonNeighbors]
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨a, ha, hax⟩ := exists_mem_A1gen_smul_x2 h0 h1
    exact ⟨⟨a, ha⟩, hax⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    have haL := A1gen_le_L0 ha
    constructor
    · have := (Δ_adj_smul a x0 x2).2 Δ_adj_x0_x2
      rwa [L0_smul_x0 haL] at this
    · have := (Δ_adj_smul a x1 x2).2 Δ_adj_x1_x2
      rwa [L0_smul_x1 haL] at this

theorem ncard_commonNeighbors_x0_x1 : (Δ.commonNeighbors x0 x1).ncard = 3510 := by
  rw [commonNeighbors_x0_x1_eq, ← Nat.card_coe_set_eq]
  have h := a1TreeFacts.card_orbit
  rw [(s1OK_spec geomFacts.s1_ok).2.1] at h
  exact h

theorem S1_pairs {c d : Ω} (hc : Δ.Adj x0 c) (hd : Δ.Adj x0 d) (hcd : Δ.Adj c d) :
    ∃ k ∈ Zp, k • x1 = c ∧ k • x2 = d := by
  obtain ⟨⟨k₁, hk₁⟩, hc1⟩ := Δ_adj_x0_iff.1 hc
  have hc1' : k₁ • x1 = c := hc1
  subst hc1'
  have hk₁0 : k₁ • x0 = x0 := Zp_smul_x0 hk₁
  have hd' : Δ.Adj x0 (k₁⁻¹ • d) := by
    have := (Δ_adj_smul k₁⁻¹ x0 d).2 hd
    rwa [inv_smul_eq_iff.2 hk₁0.symm] at this
  have hcd' : Δ.Adj x1 (k₁⁻¹ • d) := by
    have := (Δ_adj_smul k₁⁻¹ (k₁ • x1) d).2 hcd
    rwa [inv_smul_smul] at this
  obtain ⟨a, ha, hax⟩ := exists_mem_A1gen_smul_x2 hd' hcd'
  have haL := A1gen_le_L0 ha
  refine ⟨k₁ * a, Subgroup.mul_mem _ hk₁ (mem_L0_iff.1 haL).1, ?_, ?_⟩
  · rw [mul_smul, L0_smul_x1 haL]
  · rw [mul_smul, hax, smul_inv_smul]

theorem Δ_triangle_transitive {x y z : Ω} (hxy : Δ.Adj x y) (hyz : Δ.Adj y z)
    (hxz : Δ.Adj x z) : ∃ g : Q3, g • x0 = x ∧ g • x1 = y ∧ g • x2 = z := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq Q3 x0 x
  have hx0 : g₀⁻¹ • x = x0 := inv_smul_eq_iff.2 hg₀.symm
  have hy : Δ.Adj x0 (g₀⁻¹ • y) := by
    have := (Δ_adj_smul g₀⁻¹ x y).2 hxy
    rwa [hx0] at this
  have hz : Δ.Adj x0 (g₀⁻¹ • z) := by
    have := (Δ_adj_smul g₀⁻¹ x z).2 hxz
    rwa [hx0] at this
  obtain ⟨k, hk, hk1, hk2⟩ := S1_pairs hy hz ((Δ_adj_smul g₀⁻¹ y z).2 hyz)
  have hk0 : k • x0 = x0 := Zp_smul_x0 hk
  refine ⟨g₀ * k, ?_, ?_, ?_⟩
  · rw [mul_smul, hk0, hg₀]
  · rw [mul_smul, hk1, smul_inv_smul]
  · rw [mul_smul, hk2, smul_inv_smul]

theorem Δ_triangle_in_plane {x y z : Ω} (hxy : Δ.Adj x y) (hyz : Δ.Adj y z) (hxz : Δ.Adj x z) :
    ∃ g : Q3, x ∈ g • plane ∧ y ∈ g • plane ∧ z ∈ g • plane := by
  obtain ⟨g, h0, h1, h2⟩ := Δ_triangle_transitive hxy hyz hxz
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [← h0]
    exact (Finset.smul_mem_smul_finset_iff g).2 x0_mem_plane
  · rw [← h1]
    exact (Finset.smul_mem_smul_finset_iff g).2 x1_mem_plane
  · rw [← h2]
    exact (Finset.smul_mem_smul_finset_iff g).2 x2_mem_plane

end Soundness

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
