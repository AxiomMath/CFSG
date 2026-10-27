module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Stage1Ronan
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Amalgam
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Monster.B.Recog CFSG.Sporadic.SuzRecog.TitsTwo CFSG.Sporadic.Co1Patterson
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

universe v

section Planes

theorem Γ0_triangle_in_plane {u v w : Ω} (hu : Δ.Adj x0 u) (hv : Δ.Adj x0 v) (hw : Δ.Adj x0 w)
    (huv : Δ.Adj u v) (hvw : Δ.Adj v w) (huw : Δ.Adj u w) :
    ∃ g ∈ Zp, u ∈ g • plane ∧ v ∈ g • plane ∧ w ∈ g • plane := by
  obtain ⟨k, hk, hk1, hk2⟩ := S1_pairs hu hv huv
  have hkinv0 : k⁻¹ • x0 = x0 := Zp_smul_x0 (Zp.inv_mem hk)
  have hw0 : Δ.Adj x0 (k⁻¹ • w) := by
    have := (Δ_adj_smul k⁻¹ x0 w).2 hw
    rwa [hkinv0] at this
  have hw1 : Δ.Adj x1 (k⁻¹ • w) := by
    have := (Δ_adj_smul k⁻¹ u w).2 huw
    rwa [← hk1, inv_smul_smul] at this
  have hw2 : Δ.Adj x2 (k⁻¹ • w) := by
    have := (Δ_adj_smul k⁻¹ v w).2 hvw
    rwa [← hk2, inv_smul_smul] at this
  obtain ⟨h, hh, hfix, hpl⟩ := stage1_stab_transitive hw0 hw1 hw2
  have hhL := A1gen_le_L0 hh
  have hhZ : h ∈ Zp := (mem_L0_iff.1 hhL).1
  have hh1 : h • x1 = x1 := (mem_L0_iff.1 hhL).2
  refine ⟨k * h, Zp.mul_mem hk hhZ, ?_, ?_, ?_⟩
  · have : (k * h) • x1 = u := by rw [mul_smul, hh1, hk1]
    rw [← this]
    exact (Finset.smul_mem_smul_finset_iff (k * h)).2 x1_mem_plane
  · have : (k * h) • x2 = v := by rw [mul_smul, hfix, hk2]
    rw [← this]
    exact (Finset.smul_mem_smul_finset_iff (k * h)).2 x2_mem_plane
  · have : (k * h) • planePt 3 = w := by rw [mul_smul, hpl, smul_inv_smul]
    rw [← this]
    exact (Finset.smul_mem_smul_finset_iff (k * h)).2 (planePt_mem 3)

theorem Γ23_triangle_in_plane {a b c : Zp ⧸ XpZ} (hab : Γ23.Adj a b) (hbc : Γ23.Adj b c)
    (hac : Γ23.Adj a c) :
    ∃ g ∈ Zp, pt a ∈ g • plane ∧ pt b ∈ g • plane ∧ pt c ∈ g • plane :=
  Γ0_triangle_in_plane (Δ_adj_x0_pt a) (Δ_adj_x0_pt b) (Δ_adj_x0_pt c) ((Γ23_adj_iff a b).1 hab)
    ((Γ23_adj_iff b c).1 hbc) ((Γ23_adj_iff a c).1 hac)

end Planes

section Tits

theorem exists_mem_XqZ_smul_x1 {p : Ω} (hp : p ∈ plane) (hp0 : p ≠ x0) :
    ∃ q ∈ XqZ, (q : Q3) • x1 = p := by
  obtain ⟨g, hg, h0, h1⟩ :=
    Zq_twoTransitive x0_mem_plane x1_mem_plane x0_mem_plane hp x0_ne_x1 hp0.symm
  have hgZ : g ∈ Zp := by
    rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
    exact h0
  exact ⟨⟨g, hgZ⟩, mem_XqZ_iff.2 hg, h1⟩

theorem XqZ_two_transitive :
    ∀ w ∈ XqZ, w • x1 ≠ x1 → ∃ l ∈ XqZ, l • x1 = x1 ∧ l • s2Z • x1 = w • x1 := by
  intro w hw hwx
  have hwq : (w : Q3) ∈ Zq := mem_XqZ_iff.1 hw
  have hp : (w : Q3) • x1 ∈ plane := Zq_preserves_plane hwq x1_mem_plane
  have hw0 : (w : Q3) • x0 = x0 := Zp_smul_x0 w.2
  have hp0 : (w : Q3) • x1 ≠ x0 := by
    intro h
    exact x0_ne_x1 (smul_left_cancel (w : Q3) (h.trans hw0.symm)).symm
  obtain ⟨g, hg, h0, h1, h2⟩ := Zq_threeTransitive x0_mem_plane x1_mem_plane x2_mem_plane
    x0_mem_plane x1_mem_plane hp x0_ne_x1 x0_ne_x2 x1_ne_x2 x0_ne_x1 hp0.symm hwx.symm
  have hgZ : g ∈ Zp := by
    rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
    exact h0
  refine ⟨⟨g, hgZ⟩, mem_XqZ_iff.2 hg, h1, ?_⟩
  show g • (s2Z : Q3) • x1 = (w : Q3) • x1
  rw [s2Z_smul_x1]
  exact h2

theorem XeZ_mem_iff : ∀ g : Zp, g ∈ XeZ ↔ (g • x1 = x1 ∧ g • s2Z • x1 = s2Z • x1) ∨
    (g • x1 = s2Z • x1 ∧ g • s2Z • x1 = x1) := by
  intro g
  have e1 : s2Z • x1 = x2 := s2Z_smul_x1
  rw [e1]
  exact mem_XeZ_iff

theorem pt_mem_smul_plane_of_inc {x y : Zp ⧸ XpZ} {π : Zp ⧸ XqZ}
    (hx : ∃ z : Zp, x = (z : Zp ⧸ XpZ) ∧ π = (z : Zp ⧸ XqZ))
    (hy : ∃ z : Zp, y = (z : Zp ⧸ XpZ) ∧ π = (z : Zp ⧸ XqZ)) :
    ∃ z : Zp, pt x ∈ (z : Q3) • plane ∧ pt y ∈ (z : Q3) • plane := by
  obtain ⟨z₁, rfl, hπ₁⟩ := hx
  obtain ⟨z₂, rfl, hπ₂⟩ := hy
  have hq : z₁⁻¹ * z₂ ∈ XqZ := by
    have := hπ₁.symm.trans hπ₂
    rwa [QuotientGroup.eq] at this
  refine ⟨z₁, ?_, ?_⟩
  · rw [pt_mk]
    exact (Finset.smul_mem_smul_finset_iff (z₁ : Q3)).2 x1_mem_plane
  · have h1 : pt (z₂ : Zp ⧸ XpZ) = (z₁ : Q3) • (((z₁⁻¹ * z₂ : Zp)) : Q3) • x1 := by
      rw [pt_mk, ← mul_smul, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [h1]
    exact (Finset.smul_mem_smul_finset_iff (z₁ : Q3)).2 (Zq_preserves_plane (mem_XqZ_iff.1 hq)
      x1_mem_plane)

theorem inc_of_mem_smul_plane (g : Zp) {v : Zp ⧸ XpZ} (hv : pt v ∈ (g : Q3) • plane) :
    ∃ z : Zp, v = (z : Zp ⧸ XpZ) ∧ (g : Zp ⧸ XqZ) = (z : Zp ⧸ XqZ) := by
  have hinv : (g : Q3)⁻¹ • pt v ∈ plane := by
    rwa [← Finset.inv_smul_mem_iff] at hv
  have hne : (g : Q3)⁻¹ • pt v ≠ x0 := by
    intro h
    rw [inv_smul_eq_iff] at h
    exact (Δ_adj_x0_pt v).ne (Zp_smul_x0 g.2 ▸ h).symm
  obtain ⟨q, hq, hqx⟩ := exists_mem_XqZ_smul_x1 hinv hne
  refine ⟨g * q, pt_injective ?_, ?_⟩
  · rw [pt_mk, Subgroup.coe_mul, mul_smul, hqx, smul_inv_smul]
  · rw [QuotientGroup.eq]
    simpa using hq

theorem triangulableBy_cosetGraph₂ :
    TriangulableBy (cosetGraph₂ XpZ XqZ s2Z) (amalgamTriangles XpZ XqZ s2Z) := by
  refine triangulableBy_of_points (Δ := cosetGraph XpZ s2Z)
    (inc := fun x π => ∃ z : Zp, x = (z : Zp ⧸ XpZ) ∧ π = (z : Zp ⧸ XqZ))
    (fun _ _ => cosetGraph₂_adj_inl_inl) (fun _ _ => cosetGraph₂_adj_inl_inr)
    (fun _ _ => cosetGraph₂_not_adj_inr_inr) ?_ ?_ ?_ Γ23_triangulable
  · intro x y π hxy hx hy
    exact (amalgamTriangles_iff _).2 ⟨x, y, π, hxy, hx, hy, rfl⟩
  · intro π x y hx hy hxy
    obtain ⟨z, hxz, hyz⟩ := pt_mem_smul_plane_of_inc hx hy
    have hne : pt x ≠ pt y := fun h => hxy (pt_injective h)
    exact (Γ23_adj_iff x y).2 (Δ_smul_plane_isClique (z : Q3) hxz hyz hne)
  · intro x y z hxy hyz hxz
    obtain ⟨g, hg, hgx, hgy, hgz⟩ := Γ23_triangle_in_plane hxy hyz hxz
    exact ⟨((⟨g, hg⟩ : Zp) : Zp ⧸ XqZ), inc_of_mem_smul_plane ⟨g, hg⟩ hgx,
      inc_of_mem_smul_plane ⟨g, hg⟩ hgy, inc_of_mem_smul_plane ⟨g, hg⟩ hgz⟩

theorem titsInput : TitsInput XpZ XqZ XeZ s2Z :=
  TitsInput.of_action (Ω := Ω) (x₀ := x1) XpZ_eq_stabilizer
    (by
      have e1 : s2Z • x1 = x2 := s2Z_smul_x1
      rw [e1]
      exact x1_ne_x2.symm)
    (by
      have e1 : s2Z • x1 = x2 := s2Z_smul_x1
      have e2 : s2Z • x2 = x1 := s2Z_smul_x2
      rw [e1, e2])
    s2Z_mem_XqZ XeZ_mem_iff XqZ_two_transitive
    (cosetGraph₂_preconnected_of_points Γ23_connected.preconnected) triangulableBy_cosetGraph₂

theorem f13 : AmalgamUniversal.{0, v} (L0.subgroupOf Zp) ((Zp ⊓ Zq).subgroupOf Zp)
    (Y0.subgroupOf Zp) ⟨s2, s2_mem_Zp⟩ :=
  amalgamUniversal_of_tits titsInput

end Tits

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
