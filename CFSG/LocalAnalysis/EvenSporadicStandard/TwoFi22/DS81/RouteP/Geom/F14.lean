module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Ronan
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Amalgam
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Transfer
public import CFSG.Monster.B.GSide.HomotopyLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.S1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open SimpleGraph CFSG.Monster.B.Recog CFSG.Sporadic.SuzRecog.TitsTwo CFSG.Sporadic.Co1Patterson
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

universe v

section Swap


@[expose] noncomputable def s01 : Q3 := Classical.choose exists_swap01

theorem s01_mem_Zq : s01 ∈ Zq := (Classical.choose_spec exists_swap01).1

theorem s01_smul_x0 : s01 • x0 = x1 := (Classical.choose_spec exists_swap01).2.1

theorem s01_smul_x1 : s01 • x1 = x0 := (Classical.choose_spec exists_swap01).2.2

theorem exists_mem_Zq_smul_x0 {p : Ω} (hp : p ∈ plane) : ∃ g ∈ Zq, g • x0 = p := by
  obtain ⟨r, hr, hrp, -⟩ := exists_mem_plane_ne_two p p
  obtain ⟨g, hg, h0, -⟩ := Zq_twoTransitive x0_mem_plane x1_mem_plane hp hr x0_ne_x1 hrp.symm
  exact ⟨g, hg, h0⟩

end Swap

section Incidence


theorem inc_iff (x : Q3 ⧸ Zp) (g : Q3) :
    (∃ z : Q3, x = (z : Q3 ⧸ Zp) ∧ (g : Q3 ⧸ Zq) = (z : Q3 ⧸ Zq)) ↔
      omegaEquiv x ∈ g • plane := by
  constructor
  · rintro ⟨z, rfl, hz⟩
    rw [QuotientGroup.eq] at hz
    rw [omegaEquiv_mk]
    have e : z • x0 = g • ((g⁻¹ * z) • x0) := by rw [← mul_smul, mul_inv_cancel_left]
    rw [e]
    exact (Finset.smul_mem_smul_finset_iff g).2 (Zq_preserves_plane hz x0_mem_plane)
  · intro h
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
    rw [omegaEquiv_mk, ← Finset.inv_smul_mem_iff] at h
    obtain ⟨k, hk, hkz⟩ := exists_mem_Zq_smul_x0 h
    refine ⟨g * k, omegaEquiv.injective ?_, QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])⟩
    rw [omegaEquiv_mk, omegaEquiv_mk, mul_smul, hkz, smul_inv_smul]

end Incidence

section Tits


theorem triangulable_cosetGraph_s01 : Triangulable (cosetGraph Zp s01) :=
  (CFSG.Monster.B.GSide.triangulable_iff_of_iso (cosetGraphIso s01_smul_x0 s01_smul_x1)).2
    Δ_triangulable

theorem triangulableBy_s01 :
    TriangulableBy (cosetGraph₂ Zp Zq s01) (amalgamTriangles Zp Zq s01) := by
  refine triangulableBy_of_points
    (inc := fun x π => ∃ z : Q3, x = (z : Q3 ⧸ Zp) ∧ π = (z : Q3 ⧸ Zq))
    (fun _ _ => cosetGraph₂_adj_inl_inl) (fun _ _ => cosetGraph₂_adj_inl_inr)
    (fun _ _ => cosetGraph₂_not_adj_inr_inr) ?_ ?_ ?_ triangulable_cosetGraph_s01
  · intro x y π hxy hx hy
    exact (amalgamTriangles_iff _).2 ⟨x, y, π, hxy, hx, hy, rfl⟩
  · intro π x y hx hy hne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective π
    exact (cosetGraph_adj_iff_Δ s01_smul_x0 s01_smul_x1 x y).2
      (Δ_smul_plane_isClique g ((inc_iff x g).1 hx) ((inc_iff y g).1 hy)
        fun h => hne (omegaEquiv.injective h))
  · intro x y z hxy hyz hxz
    obtain ⟨g, hx, hy, hz⟩ := Δ_triangle_in_plane
      ((cosetGraph_adj_iff_Δ s01_smul_x0 s01_smul_x1 x y).1 hxy)
      ((cosetGraph_adj_iff_Δ s01_smul_x0 s01_smul_x1 y z).1 hyz)
      ((cosetGraph_adj_iff_Δ s01_smul_x0 s01_smul_x1 x z).1 hxz)
    exact ⟨(g : Q3 ⧸ Zq), (inc_iff x g).2 hx, (inc_iff y g).2 hy, (inc_iff z g).2 hz⟩

theorem preconnected_cosetGraph₂_s01 : (cosetGraph₂ Zp Zq s01).Preconnected :=
  cosetGraph₂_preconnected_of_points
    ((cosetGraphIso s01_smul_x0 s01_smul_x1).preconnected_iff.2 Δ_connected.preconnected)

theorem titsInput_s01 : TitsInput Zp Zq Ze s01 := by
  refine TitsInput.of_action Zp_eq_stabilizer ?_ ?_ s01_mem_Zq (fun g => ?_) ?_
    preconnected_cosetGraph₂_s01 triangulableBy_s01
  · rw [s01_smul_x0]
    exact x0_ne_x1.symm
  · rw [s01_smul_x0, s01_smul_x1]
  · rw [s01_smul_x0]
    exact mem_Ze_iff
  · intro w hw hwx
    obtain ⟨l, hl, hl0, hl1⟩ := Zq_twoTransitive (p := x0) (q := x1) (p' := x0) (q' := w • x0)
      x0_mem_plane x1_mem_plane x0_mem_plane (Zq_preserves_plane hw x0_mem_plane) x0_ne_x1
      (Ne.symm hwx)
    exact ⟨l, hl, hl0, by rw [s01_smul_x0]; exact hl1⟩

theorem f14 : AmalgamUniversal.{0, v} Zp Zq Ze s01 := amalgamUniversal_of_tits titsInput_s01

end Tits

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
