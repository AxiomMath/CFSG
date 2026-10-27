module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneTree
public import CFSG.Monster.B.Recog.GenericTits

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open SimpleGraph CFSG.Monster.B.Recog
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Graph


@[expose] def OrbRel (y z : Ω) : Prop := ∃ g : Q3, g • x0 = y ∧ g • x1 = z

@[expose] def Δ : SimpleGraph Ω := SimpleGraph.fromRel OrbRel

theorem Δ_adj_iff_orbRel {y z : Ω} : Δ.Adj y z ↔ y ≠ z ∧ (OrbRel y z ∨ OrbRel z y) :=
  SimpleGraph.fromRel_adj _ _ _

theorem OrbRel.ne {y z : Ω} (h : OrbRel y z) : y ≠ z := by
  obtain ⟨g, rfl, rfl⟩ := h
  intro e
  exact x0_ne_x1 (smul_left_cancel g e)

theorem orbRel_smul (g : Q3) {y z : Ω} : OrbRel (g • y) (g • z) ↔ OrbRel y z := by
  constructor
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨g⁻¹ * k, ?_, ?_⟩
    · rw [mul_smul, hk0, inv_smul_smul]
    · rw [mul_smul, hk1, inv_smul_smul]
  · rintro ⟨k, hk0, hk1⟩
    exact ⟨g * k, by rw [mul_smul, hk0], by rw [mul_smul, hk1]⟩

theorem Zp_smul_x0 {k : Q3} (hk : k ∈ Zp) : k • x0 = x0 := by
  rwa [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff] at hk

section Swap


theorem orbRel_symm {y z : Ω} (h : OrbRel y z) : OrbRel z y := by
  obtain ⟨g, rfl, rfl⟩ := h
  obtain ⟨s, -, hs0, hs1⟩ := exists_swap01
  exact ⟨g * s, by rw [mul_smul, hs0], by rw [mul_smul, hs1]⟩

theorem Δ_adj_iff {y z : Ω} : Δ.Adj y z ↔ OrbRel y z := by
  rw [Δ_adj_iff_orbRel]
  exact ⟨fun h => h.2.elim id orbRel_symm, fun h => ⟨h.ne, Or.inl h⟩⟩

theorem Δ_adj_smul (g : Q3) (y z : Ω) : Δ.Adj (g • y) (g • z) ↔ Δ.Adj y z := by
  rw [Δ_adj_iff, Δ_adj_iff, orbRel_smul]

theorem Δ_adj_comm (y z : Ω) : Δ.Adj y z ↔ Δ.Adj z y := Δ.adj_comm y z

theorem Δ_adj_x0_iff {z : Ω} :
    Δ.Adj x0 z ↔ z ∈ MulAction.orbit Zp x1 := by
  rw [Δ_adj_iff]
  constructor
  · rintro ⟨g, hg0, hg1⟩
    have hgZ : g ∈ Zp := by
      rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
      exact hg0
    exact ⟨⟨g, hgZ⟩, hg1⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, Zp_smul_x0 hk, rfl⟩

theorem Δ_adj_smul_x0_iff (t : Q3) {z : Ω} :
    Δ.Adj (t • x0) z ↔ t⁻¹ • z ∈ MulAction.orbit Zp x1 := by
  rw [← Δ_adj_x0_iff, ← Δ_adj_smul t⁻¹ (t • x0) z, inv_smul_smul]

end Swap

end Graph

section Plane


theorem Δ_plane_clique {p q : Ω} (hp : p ∈ plane) (hq : q ∈ plane) (hpq : p ≠ q) :
    Δ.Adj p q := by
  obtain ⟨g, -, h0, h1⟩ := Zq_twoTransitive x0_mem_plane x1_mem_plane hp hq x0_ne_x1 hpq
  exact Δ_adj_iff.2 ⟨g, h0, h1⟩

theorem Δ_plane_isClique : Δ.IsClique (plane : Set Ω) := fun _ hp _ hq hpq =>
  Δ_plane_clique hp hq hpq

theorem Δ_plane_isNClique : Δ.IsNClique 24 plane := ⟨Δ_plane_isClique, card_plane⟩

theorem Δ_smul_plane_isClique (g : Q3) : Δ.IsClique ((g • plane : Finset Ω) : Set Ω) := by
  intro p hp q hq hpq
  rw [Finset.mem_coe, ← Finset.inv_smul_mem_iff] at hp hq
  exact (Δ_adj_smul g⁻¹ p q).1 (Δ_plane_clique hp hq fun h => hpq (smul_left_cancel _ h))

theorem Δ_adj_x0_x1 : Δ.Adj x0 x1 := Δ_plane_clique x0_mem_plane x1_mem_plane x0_ne_x1

theorem Δ_adj_x0_x2 : Δ.Adj x0 x2 := Δ_plane_clique x0_mem_plane x2_mem_plane x0_ne_x2

theorem Δ_adj_x1_x2 : Δ.Adj x1 x2 := Δ_plane_clique x1_mem_plane x2_mem_plane x1_ne_x2

end Plane

section CosetGraph


theorem not_mem_Zp_of_swap {s : Q3} (hs0 : s • x0 = x1) : s ∉ Zp := by
  intro h
  rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff] at h
  exact x0_ne_x1 (h.symm.trans hs0)

theorem mul_self_mem_Zp_of_swap {s : Q3} (hs0 : s • x0 = x1) (hs1 : s • x1 = x0) :
    s * s ∈ Zp := by
  rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff, mul_smul, hs0, hs1]

theorem cosetGraph_adj_iff_Δ {s : Q3} (hs0 : s • x0 = x1) (hs1 : s • x1 = x0)
    (a b : Q3 ⧸ Zp) :
    (cosetGraph Zp s).Adj a b ↔ Δ.Adj (omegaEquiv a) (omegaEquiv b) := by
  induction a using QuotientGroup.induction_on with
  | H z =>
    induction b using QuotientGroup.induction_on with
    | H u =>
      have key : ∀ a : Q3, (z * a * s) • x0 = z • a • x1 := fun a => by
        rw [mul_smul, mul_smul, hs0]
      rw [cosetGraph_adj_mk_iff (not_mem_Zp_of_swap hs0) (mul_self_mem_Zp_of_swap hs0 hs1),
        omegaEquiv_mk, omegaEquiv_mk, Δ_adj_smul_x0_iff]
      constructor
      · rintro ⟨a, ha, h⟩
        rw [QuotientGroup.eq] at h
        have h' : u⁻¹ * (z * a * s) ∈ Zp := h
        rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff,
          key] at h'
        exact ⟨⟨a, ha⟩, show a • x1 = z⁻¹ • u • x0 by rw [← h', inv_smul_smul]⟩
      · rintro ⟨⟨a, ha⟩, h⟩
        refine ⟨a, ha, ?_⟩
        rw [QuotientGroup.eq]
        show u⁻¹ * (z * a * s) ∈ Zp
        have h' : a • x1 = z⁻¹ • u • x0 := h
        rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff, mul_smul, key, h', smul_inv_smul,
          inv_smul_smul]

@[expose] noncomputable def cosetGraphIso {s : Q3} (hs0 : s • x0 = x1) (hs1 : s • x1 = x0) :
    cosetGraph Zp s ≃g Δ where
  toEquiv := omegaEquiv
  map_rel_iff' := (cosetGraph_adj_iff_Δ hs0 hs1 _ _).symm

end CosetGraph

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
