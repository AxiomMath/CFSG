module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Hyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Free
public import CFSG.ClassicalInvolution.Asc77.WP3S28BIndep

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Input


@[expose] def TriangleHyp51R (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W → ¬ TwinPerp.WCentralNontrivial W →
          oddCoreIn (tightCore R) ≠ ⊥ →
          ∀ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R →
            ∀ D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t,
              Hyp51At (cube D) (vertex D)

end Input

section Main


variable {r n : ℕ}

theorem alphaOddR_of_triangleHyp51R (hT : TriangleHyp51R r n) : AlphaOddR r n := by
  intro hr Y _ _ R S t h h2 W hW htW hS4 hnc g hg hgt
  classical
  by_cases hK : oddCoreIn (tightCore R) = ⊥
  · exact alphaOf_odd_of_oddCore_bot hr h h2 hW htW hS4 hnc hK hg
  obtain ⟨K', hK', hne, ⟨D⟩⟩ := Perp23.Two.exists_twoFrame h h2 hW htW hS4
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have cx : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.ctxOf h.partIHypG hW
  have hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hju := frame_ju h hW hnc D
  have hm : Even D.m := twoFrame_m_even hr h hW D
  have hB : Hyp51 (cube D) :=
    hyp51_cube D hc hm hju (hyp51At_cube_t hr h h2 hW hnc hK' hne D)
      (hT hr Y R S t h h2 W hW htW hS4 hnc hK K' hK' hne D)
  have hEN : g ∈ Subgroup.normalizer (Subgroup.closure ({t, D.F.j} : Set Y) : Set Y) :=
    D.mgrp_le_normalizer hΩ hW cx hg
  have htB : t ∈ cube D := Subgroup.subset_closure (by simp)
  have hjB : D.F.j ∈ cube D := Subgroup.subset_closure (by simp)
  have htE : t ∈ Subgroup.closure ({t, D.F.j} : Set Y) := Subgroup.subset_closure (by simp)
  have hvE : g * t * g⁻¹ ∈ Subgroup.closure ({t, D.F.j} : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp hEN t).mp htE
  have hEB : Subgroup.closure ({t, D.F.j} : Set Y) ≤ cube D := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]; exact htB
    · rw [Set.mem_singleton_iff.mp hx]; exact hjB
  have hE'B : Subgroup.closure ({t, g * t * g⁻¹} : Set Y) ≤ cube D := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]; exact htB
    · rw [Set.mem_singleton_iff.mp hx]; exact hEB hvE
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := Thompson.MGrp_le_normalizer _ W hg
  have hvW : g * t * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgN t).mp htW
  have hv2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hv1 : g * t * g⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h1]; group
  have htv : t * (g * t * g⁻¹) = (g * t * g⁻¹) * t := hc t htW _ hvW
  have hcard : Nat.card ↥(Subgroup.closure ({t, g * t * g⁻¹} : Set Y)) = 4 :=
    S28B.card_closure_pair_eq_four hz2 hv2 htv hz1 hv1 hgt
  exact (lemma54_odd_and_eq hB hE'B ⟨by rw [hcard]; norm_num,
    closure_pair_sq hz2 hv2 htv⟩).1

theorem twinPerp24R_of_triangleHyp51R (hr : 4 ≤ r) (hE : TwinThmER r n) (h233 : TwinPerp233R r n)
    (hT : TriangleHyp51R r n) : TwinPerp24R r n :=
  twinPerp24R_of_alphaOdd hr hE h233 (alphaOddR_of_triangleHyp51R hT)

theorem hyp51At_vertex_of_inO2 (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hP : PerpHypR r n Y R S t) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {K' : Subgroup Y}
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) {a : Y}
    (ha : a ∈ Subgroup.centralizer ({vertex D} : Set Y))
    (haE : a ∈ Subgroup.closure ({t, D.F.j} : Set Y)) (ha1 : a ≠ 1)
    (hT : TightInO2 (oddQuotMk (vertex D) ⟨a, ha⟩)) : Hyp51At (cube D) (vertex D) := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hP.core.hyp
  have hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hju := frame_ju hP hW hnc D
  have hm : Even D.m := twoFrame_m_even hr hP hW D
  obtain ⟨hv1, hvt, hvj, hvtj⟩ := vertex_ne D hc hm hju
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have htj : t * D.F.j = D.F.j * t := hc t D.t_mem_W D.F.j D.j_mem_W
  have hav : a ≠ vertex D := by
    intro h1
    rcases closure_pair_cases hz2 D.j_sq htj a haE with h3 | h3 | h3 | h3
    · exact ha1 h3
    · exact hvt (h1 ▸ h3)
    · exact hvj (h1 ▸ h3)
    · exact hvtj (h1 ▸ h3)
  have htB : t ∈ cube D := Subgroup.subset_closure (by simp)
  have hjB : D.F.j ∈ cube D := Subgroup.subset_closure (by simp)
  have hvB : vertex D ∈ cube D := Subgroup.subset_closure (by simp)
  have haB : a ∈ cube D := by
    have hle : Subgroup.closure ({t, D.F.j} : Set Y) ≤ cube D := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx]; exact htB
      · rw [Set.mem_singleton_iff.mp hx]; exact hjB
    exact hle haE
  exact hyp51At_of_commute (isElemAbelian_cube D hc hm hju) hvB hv1 haB ha1 hav ha
    fun L hL => commute_of_tightInO2 hT hL

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
