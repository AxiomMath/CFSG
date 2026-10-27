module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4VtxAlg
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFusion
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Vertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame
public import CFSG.ClassicalInvolution.SmallCases.A7T22ZStar
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
open scoped commutatorElement

structure VtxFacts {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (t : Y) (K' : Subgroup Y) (c : Y) :
    Prop where
  sq : c * c = 1
  ne : c ≠ 1
  comm_t : t * c = c * t
  tq' : c ∈ Bootstrap.trivialOnQuot K'
  ntq : c ∉ Bootstrap.trivialOnQuot (tightCore R)
  twin_le : tightCore R ≤ Bootstrap.trivialOnQuot K'
  twin_fix : ∀ g : Y, g * t = t * g → g * c = c * g → conjSub g (tightCore R) = tightCore R

section Vtx


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem vtxFacts (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (hnc : ¬ TwinPerp.WCentralNontrivial W)
    {K' : Subgroup Y} (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R)
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) :
    VtxFacts R t K' (vertex D) := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hju := frame_ju h hW hnc D
  have hm : Even D.m := twoFrame_m_even hr h hW D
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hv1 : vertex D ≠ 1 := (vertex_ne D hc hm hju).1
  have hv2 : vertex D * vertex D = 1 := vertex_sq_eq D hc hm hju
  have hvW : vertex D ∈ W := vertex_mem_W D hc hm
  have htv : t * vertex D = vertex D * t := hc t D.t_mem_W (vertex D) hvW
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hK'.1
  have hcls : CoreAssembly.conjClass K' = CoreAssembly.conjClass (tightCore R) :=
    TwinVtx.conjClass_eq_of_mem hK'.1
  have hx₂K' : D.x₂ ∈ K' := by
    have := D.F.ρ'.hRK.1 D.x₂_mem_R
    rwa [D.hρ'K] at this
  have hρ'syl : IsSylow2In D.F.ρ'.R K' := by
    have := D.F.ρ'.hRK
    rwa [D.hρ'K] at this
  have hq' : IsPGroup 2 (↥K' ⧸ classicalInvolutionOddCore ↥K') :=
    Perp23.isPGroup_quot_of_member h hK'.1
  have hrc : D.F.ρ'.r * vertex D = vertex D * D.F.ρ'.r := by
    have e := vertex_r'_eq D hc hm
    calc D.F.ρ'.r * vertex D = (D.F.ρ'.r * vertex D * D.F.ρ'.r⁻¹) * D.F.ρ'.r := by group
      _ = vertex D * D.F.ρ'.r := by rw [e]
  have hiR' : (D.F.ρ'.R ⊓ W).relIndex D.F.ρ'.R = 2 := by
    have hcard := Q3CL.Thompson.D_card hΩ hW D.F.ρ'.hR
    have hrel := Subgroup.relIndex_mul_card (H := D.F.ρ'.R ⊓ W) (K := D.F.ρ'.R)
    rw [inf_eq_left.mpr (inf_le_left : D.F.ρ'.R ⊓ W ≤ D.F.ρ'.R)] at hrel
    have hpos : 0 < Nat.card ↥(D.F.ρ'.R ⊓ W) := Nat.card_pos
    have h3 : (D.F.ρ'.R ⊓ W).relIndex D.F.ρ'.R * Nat.card ↥(D.F.ρ'.R ⊓ W) =
        2 * Nat.card ↥(D.F.ρ'.R ⊓ W) := by
      rw [hrel, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hcR' : ∀ x ∈ D.F.ρ'.R, vertex D * x = x * vertex D := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact hc _ hvW _ hxW
    · have hw : D.F.ρ'.r⁻¹ * x ∈ W :=
        (inv_mul_mem_of_relIndex_two' hiR' D.F.ρ'.hr hx
          (fun hh => D.F.ρ'.hrW hh.2) (fun hh => hxW hh.2)).2
      obtain ⟨w, hwW, rfl⟩ : ∃ w ∈ W, x = D.F.ρ'.r * w := ⟨D.F.ρ'.r⁻¹ * x, hw, by group⟩
      calc vertex D * (D.F.ρ'.r * w) = (vertex D * D.F.ρ'.r) * w := by group
        _ = (D.F.ρ'.r * vertex D) * w := by rw [hrc]
        _ = D.F.ρ'.r * (vertex D * w) := by group
        _ = D.F.ρ'.r * (w * vertex D) := by rw [hc _ hvW _ hwW]
        _ = D.F.ρ'.r * w * vertex D := by group
  have hx₂conj : D.x₂ ∈ conjSub (vertex D) K' := by
    have h1 : vertex D * D.x₂ * (vertex D)⁻¹ ∈ conjSub (vertex D) K' := conj_mem_conjSub hx₂K'
    have h2' : vertex D * D.x₂ * (vertex D)⁻¹ = D.x₂ := by
      rw [hc _ hvW _ D.x₂_mem_W]
      group
    rwa [h2'] at h1
  have hconjCls : conjSub (vertex D) K' ∈ CoreAssembly.conjClass (tightCore R) := by
    have h1 : conjSub (vertex D) K' ∈ CoreAssembly.conjClass K' := ⟨vertex D, rfl⟩
    rw [hcls] at h1
    exact h1
  have hconj : conjSub (vertex D) K' = K' :=
    eq_of_mem_inf_of_four_dvd hΩ hconjCls hK'.1 hx₂conj hx₂K'
      (by rw [D.o₂]; exact dvd_mul_right 4 D.m)
  have hnorm : vertex D ∈ Subgroup.normalizer (K' : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr hconj
  have hcK' : vertex D ∈ Bootstrap.trivialOnQuot K' :=
    mem_trivialOnQuot_of_centralizes hq' hρ'syl hnorm hcR'
  have hnotK : vertex D ∉ Bootstrap.trivialOnQuot (tightCore R) := by
    intro hc0
    have hcinv : (vertex D)⁻¹ = vertex D := inv_eq_of_mul_eq_one_right hv2
    have e : ⁅vertex D, D.F.ρ.r⁆ = t := by
      rw [commutatorElement_def, hcinv]
      calc vertex D * D.F.ρ.r * vertex D * D.F.ρ.r⁻¹
          = vertex D * (D.F.ρ.r * vertex D * D.F.ρ.r⁻¹) := by group
        _ = vertex D * (vertex D * t) := by rw [vertex_r_eq D hc hm]
        _ = (vertex D * vertex D) * t := by group
        _ = t := by rw [hv2, one_mul]
    have hmem := hc0.2 D.F.ρ.r D.r_mem_K
    rw [e] at hmem
    exact not_mem_oddCoreIn_of_orderOf_two ht2 hmem
  have hKΩ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := CoreAssembly.mem_conjClass_self _
  have htwin_le : tightCore R ≤ Bootstrap.trivialOnQuot K' :=
    A7T22.le_trivialOnQuot_of_twin hΩ hKΩ hK'Ω hne.symm hz D.hzK'
  refine ⟨hv2, hv1, htv, hcK', hnotK, htwin_le, ?_⟩
  intro g hgt hgc
  have hgt' : g * t * g⁻¹ = t := by rw [hgt]; group
  have hKtw : conjSub g (tightCore R) ∈
      twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    ⟨⟨g, rfl⟩, t, hz, by have := hz.conj g; rwa [hgt'] at this⟩
  rw [TwinPerp.twinSet_eq_pair h2 hK' hne] at hKtw
  rcases hKtw with hK | hKeq
  · exact hK
  · exfalso
    have h1 : vertex D ∈ Bootstrap.trivialOnQuot (conjSub g (tightCore R)) := by
      rw [hKeq]; exact hcK'
    have h3 := Bootstrap.trivialOnQuot_conjSub h1 g⁻¹
    rw [conjSub_inv_conjSub] at h3
    have h4 : g⁻¹ * vertex D * g⁻¹⁻¹ = vertex D := by
      calc g⁻¹ * vertex D * g⁻¹⁻¹ = g⁻¹ * (vertex D * g) := by group
        _ = g⁻¹ * (g * vertex D) := by rw [hgc]
        _ = vertex D := by group
    rw [h4] at h3
    exact hnotK h3

end Vtx

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
