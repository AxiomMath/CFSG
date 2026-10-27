module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Triangle
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestLayer
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24LayerTq
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Count

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


@[expose] def VertexEdgelessExclR (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W → ¬ TwinPerp.WCentralNontrivial W →
          ∀ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R →
            ∀ D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t,
              ∀ (htC : t ∈ Subgroup.centralizer ({vertex D} : Set Y))
                (ht' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) ∈ secH K' (vertex D))
                (S₀ : Sylow 2 ↥(tightCore (secR K' (vertex D)))),
                TightDatum (tightCore (secR K' (vertex D))) S₀
                    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D))) ⟨⟨t, htC⟩, ht'⟩) →
                  TightClsR r (SecQ K' (vertex D)) (tightCore (secR K' (vertex D))) S₀
                    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D))) ⟨⟨t, htC⟩, ht'⟩) →
                    ¬ TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D)))
                      ⟨⟨t, htC⟩, ht'⟩) →
                      ¬ TightEdgeless (tightCore (secR K' (vertex D)))

end Input

section Main


variable {r n : ℕ}

theorem triangleHyp51R_of_vertexEdgeless (hNo : NoQ16E4) (hV : VertexEdgelessExclR r n) :
    TriangleHyp51R r n := by
  intro hr Y _ _ R S t h h2 W hW htW hS4 hnc _hK K' hK' hne D
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
  have htC : t ∈ Subgroup.centralizer ({vertex D} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htv
  have hstd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hstd₀⟩ := hstd.core
  have hRc₀ : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc₀]
    exact hK'.1
  obtain ⟨S₃, hstd₃⟩ := exists_datum_atR hstd₀ hRc₀ hK'Ω D.hzK'
  have hRc₃ : tightCore K' = K' := TwinVtx.tightCore_eq_of_mem hRc₀ hK'Ω
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
    · have hw : D.F.ρ'.r⁻¹ * x ∈ W := by
        have hmem := inv_mul_mem_of_relIndex_two hiR' D.F.ρ'.hr hx
          (fun hh => D.F.ρ'.hrW hh.2) (fun hh => hxW hh.2)
        exact hmem.2
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
  have hcK' : vertex D ∈ CFSG.ClassicalInvolution.Balance.Bootstrap.trivialOnQuot K' :=
    mem_trivialOnQuot_of_centralizes hq' hρ'syl hnorm hcR'
  have hcm : vertex D ∈ centralizerModOdd ⊤ K' :=
    TwinEdge.mem_centralizerModOdd_of_commutator hv2 fun x hx => hcK'.2 x hx
  have hnotK : vertex D ∉ CFSG.ClassicalInvolution.Balance.Bootstrap.trivialOnQuot (tightCore R) := by
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
  have hV' : ∀ M ∈ twinSet (CoreAssembly.conjClass K') K',
      vertex D ∈ CFSG.ClassicalInvolution.Balance.Bootstrap.trivialOnQuot M → M = K' := by
    intro M hM hMc
    rw [hcls, twinSet_eq_of_mem_twinSet hz hK', TwinPerp.twinSet_eq_pair h2 hK' hne] at hM
    rcases hM with hM | hM
    · rw [hM] at hMc
      exact absurd hMc hnotK
    · exact hM
  have hΩ₃ : HypOmegaGen (CoreAssembly.conjClass (tightCore K')) := by
    rw [hRc₃, hcls]
    exact hΩ
  have hZ : Subgroup.center Y = ⊥ := h.center_eq_bot
  obtain ⟨ht', S₀', hdc, hq8c, hgenc, hOq, -, -, hlt⟩ :=
    Perp22Rest.exists_secPkg hstd₃ hRc₃ hZ hv2 hv1 hcm htC
  have hnotw := Perp22Rest.not_hasTwin_section hstd₃.datum hRc₃ hΩ₃ hv2 hv1 hcm htC ht' hV'
  have hidem : tightCore (tightCore (secR K' (vertex D))) = tightCore (secR K' (vertex D)) :=
    TwinEdge.tightCore_idem _
  have hdt := Perp22Rest.tightDatum_of_not_hasTwin hdc hidem hnotw
  have hcls' : TightClsR r (SecQ K' (vertex D)) (tightCore (secR K' (vertex D))) S₀'
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D))) ⟨⟨t, htC⟩, ht'⟩) :=
    ⟨hq8c, hgenc, hOq⟩
  have hex := (h.core.tbelow (SecQ K' (vertex D)) hlt _ S₀' _ hdt hcls').resolve_right
    (not_goodThreeElement_of_four_le hr hdt hq8c)
  by_cases hE2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D)))
      ⟨⟨t, htC⟩, ht'⟩)
  ·
    have hT : TightInO2 (oddQuotMk (vertex D) ⟨t, htC⟩) :=
      tightInO2_oddQuot_of_subnormal (isSubnormal_subnormalClosure _) ht' hE2
    exact hyp51At_vertex_of_inO2 hr h hW hnc D htC (Subgroup.subset_closure (Set.mem_insert _ _)) hz1 hT
  ·
    exfalso
    rcases hex with h2' | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact hE2 h2'
    · exact hV hr Y R S t h h2 W hW htW hS4 hnc K' hK' hne D htC ht' S₀' hdt hcls' hE2 he
    · exact hV hr Y R S t h h2 W hW htW hS4 hnc K' hK' hne D htC ht' S₀' hdt hcls' hE2 he
    · exact hE2 (tightInO2_of_twinE4' hr hNo hdc hq8c (Perp22Rest.twinE4_of_tightE4 h4))

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
