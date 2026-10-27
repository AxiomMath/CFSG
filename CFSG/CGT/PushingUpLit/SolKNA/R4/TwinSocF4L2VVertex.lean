module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4LayAct
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4VtxFacts
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VLay
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Layer

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
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
open scoped commutatorElement

section Aux

variable {Y : Type} [Group Y] [Finite Y]

theorem uniqueInv_comm {K : Subgroup Y} {u : Y} (h : IsUniqueInvolution K u) {k : Y} (hk : k ∈ K) :
    k * u = u * k := by
  have hm : k * u * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk h.mem) (K.inv_mem hk)
  have hs : k * u * k⁻¹ * (k * u * k⁻¹) = 1 := by
    calc k * u * k⁻¹ * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
      _ = 1 := by rw [h.sq, mul_one, mul_inv_cancel]
  rcases h.unique _ hm hs with h1 | h1
  · exfalso
    apply h.ne_one
    have : u = k⁻¹ * (k * u * k⁻¹) * k := by group
    rw [this, h1]
    group
  · calc k * u = k * u * k⁻¹ * k := by group
      _ = u * k := by rw [h1]

end Aux

section Act

variable {Y : Type} [Group Y] [Finite Y]

theorem layerAct_pow_of_pow {K' : Subgroup Y} {c x t : Y} {n : ℕ}
    (hxC : x ∈ Subgroup.centralizer ({c} : Set Y)) (hx : x ∈ Subgroup.normalizer (K' : Set Y))
    (htC : t ∈ Subgroup.centralizer ({c} : Set Y)) (ht' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈
      secH K' c) (hxn : x ^ n = t) :
    layerAct K' c (LayerΓ.ofNormalizer hxC hx) ^ n =
      MulAut.conj (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c))
        (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c))) := by
  rw [← map_pow]
  have : LayerΓ.ofNormalizer hxC hx ^ n = LayerΓ.ofMem (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c)) := by
    apply LayerΓ.toY_injective K' c
    rw [map_pow, LayerΓ.toY_ofNormalizer, LayerΓ.toY_ofMem, hxn]
  rw [this, layerAct_of_mem]

theorem layerAct_fix_of_comm {K' : Subgroup Y} {c t : Y}
    (htC : t ∈ Subgroup.centralizer ({c} : Set Y)) (ht' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈
      secH K' c) (k : LayerΓ K' c) (hk : LayerΓ.toY K' c k * t = t * LayerΓ.toY K' c k) :
    layerAct K' c k (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c))
      (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c))) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c)) (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c)) := by
  show Perp22.actQuot (secH K' c) k (QuotientGroup.mk _) = QuotientGroup.mk _
  rw [Perp22.actQuot_apply_mk]
  refine congrArg QuotientGroup.mk (Subtype.ext (Subtype.ext ?_))
  show (LayerΓ.toY K' c k) * t * (LayerΓ.toY K' c k)⁻¹ = t
  rw [hk, mul_inv_cancel_right]

end Act

section Main

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem frame_x₁_order (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) {K' : Subgroup Y}
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) :
    4 * D.m = 2 ^ (r - 1) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hcard : Nat.card D.F.ρ.R = 2 * Nat.card ↥(D.F.ρ.R ⊓ W) :=
    Q3CL.Thompson.D_card hΩ hW D.F.ρ.hR
  have hcard2 : Nat.card ↥(D.F.ρ.R ⊓ W) = 4 * D.m := by
    rw [← D.h₁, Nat.card_zpowers, D.o₁]
  have hρsyl : IsSylow2In D.F.ρ.R (tightCore R) := by
    have := D.F.ρ.hRK
    rwa [D.hρK] at this
  have hsyl : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := h.core.datum.sylow_core
  have h1 := natCard_eq_pow_of_isSylow2In hρsyl
  have h2 := natCard_eq_pow_of_isSylow2In hsyl
  have hS : Nat.card ((S : Subgroup R).map R.subtype) = 2 ^ r := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have h4 : 4 * 2 ^ (r - 2) = 2 ^ r := by
      obtain ⟨s, hs⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
      rw [hs, Nat.add_sub_cancel, pow_add]; ring
    rw [Nat.card_congr h.core.quat.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, h4]
  have h3 : Nat.card D.F.ρ.R = 2 ^ r := by rw [h1, ← h2, hS]
  rw [h3, hcard2] at hcard
  have h4 : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
  omega

theorem vertexEdgelessExclR_of_inputs2 {r n : ℕ} (hList : SmallListR) (hO : NoDatumOtherR r)
    (h6 : ∀ m, TightLargeEdgeSR r m) (hL3 : SocF4L3 r) (hU3 : SocF4U3 r) :
    Perp24.VertexEdgelessExclR r n := by
  intro hr Y _ _ R S t h h2 W hW htW hS4 hnc K' hK' hne D htC ht' S₀ hdt hcls' hE2 hE
  classical
  have vf := vtxFacts hr h h2 hW hnc hK' hne D
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hm₀ : Even D.m := twoFrame_m_even hr h hW D
  have hvW : vertex D ∈ W := vertex_mem_W D hc hm₀
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hlt : Nat.card (SecQ K' (vertex D)) < n := by
    have hZ : Subgroup.center Y = ⊥ := h.center_eq_bot
    have h1 : Nat.card (SecQ K' (vertex D)) ≤ Nat.card ↥(secH K' (vertex D)) :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2' : Nat.card ↥(secH K' (vertex D)) ≤
        Nat.card ↥(Subgroup.centralizer ({vertex D} : Set Y)) := Subgroup.card_le_card_group _
    have h3 := PhilipHall.Frame.TwinEdge.card_centralizer_lt_of_center hZ vf.ne
    rw [← h.core.card]
    omega
  have hm4 : 4 * D.m = 2 ^ (r - 1) := frame_x₁_order hr h hW D
  have hx₁R : D.x₁ ∈ D.F.ρ.R := by
    have : D.x₁ ∈ D.F.ρ.R ⊓ W := D.h₁ ▸ Subgroup.mem_zpowers D.x₁
    exact this.1
  have hx₁K : D.x₁ ∈ tightCore R := by
    have := D.F.ρ.hRK.1 hx₁R
    rwa [D.hρK] at this
  have hx₂ : D.x₁ ^ 2 ^ (r - 2) = t := by
    calc D.x₁ ^ 2 ^ (r - 2) = D.x₁ ^ (2 * D.m) := by
          congr 1
          have : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by rw [← pow_succ']; congr 1; omega
          omega
      _ = t := D.z₁
  have hxk : D.x₁ ^ 2 ^ (r - 1) = 1 := by
    rw [← hm4, ← D.o₁]; exact pow_orderOf_eq_one _
  have hxC : D.x₁ ∈ Subgroup.centralizer ({vertex D} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hc _ D.x₁_mem_W (vertex D) hvW)
  have hxtq := vf.twin_le hx₁K
  have hxN : D.x₁ ∈ Subgroup.normalizer (K' : Set Y) := hxtq.1
  have hvN : (⟨D.x₁, hxC⟩ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) ∈
      Subgroup.normalizer ((tightCore (K'.subgroupOf (Subgroup.centralizer ({vertex D} : Set Y))) :
        Subgroup ↥(Subgroup.centralizer ({vertex D} : Set Y))) :
          Set ↥(Subgroup.centralizer ({vertex D} : Set Y))) := mem_normalizer_core hxC hxN
  have hvk : (⟨D.x₁, hxC⟩ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) ^ 2 ^ (r - 1) = 1 :=
    Subtype.ext (by simpa using hxk)
  have hvt : ∀ y ∈ tightCore (K'.subgroupOf (Subgroup.centralizer ({vertex D} : Set Y))),
      ⁅(((⟨D.x₁, hxC⟩ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) :
        ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y),
        ((y : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)⁆ ∈ oddCoreIn K' := by
    intro y hy
    have hyK' : ((y : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y) ∈ K' :=
      Subgroup.mem_subgroupOf.mp (tightCore_le _ hy)
    exact hxtq.2 _ hyK'
  obtain ⟨P, hP, hPfix⟩ := exists_sylow_centralized' hvN hvk hvt
  have hSylV := isSylow2In_image_section hP
  let Sb : Sylow 2 ↥(tightCore (secR K' (vertex D))) := TwinEdge.sylowOf hSylV
  have hmapS : (Sb : Subgroup ↥(tightCore (secR K' (vertex D)))).map
      (tightCore (secR K' (vertex D))).subtype =
      (P.subgroupOf (secH K' (vertex D))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D)))) :=
    Subgroup.map_subgroupOf_eq_of_le hSylV.1
  have hdb := TightDatum.ofSylow hdt Sb
  have hcb : TightClsR r (SecQ K' (vertex D)) (tightCore (secR K' (vertex D))) Sb
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' (vertex D))) ⟨⟨t, htC⟩, ht'⟩) :=
    ⟨⟨(Sylow.equiv Sb S₀).trans hcls'.1.some⟩, hcls'.2.1, hcls'.2.2⟩
  have hKq : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    Perp23.isPGroup_quot_of_member h (CoreAssembly.mem_conjClass_self _)
  have hρsyl : IsSylow2In D.F.ρ.R (tightCore R) := by
    have := D.F.ρ.hRK
    rwa [D.hρK] at this
  have hrel : (D.F.ρ.R ⊓ W).relIndex D.F.ρ.R = 2 := by
    have hcard := Q3CL.Thompson.D_card hΩ hW D.F.ρ.hR
    have hrel := Subgroup.relIndex_mul_card (H := D.F.ρ.R ⊓ W) (K := D.F.ρ.R)
    rw [inf_eq_left.mpr (inf_le_left : D.F.ρ.R ⊓ W ≤ D.F.ρ.R)] at hrel
    have hpos : 0 < Nat.card ↥(D.F.ρ.R ⊓ W) := Nat.card_pos
    have h3 : (D.F.ρ.R ⊓ W).relIndex D.F.ρ.R * Nat.card ↥(D.F.ρ.R ⊓ W) =
        2 * Nat.card ↥(D.F.ρ.R ⊓ W) := by
      rw [hrel, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hcr : vertex D * D.F.ρ.r * (vertex D)⁻¹ = t * D.F.ρ.r := by
    have e := vertex_r_eq D hc hm₀
    have hcinv : (vertex D)⁻¹ = vertex D := inv_eq_of_mul_eq_one_right vf.sq
    have e' : D.F.ρ.r * vertex D = vertex D * t * D.F.ρ.r := by
      calc D.F.ρ.r * vertex D = (D.F.ρ.r * vertex D * D.F.ρ.r⁻¹) * D.F.ρ.r := by group
        _ = vertex D * t * D.F.ρ.r := by rw [e]
    rw [hcinv]
    calc vertex D * D.F.ρ.r * vertex D = vertex D * (D.F.ρ.r * vertex D) := by group
      _ = vertex D * (vertex D * t * D.F.ρ.r) := by rw [e']
      _ = (vertex D * vertex D) * t * D.F.ρ.r := by group
      _ = t * D.F.ρ.r := by rw [vf.sq, one_mul]
  let tH : ↥(secH K' (vertex D)) := ⟨⟨t, htC⟩, ht'⟩
  let Ĥ : Subgroup (LayerΓ K' (vertex D)) :=
    (Subgroup.centralizer ({tH} : Set ↥(secH K' (vertex D)))).map
      (Subgroup.inclusion Subgroup.le_normalizer)
  have hOK : oddCoreIn (tightCore R) ≤ tightCore R := Subgroup.map_subtype_le _
  refine false_of_layer_action2 hr h.core.below h.core.tbelow hList hO h6 hL3 hU3 hlt hdb hcb hE2 hE
    (layerAct K' (vertex D)) (𝒦 := layerK K' (tightCore R) (vertex D))
    (𝒩 := layerO K' (tightCore R) (vertex D)) (Ĥ := Ĥ) (e := LayerΓ.ofNormalizer hxC hxN)
    ?_ ?_ (layerAct_pow_of_pow hxC hxN htC ht' hx₂) ?_ (odd_card_layerO K' (tightCore R) (vertex D))
    ?_ ?_ ?_ ?_ ?_
  ·
    exact Subgroup.mem_comap.mpr (by rw [LayerΓ.toY_ofNormalizer]; exact hx₁K)
  ·
    intro s hs
    rw [hmapS] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hpP : ((p : ↥(secH K' (vertex D))) : ↥(Subgroup.centralizer ({vertex D} : Set Y))) ∈ P :=
      Subgroup.mem_subgroupOf.mp hp
    show Perp22.actQuot (secH K' (vertex D)) (LayerΓ.ofNormalizer hxC hxN) (QuotientGroup.mk p) =
      QuotientGroup.mk p
    rw [Perp22.actQuot_apply_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (hPfix _ hpP))
  ·
    intro a ha b hb
    have ha' : LayerΓ.toY K' (vertex D) a ∈ tightCore R := ha
    have hb' : LayerΓ.toY K' (vertex D) b ∈ tightCore R := hb
    show LayerΓ.toY K' (vertex D) ⁅a, b⁆ ∈ oddCoreIn (tightCore R)
    rw [map_commutatorElement]
    exact commutator_mem_oddCoreIn_of_centralizer hKq hρsyl hc hvW hrel D.F.ρ.hr D.F.ρ.hrW hcr hz.mem ht2
      ha' hb' (LayerΓ.toY_comm K' (vertex D) a) (LayerΓ.toY_comm K' (vertex D) b)
  ·
    intro g hg
    exact hOK hg
  ·
    intro k hk
    have hk' : LayerΓ.toY K' (vertex D) k ∈ tightCore R := hk
    obtain ⟨o, ho, p, hp, hop⟩ := exists_oddCore_mul_of_centralizer hKq hρsyl hc hvW hrel D.F.ρ.hr
      D.F.ρ.hrW hcr hz.mem ht2 hk' (LayerΓ.toY_comm K' (vertex D) k)
    rw [← D.h₁] at hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    refine ⟨k * (LayerΓ.ofNormalizer hxC hxN ^ j)⁻¹, ?_, j, by group⟩
    show LayerΓ.toY K' (vertex D) (k * (LayerΓ.ofNormalizer hxC hxN ^ j)⁻¹) ∈ oddCoreIn (tightCore R)
    rw [map_mul, map_inv, map_zpow, LayerΓ.toY_ofNormalizer, ← hop, mul_inv_cancel_right]
    exact ho
  ·
    intro k hk
    have hk' : LayerΓ.toY K' (vertex D) k ∈ tightCore R := hk
    exact layerAct_fix_of_comm htC ht' k (uniqueInv_comm hz hk')
  ·
    rintro _ ⟨h₀, hh₀, rfl⟩ k hk
    have hk' : LayerΓ.toY K' (vertex D) k ∈ tightCore R := hk
    have hh₀t : tH * h₀ = h₀ * tH := Subgroup.mem_centralizer_iff.mp hh₀ tH rfl
    have hgt : (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) * t =
        t * (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) := by
      have := congrArg (fun x : ↥(secH K' (vertex D)) => (((x : ↥(secH K' (vertex D))) :
        ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) hh₀t
      exact this.symm
    have hgc : (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) * vertex D =
        vertex D * (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) :=
      (LayerΓ.toY_comm K' (vertex D) (Subgroup.inclusion Subgroup.le_normalizer h₀)).symm
    have hfix := vf.twin_fix _ hgt hgc
    show LayerΓ.toY K' (vertex D) (Subgroup.inclusion Subgroup.le_normalizer h₀ * k *
      (Subgroup.inclusion Subgroup.le_normalizer h₀)⁻¹) ∈ tightCore R
    rw [map_mul, map_mul, map_inv]
    have hmem : (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) *
        LayerΓ.toY K' (vertex D) k * (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y))⁻¹ ∈
        conjSub (((h₀ : ↥(Subgroup.centralizer ({vertex D} : Set Y))) : Y)) (tightCore R) :=
      conj_mem_conjSub hk'
    rw [hfix] at hmem
    exact hmem
  ·
    intro q hq
    obtain ⟨h₀, hh₀, hh₀q⟩ := exists_layerElt_of_centralizes htC ht' hz2 q hq
    refine ⟨Subgroup.inclusion Subgroup.le_normalizer h₀, ⟨h₀, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro y rfl
      exact hh₀.symm
    · rw [← hh₀q]
      exact layerAct_of_mem h₀

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
