module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4V
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem mem_coreAt_of_sq_sq {Y : Type} [Group Y] {L : Subgroup Y} {a e : Y} (he : e ∈ L)
    (h4 : e * e * (e * e) = 1) (hea : e * a = a * e) : e ∈ coreAt a L :=
  le_coreAt a (isPGroup_zpowers_of_sq_sq h4) (Subgroup.zpowers_le.mpr he)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hea))
    (Subgroup.mem_zpowers e)

theorem mul_mul_self_of_comm {Y : Type} [Group Y] {a b : Y} (h : a * b = b * a) :
    a * b * (a * b) = a * a * (b * b) := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← h]
    _ = a * a * (b * b) := by group

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem vertexTriv_core (hL : TightLargeHypR r n Y R S t)
    (h2 : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    VertexTriv (CoreAssembly.conjClass (tightCore R)) (tightCore R) t :=
  fun _ hm _ hℓ => commutator_mem_oddCoreOf_linkLayer hL h2 hm hℓ

theorem coverSp4_core (hL : TightLargeHypR r n Y R S t) (hcov : CoverSp4 ↥(linkGrp R t)) :
    CoverSp4 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
  hcov.of_mulEquiv (linkLayerEquiv hL).symm

end Cit3

section Layers


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K' : Subgroup Y} {u x y x' : Y}

theorem exists_three_layers3 (hL : TightLargeHypR r n Y R S t)
    (h2 : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J))
    (hcov : CoverSp4 ↥(linkGrp R t)) (hF : E4FrameAt R t J K' u x y x') :
    ∃ L₁ L₂ L₃ : Subgroup Y,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₁ t ∧
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₂ u ∧
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₃ (t * u) := by
  have hΩ := TightLargeHypR.typeRFam hL
  have hcl := hΩ.hyp.conjInvariant
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htr := vertexTriv_core hL h2
  have hcv := coverSp4_core hL hcov
  have hu := hF.invJ
  have htu := hF.invK
  obtain ⟨ctx, cty, ctx'⟩ := hF.commute_t
  obtain ⟨cux, cuy, cux'⟩ := hF.commute_u
  have ctu : t * u = u * t := hF.comm_tu
  have cxy : x * y = y * x := hF.cxy
  have cxx' : x * x' = x' * x := hF.cxx'
  have cyx' : y * x' = x' * y := hF.cyx'
  have hx4 : x * x * (x * x) = 1 := by rw [hF.sqx, ht.sq]
  have hy4 : y * y * (y * y) = 1 := by rw [hF.sqy, hu.sq]
  have hx'4 : x' * x' * (x' * x') = 1 := by rw [hF.sqx', htu.sq]
  have hs2 := hF.sq_s ht.sq hu.sq
  have hJΩ := hF.memJ.1
  have hK'Ω := hF.memK.1
  have hKJ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ.hyp hK₀ hJΩ hF.memJ
  have hKK' : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K' :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ.hyp hK₀ hK'Ω hF.memK
  have hJK' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K' :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ.hyp hJΩ hK'Ω hF.memKJ
  have cxtu : Commute (t * u) x := ctx.mul_left cux
  have cytu : Commute (t * u) y := cty.mul_left cuy
  have cttu : (t : Y) * (t * u) = t * u * t := by rw [mul_assoc, ctu, ← mul_assoc]
  have cutu : u * (t * u) = t * u * u := by rw [← mul_assoc, ← ctu]
  have hutu : u * (t * u) = t := by rw [← mul_assoc, ← ctu, mul_assoc, hu.sq, mul_one]
  have httu : t * (t * u) = u := by rw [← mul_assoc, ht.sq, one_mul]
  have hu1 : u * u * (u * u) = 1 := by rw [hu.sq, one_mul]
  have ht1 : t * t * (t * t) = 1 := by rw [ht.sq, one_mul]
  have htu1 : t * u * (t * u) * (t * u * (t * u)) = 1 := by rw [htu.sq, one_mul]
  obtain ⟨L₁, h₁⟩ : ∃ L : Subgroup Y,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * (y * x')} : Set Y)) L t := by
    refine exists_layer3_at_vertex hΩ hK₀ ht htr hcv
      (mem_coreAt_of_sq_sq hF.memx hx4 ctx.eq.symm)
      ((linkLayerAt _ _ t).mul_mem
        (coreAt_le_linkLayerAt hF.memJ (mem_coreAt_of_sq_sq hF.memy hy4 cty.eq.symm))
        (coreAt_le_linkLayerAt hF.memK (mem_coreAt_of_sq_sq hF.memx' hx'4 ctx'.eq.symm)))
      (by rw [mul_mul_self_of_comm cyx', hF.sqy, hF.sqx', hutu]) ?_
      (by rw [← mul_assoc x y x']; exact hs2)
    have h1 := (linkLayerAt _ _ t).mul_mem
      (coreAt_le_linkLayerAt hF.memJ (mem_coreAt_of_sq_sq hu.mem hu1 ctu.symm))
      (coreAt_le_linkLayerAt hF.memK (mem_coreAt_of_sq_sq htu.mem htu1 cttu.symm))
    rwa [hutu] at h1
  obtain ⟨g, hgJ'⟩ := hJΩ
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgt : g * t * g⁻¹ = u := by
    have h1 := ht.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  have htrJ := htr.conj hcl g
  have hcvJ := coverSp4_conj hcl hcv g
  rw [hgJ, hgt] at htrJ hcvJ
  obtain ⟨L₂, h₂⟩ : ∃ L : Subgroup Y,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({y * (x * x')} : Set Y)) L u := by
    refine exists_layer3_at_vertex hΩ (hgJ ▸ hΩ.hyp.conjInvariant g _ hK₀) hu htrJ hcvJ
      (mem_coreAt_of_sq_sq hF.memy hy4 cuy.eq.symm)
      ((linkLayerAt _ _ u).mul_mem
        (coreAt_le_linkLayerAt hKJ (mem_coreAt_of_sq_sq hF.memx hx4 cux.eq.symm))
        (coreAt_le_linkLayerAt hF.memKJ (mem_coreAt_of_sq_sq hF.memx' hx'4 cux'.eq.symm)))
      (by rw [mul_mul_self_of_comm cxx', hF.sqx, hF.sqx', httu]) ?_ ?_
    · have h1 := (linkLayerAt _ _ u).mul_mem
        (coreAt_le_linkLayerAt hKJ (mem_coreAt_of_sq_sq ht.mem ht1 ctu))
        (coreAt_le_linkLayerAt hF.memKJ (mem_coreAt_of_sq_sq htu.mem htu1 cutu.symm))
      rwa [httu] at h1
    · have e : y * (x * x') = x * y * x' := by rw [← mul_assoc, ← cxy]
      rw [e]
      exact hs2
  obtain ⟨h, hhK'⟩ := hK'Ω
  have hhK : conjSub h (tightCore R) = K' := hhK'
  have hht : h * t * h⁻¹ = t * u := by
    have h1 := ht.conj h
    rw [hhK] at h1
    exact h1.eq htu
  have htrK := htr.conj hcl h
  have hcvK := coverSp4_conj hcl hcv h
  rw [hhK, hht] at htrK hcvK
  have hxyx' : x' * (x * y) = x * y * x' := by
    rw [← mul_assoc, ← cxx', mul_assoc, ← cyx', ← mul_assoc]
  obtain ⟨L₃, h₃⟩ : ∃ L : Subgroup Y,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({x' * (x * y)} : Set Y)) L (t * u) := by
    refine exists_layer3_at_vertex hΩ (hhK ▸ hΩ.hyp.conjInvariant h _ hK₀) htu htrK hcvK
      (mem_coreAt_of_sq_sq hF.memx' hx'4 (ctx'.mul_left cux').eq.symm)
      ((linkLayerAt _ _ (t * u)).mul_mem
        (coreAt_le_linkLayerAt hKK' (mem_coreAt_of_sq_sq hF.memx hx4 cxtu.eq.symm))
        (coreAt_le_linkLayerAt hJK' (mem_coreAt_of_sq_sq hF.memy hy4 cytu.eq.symm)))
      (by rw [mul_mul_self_of_comm cxy, hF.sqx, hF.sqy]) ?_ ?_
    · exact (linkLayerAt _ _ (t * u)).mul_mem
        (coreAt_le_linkLayerAt hKK' (mem_coreAt_of_sq_sq ht.mem ht1 cttu))
        (coreAt_le_linkLayerAt hJK' (mem_coreAt_of_sq_sq hu.mem hu1 cutu))
    · rw [hxyx']
      exact hs2
  rw [← mul_assoc x y x'] at h₁
  rw [show y * (x * x') = x * y * x' by rw [← mul_assoc, ← cxy]] at h₂
  rw [hxyx'] at h₃
  exact ⟨L₁, L₂, L₃, h₁, h₂, h₃⟩

end Layers

end CFSG.ClassicalInvolution.Q3.TL4
