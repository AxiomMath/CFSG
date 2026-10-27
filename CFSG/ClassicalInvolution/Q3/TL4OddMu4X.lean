module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4C
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XTag
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4N

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem coverSL4_core (hL : TightLargeHypR r n Y R S t) (hcov : CoverSL4 ↥(linkGrp R t)) :
    CoverSL4 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
  hcov.of_mulEquiv (linkLayerEquiv hL).symm

end Cit3

section Layers


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K' : Subgroup Y} {u x y x' : Y}

theorem exists_two_layers9 (hL : TightLargeHypR r n Y R S t)
    (h2 : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J))
    (hcov : CoverSL4 ↥(linkGrp R t)) (hF : E4FrameAt R t J K' u x y x') :
    ∃ L₁ L₂ : Subgroup Y,
      IsSectionMember 3 2 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₁ t ∧
        IsSectionMember 3 2 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₂ u ∧
        Q3AM.WeakClosureAt (x * y * x') L₁ ∧ Q3AM.NormalizesImageAt (x * y * x') u L₁ := by
  have hΩ := TightLargeHypR.typeRFam hL
  have hcl := hΩ.hyp.conjInvariant
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htr := vertexTriv_core hL h2
  have hcv := coverSL4_core hL hcov
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
  have hKJ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ.hyp hK₀ hJΩ hF.memJ
  have cttu : (t : Y) * (t * u) = t * u * t := by rw [mul_assoc, ctu, ← mul_assoc]
  have cutu : u * (t * u) = t * u * u := by rw [← mul_assoc, ← ctu]
  have hutu : u * (t * u) = t := by rw [← mul_assoc, ← ctu, mul_assoc, hu.sq, mul_one]
  have httu : t * (t * u) = u := by rw [← mul_assoc, ht.sq, one_mul]
  have hu1 : u * u * (u * u) = 1 := by rw [hu.sq, one_mul]
  have ht1 : t * t * (t * t) = 1 := by rw [ht.sq, one_mul]
  have htu1 : t * u * (t * u) * (t * u * (t * u)) = 1 := by rw [htu.sq, one_mul]
  have hs : x * (y * x') = x * y * x' := by rw [← mul_assoc]
  have huΛ : u ∈ linkLayer R t :=
    coreAt_le_linkLayerAt hF.memJ (mem_coreAt_of_sq_sq hu.mem hu1 ctu.symm)
  have htΛ : t ∈ linkLayer R t := by
    have h1 := (linkLayerAt _ _ t).mul_mem huΛ
      (coreAt_le_linkLayerAt hF.memK (mem_coreAt_of_sq_sq htu.mem htu1 cttu.symm))
    rwa [hutu] at h1
  obtain ⟨L₁, hL₁⟩ := exists_layer9_at_vertex hΩ hK₀ ht htr hcv
    (mem_coreAt_of_sq_sq hF.memx hx4 ctx.eq.symm)
    ((linkLayerAt _ _ t).mul_mem
      (coreAt_le_linkLayerAt hF.memJ (mem_coreAt_of_sq_sq hF.memy hy4 cty.eq.symm))
      (coreAt_le_linkLayerAt hF.memK (mem_coreAt_of_sq_sq hF.memx' hx'4 ctx'.eq.symm)))
    (by rw [mul_mul_self_of_comm cyx', hF.sqy, hF.sqx', hutu]) htΛ (by rw [hs]; exact hs2)
  obtain ⟨g, hgJ'⟩ := hJΩ
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgt : g * t * g⁻¹ = u := by
    have h1 := ht.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  have htrJ := htr.conj hcl g
  have hcvJ := coverSL4_conj hcl hcv g
  rw [hgJ, hgt] at htrJ hcvJ
  have hs' : y * (x * x') = x * y * x' := by rw [← mul_assoc, ← cxy]
  obtain ⟨L₂, hL₂⟩ := exists_layer9_at_vertex hΩ (hgJ ▸ hΩ.hyp.conjInvariant g _ hK₀) hu htrJ
    hcvJ (mem_coreAt_of_sq_sq hF.memy hy4 cuy.eq.symm)
    ((linkLayerAt _ _ u).mul_mem
      (coreAt_le_linkLayerAt hKJ (mem_coreAt_of_sq_sq hF.memx hx4 cux.eq.symm))
      (coreAt_le_linkLayerAt hF.memKJ (mem_coreAt_of_sq_sq hF.memx' hx'4 cux'.eq.symm)))
    (by rw [mul_mul_self_of_comm cxx', hF.sqx, hF.sqx', httu])
    (by
      have h1 := (linkLayerAt _ _ u).mul_mem
        (coreAt_le_linkLayerAt hKJ (mem_coreAt_of_sq_sq ht.mem ht1 ctu))
        (coreAt_le_linkLayerAt hF.memKJ (mem_coreAt_of_sq_sq htu.mem htu1 cutu.symm))
      rwa [httu] at h1)
    (by rw [hs']; exact hs2)
  rw [hs] at hL₁
  rw [hs'] at hL₂
  have hwc : Q3AM.WeakClosureAt (x * y * x') L₁ := fun h hh hR =>
    weakClosure_of_linkLayer hΩ hK₀ ht hL₁ hh hR
  have huC : u ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ctu.symm
  have hus : u ∈ Subgroup.centralizer ({x * y * x'} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hF.comm_us
  exact ⟨L₁, L₂, hL₁.mem, hL₂.mem, hwc,
    Q3AM.normalizesImageAt_of_conjSub_eq (hL₁.norm u huC hus)⟩

end Layers

end CFSG.ClassicalInvolution.Q3.TL4
