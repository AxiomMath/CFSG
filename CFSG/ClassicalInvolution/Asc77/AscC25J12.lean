module

public import CFSG.ClassicalInvolution.Asc77.AscC25J11
public import CFSG.ClassicalInvolution.Asc77.AscC25J10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem crossIn_twinSect0 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hF' : IsFAut R' a) (hat : a * t' = t' * a)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K' a))) :
    ∃ (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
      (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
      (a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))),
      TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
        (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀ := by
  have ht'a : t' ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hat.symm
  refine ⟨ht'a, ?_⟩
  have d' := twinCtx'_of_hyp25 h
  have hzKa : z ∈ K' ⊓ Subgroup.centralizer ({a} : Set G) := ⟨h.hz'.mem, hzA⟩
  set w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩ with hwdef
  have hw : conjSub (w : G) K' = K := conjSub_t'_K' h
  set L := crossIn K' a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hLmem : L ∈ conjFamily L := ⟨1, conjSub_one L⟩
  have hL'mem : conjSub w L ∈ conjFamily L := ⟨w, rfl⟩
  have hLX : L ≤ X := le_conjGen hLmem
  have hL'X : conjSub w L ≤ X := le_conjGen hL'mem
  have hzw : w * ⟨z, hzA⟩ * w⁻¹ = (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
    apply Subtype.ext
    change t' * z * t'⁻¹ = z
    calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [t'_comm_z h]
      _ = z := by group
  have hu₁ : IsUniqueInvolution L ⟨z, hzA⟩ := by
    have := crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa 1
    have e : (1 : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z, hzA⟩ * 1⁻¹ = ⟨z, hzA⟩ := by group
    rw [conjSub_one, e] at this
    exact this
  have hu₂ : IsUniqueInvolution (conjSub w L) ⟨z, hzA⟩ := by
    have := crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa w
    rwa [hzw] at this
  have hne : conjSub w L ≠ L := crossIn_swap_ne d' hΛ hw
  have hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hu₁.mem
  set z₀ : ↥X ⧸ classicalInvolutionOddCore ↥X := QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩ with hz₀
  have hz₀A : IsUniqueInvolution (secImg X L) z₀ := by
    have h1 := crossIn_isUniqueInvolution_secImg h.hz' hzA hzKa 1
    have e1 : (QuotientGroup.mk' _ ⟨1 * ⟨z, hzA⟩ * 1⁻¹, le_conjGen ⟨1, rfl⟩
        (crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa 1).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp
    rw [e1, conjSub_one] at h1
    exact h1
  have hz₀A' : IsUniqueInvolution (secImg X (conjSub w L)) z₀ := by
    have h1 := crossIn_isUniqueInvolution_secImg h.hz' hzA hzKa w
    have e1 : (QuotientGroup.mk' _ ⟨w * ⟨z, hzA⟩ * w⁻¹, le_conjGen ⟨w, rfl⟩
        (crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa w).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      exact hzw
    rw [e1] at h1
    exact h1
  have hΛ₁ : HypOmegaModU (.sl2 3 1) (restrictFamily (conjFamily L) X) :=
    hypOmegaModU_restrict hΛ X
  have hne_img : secImg X L ≠ secImg X (conjSub w L) := by
    intro heq
    have hX1 : IsUniqueInvolution (L.subgroupOf X) ⟨⟨z, hzA⟩, hzX⟩ :=
      S1911.isUniqueInvolution_subgroupOf hu₁ hLX
    have hX2 : IsUniqueInvolution ((conjSub w L).subgroupOf X) ⟨⟨z, hzA⟩, hzX⟩ :=
      S1911.isUniqueInvolution_subgroupOf hu₂ hL'X
    have hsub := eq_of_map_eq_of_twin_three hΛ₁ ⟨L, hLmem, hLX, rfl⟩
      ⟨conjSub w L, hL'mem, hL'X, rfl⟩ hX1 hX2 heq
    have e1 := Subgroup.map_subgroupOf_eq_of_le hLX
    have e2 := Subgroup.map_subgroupOf_eq_of_le hL'X
    rw [hsub] at e1
    exact hne (e2.symm.trans e1)
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hF'
  have hyK' : y ∈ K' := h.hR'syl.1 hyR'
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyL : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ L :=
    Subgroup.mem_subgroupOf.mpr ⟨hyK', hyC⟩
  have hyX : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hyL
  have hysq : y * y = z := C25X.sq_eq_of_orderOf_four h.hz' hyK' hy4
  have hbL' : w * ⟨y, hyC⟩ * w⁻¹ ∈ conjSub w L := conj_mem_conjSub hyL
  have hbX : w * ⟨y, hyC⟩ * w⁻¹ ∈ X := hL'X hbL'
  refine ⟨hzX, QuotientGroup.mk ⟨⟨y, hyC⟩, hyX⟩, QuotientGroup.mk ⟨w * ⟨y, hyC⟩ * w⁻¹, hbX⟩,
    ⟨(mem_secFamily_iff L _).mpr ⟨1, by rw [conjSub_one]⟩, (mem_secFamily_iff L _).mpr ⟨w, rfl⟩,
      hne_img, hz₀A, hz₀A',
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbL'), ?_, ?_, ?_, ?_⟩⟩
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    apply Subtype.ext
    exact hysq
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    have e : w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) =
        w * (⟨y, hyC⟩ * ⟨y, hyC⟩) * w⁻¹ := by group
    have e2 : (⟨y, hyC⟩ * ⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = ⟨z, hzA⟩ :=
      Subtype.ext hysq
    change w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) = ⟨z, hzA⟩
    rw [e, e2, hzw]
  · intro M hM hMn
    have := crossIn_nbr_quot d' hzKa hΛ hw 1 (M := M) (by rwa [conjSub_one])
    rwa [one_mul] at this
  · intro M hM hMn
    have := crossIn_nbr_quot d' hzKa hΛ hw w (M := M) hMn
    have hww : w * w = 1 := Subtype.ext h.ht'2
    rwa [hww, conjSub_one] at this

end Datum

end CFSG.ClassicalInvolution.Asc77.C25J
