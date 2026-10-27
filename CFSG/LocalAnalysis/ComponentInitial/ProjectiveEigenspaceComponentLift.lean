module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponentsTransfer

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification CatalogueBProjectiveInvolution
open scoped MatrixGroups

namespace ProjectiveEigenspace

variable {K : Type*} [Field K] {n : ℕ}

theorem commutator_le_ordinaryRange [Nonempty (Fin n)] (T : GL (Fin n) K) :
    commutator (centralizer {ProjGenLinGroup.mk T}) ≤ (ordinaryCentralizerProjection T).range := by
  rw [← projectiveScalarCharacter_kernel_eq]
  exact Abelianization.commutator_subset_ker _

theorem le_ordinaryRange_of_perfect [Nonempty (Fin n)] (T : GL (Fin n) K)
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})} (hB : ⁅B, B⁆ = B) :
    B ≤ (ordinaryCentralizerProjection T).range := by
  rw [← hB]
  refine (commutator_mono le_top le_top).trans ?_
  rw [← _root_.commutator_def]
  exact commutator_le_ordinaryRange T

theorem comap_le_centralizer (T : GL (Fin n) K) {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hB : B ≤ (ordinaryCentralizerProjection T).range) :
    (B.map (centralizer {ProjGenLinGroup.mk T}).subtype).comap ProjGenLinGroup.mk ≤
      centralizer {T} := by
  intro g hg
  obtain ⟨b, hb, hbg⟩ := mem_map.1 (mem_comap.1 hg)
  obtain ⟨x, hx⟩ := hB hb
  have h1 : ProjGenLinGroup.mk x.val = ProjGenLinGroup.mk g := by
    rw [← hbg, ← hx]
    rfl
  obtain ⟨z, hz, hxz⟩ := ProjGenLinGroup.mk_eq_mk_iff'.1 h1
  rw [← hxz]
  exact mul_mem x.2 (center_le_centralizer _ hz)

theorem comap_eq_map_comap (T : GL (Fin n) K) {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hB : B ≤ (ordinaryCentralizerProjection T).range) :
    (B.map (centralizer {ProjGenLinGroup.mk T}).subtype).comap ProjGenLinGroup.mk =
      (B.comap (ordinaryCentralizerProjection T)).map (centralizer {T}).subtype := by
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, comap_le_centralizer T hB hg⟩, ?_, rfl⟩
    obtain ⟨b, hb, hbg⟩ := mem_map.1 (mem_comap.1 hg)
    have : ordinaryCentralizerProjection T ⟨g, comap_le_centralizer T hB hg⟩ = b :=
      Subtype.ext hbg.symm
    exact mem_comap.2 (this.symm ▸ hb)
  · rintro ⟨x, hx, rfl⟩
    exact mem_comap.2 ⟨_, hx, rfl⟩

theorem commutator_comap_eq_map (T : GL (Fin n) K)
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})}
    (hB : B ≤ (ordinaryCentralizerProjection T).range) :
    ⁅(B.map (centralizer {ProjGenLinGroup.mk T}).subtype).comap ProjGenLinGroup.mk,
        (B.map (centralizer {ProjGenLinGroup.mk T}).subtype).comap ProjGenLinGroup.mk⁆ =
      ⁅B.comap (ordinaryCentralizerProjection T), B.comap (ordinaryCentralizerProjection T)⁆.map
        (centralizer {T}).subtype := by
  rw [comap_eq_map_comap T hB, map_commutator]

theorem isComponent_commutator_comap [Nonempty (Fin n)] (T : GL (Fin n) K)
    {B : Subgroup (centralizer {ProjGenLinGroup.mk T})} (hB : CFSG.IsComponent B) :
    CFSG.IsComponent
        ⁅B.comap (ordinaryCentralizerProjection T), B.comap (ordinaryCentralizerProjection T)⁆ ∧
      ⁅B.comap (ordinaryCentralizerProjection T),
          B.comap (ordinaryCentralizerProjection T)⁆.map (ordinaryCentralizerProjection T) = B := by
  have hBB : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.1 hB.1.1
  have hBN := le_ordinaryRange_of_perfect T hBB
  set φ := ordinaryCentralizerProjection T with hφ
  set M : Subgroup φ.range := B.subgroupOf φ.range with hM
  have hcomap : M.comap φ.rangeRestrict = B.comap φ := by
    ext x
    simp [hM, mem_subgroupOf]
  have hMq : CFSG.IsQuasisimple M := (isQuasisimple_congr (subgroupOfEquivOfLe hBN)).2 hB.1
  have : Group.IsPerfect M := hMq.1
  have hcentral := ordinaryCentralizerProjection_rangeRestrict_kernel_central T
  have hsurj := φ.rangeRestrict_surjective
  have hderiv : CatalogueBCentralQuotient.derivedPreimage φ.rangeRestrict M =
      ⁅B.comap φ, B.comap φ⁆ := by
    rw [CatalogueBCentralQuotient.derivedPreimage_eq_commutator, hcomap]
  have hmap := CatalogueBCentralQuotient.derivedPreimage_map φ.rangeRestrict hsurj M
  have hsub := CatalogueBCentralQuotient.derivedPreimage_subnormal φ.rangeRestrict M
    hB.2.subgroupOf
  have : Group.IsPerfect (CatalogueBCentralQuotient.derivedPreimage φ.rangeRestrict M) :=
    CatalogueBCentralQuotient.derivedPreimage_perfect φ.rangeRestrict hsurj hcentral M
  have hq := (CatalogueBCentralQuotient.quasisimple_map_iff_of_perfect φ.rangeRestrict hcentral
    (CatalogueBCentralQuotient.derivedPreimage φ.rangeRestrict M)).2 (by rw [hmap]; exact hMq)
  rw [hderiv] at hq hsub hmap
  refine ⟨⟨hq, hsub⟩, ?_⟩
  have h2 := congrArg (Subgroup.map φ.range.subtype) hmap
  rwa [Subgroup.map_map, map_subgroupOf_eq_of_le hBN, MonoidHom.subtype_comp_rangeRestrict]
    at h2

variable (K n) in
theorem ker_mk_le_center :
    (ProjGenLinGroup.mk : GL (Fin n) K →* ProjGenLinGroup (Fin n) K).ker ≤
      center (GL (Fin n) K) := by
  rw [ProjGenLinGroup.ker_mk]

theorem commutator_comap_perfect_map {Q : Subgroup (ProjGenLinGroup (Fin n) K)}
    (hQ : ⁅Q, Q⁆ = Q) :
    ⁅⁅Q.comap ProjGenLinGroup.mk, Q.comap ProjGenLinGroup.mk⁆,
        ⁅Q.comap ProjGenLinGroup.mk, Q.comap ProjGenLinGroup.mk⁆⁆ =
        ⁅Q.comap ProjGenLinGroup.mk, Q.comap ProjGenLinGroup.mk⁆ ∧
      ⁅Q.comap ProjGenLinGroup.mk, Q.comap ProjGenLinGroup.mk⁆.map ProjGenLinGroup.mk = Q := by
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.2 hQ
  have hperf := CatalogueBCentralQuotient.derivedPreimage_perfect ProjGenLinGroup.mk
    ProjGenLinGroup.mk_surjective (ker_mk_le_center K n) Q
  have hmap := CatalogueBCentralQuotient.derivedPreimage_map ProjGenLinGroup.mk
    ProjGenLinGroup.mk_surjective Q
  rw [CatalogueBCentralQuotient.derivedPreimage_eq_commutator] at hperf hmap
  exact ⟨Subgroup.isPerfect_iff.1 hperf, hmap⟩

theorem commutator_le_center_of_commute {P R : Subgroup (GL (Fin n) K)}
    (h : ∀ p ∈ P, ∀ r ∈ R, ProjGenLinGroup.mk p * ProjGenLinGroup.mk r =
      ProjGenLinGroup.mk r * ProjGenLinGroup.mk p) :
    ⁅P, R⁆ ≤ center (GL (Fin n) K) := by
  rw [commutator_le]
  intro p hp r hr
  apply ker_mk_le_center K n
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact h p hp r hr

theorem commutator_eq_bot_of_le_center {B Q : Subgroup (GL (Fin n) K)} (hB : ⁅B, B⁆ = B)
    (h : ⁅B, Q⁆ ≤ center (GL (Fin n) K)) : ⁅B, Q⁆ = ⊥ :=
  perfect_double_commutator hB
    (commutator_eq_bot_iff_le_centralizer.2 (h.trans (center_le_centralizer _)))

end ProjectiveEigenspace

end CFSG.LocalAnalysis.ComponentInitial
