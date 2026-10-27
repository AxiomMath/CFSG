module

public import CFSG.GH74.Generic.S3.LyVert
public import CFSG.GH74.Generic.S3.Main19

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS (InG2 InC2 InT2 InB2 InCalK2)
open scoped MatrixGroups commutatorElement

@[expose] def LyNotDiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K →
    ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G) (hnd : NbrData G t p f x y Iw Iv),
      imgBar x Iw = K →
      ∀ (L : Subgroup (barQ ↥(centralizer ({y} : Set G)))), CFSG.IsComponent L →
        conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L ≠ L →
          ∀ (hAB : ⁅L, conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L⁆ = ⊥),
            ¬ S45.barSub y Iv ≤ (swapDiag hAB).range

@[expose] def LyVertTrivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K →
    ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G) (hnd : NbrData G t p f x y Iw Iv),
      imgBar x Iw = K →
      ∀ (L : Subgroup (barQ ↥(centralizer ({y} : Set G)))), CFSG.IsComponent L →
        conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L = L → S45.barSub y Iv ≤ L →
          InB2 ↥L → S45.barSub y Iv = L

theorem b_S3_LyJNT_of_parts
    (hF : GenericKnownFacts)
    (hKG : TwoThinKGroupVerticalQ Gen4Cen) (hDiag : LyNotDiag) (hVert : LyVertTrivial) :
    B_S3_LyJNT := by
  intro G _ _ x K hset hmax hnt honly t p f y Iw Iv hnd himg
  obtain ⟨L, hL, hcases⟩ := hnd.pumpup
  have hKP : GLS.IsKProperSimple G :=
    ⟨hset.simple, hset.nonab, CFSG.GH74.kProper_of_kgh hset.kgh⟩
  rcases hcases with ⟨hv, hle⟩ | ⟨hne, hAB, hdiag⟩
  · have hyL : xbar y ∈ L := hle hnd.xbar_mem_barSub
    have hZ : center ↥L ≠ ⊥ := by
      intro hbot
      have hmem : (⟨xbar y, hyL⟩ : ↥L) ∈ center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.1 (xbar_mem_center y) g)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hnd.xbar_ne_one (congrArg Subtype.val hmem)
    by_cases hG2 : InG2 ↥L
    · exact (false_of_vertical_g2 hF hset hmax hnd.y_inv hL hG2 hyL hZ).elim
    · have hC2T2 : InC2 ↥L ∨ InT2 ↥L := by
        by_contra h
        rw [not_or] at h
        exact hG2 ⟨GLS.inCalK2_of_isComponent hKP hnd.y_inv hL, h.1, h.2⟩
      have hB2 := hnd.vertical_inB2 hKG hset.gen4 hC2T2 hL hv hle
      have heq := hVert G x K hset hmax hnt honly t p f y Iw Iv hnd himg L hL hv hle hB2
      rw [heq]
      exact hL
  · exact (hDiag G x K hset hmax hnt honly t p f y Iw Iv hnd himg L hL hne hAB hdiag).elim

end CFSG.GH74.Generic.S3
