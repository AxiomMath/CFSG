module

public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley

theorem exists_unit_orderOf_eq_three_of_cube_root {L : Type} [Field L] (ω : L)
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : ∃ ζ : Lˣ, orderOf ζ = 3 := by
  have h0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have h3 : Units.mk0 ω h0 ^ 3 = 1 := by
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    linear_combination (ω - 1) * hω
  exact ⟨Units.mk0 ω h0, orderOf_eq_prime h3 fun h => hω1 (by simpa using congrArg Units.val h)⟩

theorem G2_eq_one_of_mem_rootCharStabilizer_three
    {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3)
    {w : WeylGroup .G2} (hw : ∀ i, w ∈ rootCharStabilizer (Pi.mulSingle i ζ)) : w = 1 := by
  have key : ∀ (v : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank), (w • v) i ≡ v i [ZMOD 3] := by
    intro v i
    have h0 : rootChar (Pi.mulSingle i ζ) (w • v) = rootChar (Pi.mulSingle i ζ) v := hw i v
    rw [rootChar_mulSingle_eq_zpow, rootChar_mulSingle_eq_zpow, zpow_eq_zpow_iff_modEq,
      hζ] at h0
    exact_mod_cast h0
  have a0 := key g2a g2ia
  have a1 := key g2a g2ir
  have r0 := key g2r g2ia
  have r1 := key g2r g2ir
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact eq_one_of_smul h1 h2
  all_goals
    exfalso
    rw [h1] at a0 a1
    rw [h2] at r0 r1
    revert a0 a1 r0 r1
    decide

theorem G2_eq_g2r_of_mem_rootCharKernel_three {L : Type} [Field L]
    {ζ : Lˣ} (hζ : orderOf ζ = 3) {α : Fin Tag.G2.rank → ℤ}
    (hα : α ∈ rootCharKernel (Pi.mulSingle g2ia ζ) ∩ {β | IsRoot .G2 β ∧ 0 < height β}) :
    α = g2r := by
  obtain ⟨⟨hroot, hchar⟩, -, hpos⟩ := hα
  rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at hchar
  rcases G2_root_eq_or_natAbs_ia_le hroot with rfl | rfl | ⟨h0, h2⟩
  · rfl
  · exact absurd hpos (by decide)
  · exact absurd hchar (not_dvd_of_natAbs_lt h0 (by omega))

theorem centralizer_torusTorsion_three_le {L : Type} [Field L]
    (ω : L) (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (g : ModGL .G2 L) (hg : g ∈ adjointGroup .G2 L)
    (hc : ∀ x ∈ CFSG.RankThree.Chevalley.torusTorsion L 3, g * x = x * g) :
    g ∈ torusGroup .G2 L := by
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_eq_three_of_cube_root ω hω hω1
  have hX : ∀ i, g ∈ toralCentralizer .G2 L (Pi.mulSingle i ζ) := fun i =>
    mem_toralCentralizer.2 ⟨hg, by
      rw [← hc _ (rootDiagUnit_mulSingle_mem_torusTorsion hζ i), mul_inv_cancel_right]⟩
  have hB := Chevalley_toral_centralizer_Bruhat_factors .G2 L (Pi.mulSingle g2ia ζ)
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hz1⟩ := hB.1 g (hX g2ia)
  obtain ⟨w', hw', h', hh', u', hu', v', hv', hz2⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .G2 L (Pi.mulSingle g2ir ζ)).1 g (hX g2ir)
  obtain ⟨hww, -, -, -⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
    (rootSpan_le_posUnipotent (fun α hα => hα.2) hu)
    (rootSpan_le_posUnipotent (fun α hα => hα.2) hu')
    (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
    (hz1.symm.trans hz2)
  rw [← hww] at hw'
  have hw1 : w = 1 := G2_eq_one_of_mem_rootCharStabilizer_three hζ fun i => by
    rcases fin_G2_cases i with rfl | rfl
    · exact hw
    · exact hw'
  subst hw1
  have hbot : rootSpan .G2 L (∅ : Set (Fin Tag.G2.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [inversionSet_one, Set.inter_empty, hbot, Subgroup.mem_bot] at hv
  subst hv
  have hS : rootCharKernel (Pi.mulSingle g2ia ζ) ∩ {β | IsRoot .G2 β ∧ 0 < height β} ⊆ {g2r} :=
    fun α hα => G2_eq_g2r_of_mem_rootCharKernel_three hζ hα
  have hur : u ∈ rootSubgroup .G2 L g2r := by
    have := rootSpan_mono hS hu
    rwa [rootSpan_singleton] at this
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hur
  rw [canonicalRep_one, mul_one, mul_one] at hz1
  have hfix := (mem_toralCentralizer.1 (hX g2ir)).2
  have e1 := conj_rootDiagUnit_of_mem_torusGroup (Pi.mulSingle g2ir ζ) hh
  have e2 := rootDiagUnit_conj_pinnedX (Pi.mulSingle g2ir ζ) isRoot_g2r c
  rw [rootChar_mulSingle_eq_zpow, g2r_ir, zpow_one] at e2
  have e3 : rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * (h * pinnedX .G2 L g2r c) *
      (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹ = h * pinnedX .G2 L g2r ((ζ : L) * c) := by
    calc _ = (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * h *
          (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹) *
          (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * pinnedX .G2 L g2r c *
            (rootDiagUnit .G2 (Pi.mulSingle g2ir ζ))⁻¹) := by group
      _ = _ := by rw [e1, e2]
  rw [hz1, e3] at hfix
  have hc' := pinnedX_injective .G2 L g2r (mul_left_cancel hfix)
  have hζ1 : (ζ : L) ≠ 1 := fun h1 => by
    rw [show ζ = 1 from Units.ext h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  have hc0 : c = 0 := by
    have : ((ζ : L) - 1) * c = 0 := by rw [sub_mul, one_mul, hc', sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hζ1)
  rw [hz1, hc0, pinnedX_zero, mul_one]
  exact hh

end CFSG.GH74.GLS.Stage2.Bender.Thm1
