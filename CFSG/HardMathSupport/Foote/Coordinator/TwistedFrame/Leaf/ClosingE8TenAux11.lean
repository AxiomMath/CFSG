module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux10
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData3
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux8

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.ModelFacts.Levi

set_option linter.unusedSectionVars false


@[expose] def νW : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd νWord

theorem νW_smul (γ : Fin Tag.E8.rank → ℤ) : νW • γ = νm.mulVec γ :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 νWord γ

theorem νW_theta : νW • highRoot Tag.E8 = theta2 := by rw [νW_smul, νm_theta]

@[expose] def w₂ : WeylGroup Tag.E8 := νW⁻¹ * (w8 * νW)

theorem w₂_smul (γ : Fin Tag.E8.rank → ℤ) : w₂ • γ = wm.mulVec γ := by
  apply MulAction.injective νW
  have h1 : νW • (w₂ • γ) = w8 • (νW • γ) := by
    unfold w₂
    rw [mul_smul, smul_inv_smul, mul_smul]
  show νW • (w₂ • γ) = νW • (wm.mulVec γ)
  rw [h1, w_smul, νW_smul, νW_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, wm_νm]

section Pos

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
  (H : Subgroup (ModGL Tag.E8 K))

@[expose] def gE : ModGL Tag.E8 D.L := D.g

@[expose] def cL : ModGL Tag.E8 D.L := canonicalRep (coxeterSystem Tag.E8) D.L νW

theorem Frob_canonicalRep (Fr : D.L →+* D.L) (hbij : Function.Bijective Fr) (w : WeylGroup Tag.E8) :
    Frob Fr (canonicalRep (coxeterSystem Tag.E8) D.L w) =
      canonicalRep (coxeterSystem Tag.E8) D.L w :=
  entrywise_canonicalRep (RingEquiv.ofBijective Fr hbij) w

@[expose] def toSetup2 : Setup K D.L where
  Fr := D.Fr
  hFr := D.hFr
  hbij := (toSetup D H).hbij
  h := gE D * cL D
  n := (cL D)⁻¹ * (canonicalRep (coxeterSystem Tag.E8) D.L w8 * cL D)
  hh := mul_mem (g_mem_adjointGroup' D) (canonicalRep_mem_adjointGroup _ _ _)
  hlang := by
    have hc : Frob D.Fr (cL D) = cL D := Frob_canonicalRep D D.Fr (toSetup D H).hbij νW
    have hl : Frob D.Fr (gE D) = gE D * canonicalRep (coxeterSystem Tag.E8) D.L w8 := D.lang
    rw [map_mul, hc, hl]
    group
  w := w₂
  sg := fun β => sgn νW (νW⁻¹ • ((w8 * νW) • β)) * (sgn w8 (νW • β) * sgn νW β)
  hm := ((mono_canonicalRep νW).inv).mul ((mono_canonicalRep w8).mul (mono_canonicalRep νW))
  hθ := by
    rw [w₂_smul]
    exact wm_theta
  hD := fun μ hμ => by
    rw [w₂_smul]
    exact mem_deg1Roots.1 (wm_deg1 μ (mem_deg1Roots.2 hμ))
  H := H

theorem toSetup2_hw (γ : Fin Tag.E8.rank → ℤ) : (toSetup2 D H).w • γ = wm.mulVec γ := w₂_smul γ

@[expose] def Xc (S : Set (Fin Tag.E8.rank → ℤ)) : Subgroup (ModGL Tag.E8 D.L) :=
  (rootSpan Tag.E8 D.L S).comap (MulAut.conj (cL D)).toMonoidHom

theorem mem_Xc {S : Set (Fin Tag.E8.rank → ℤ)} {x : ModGL Tag.E8 D.L} :
    x ∈ Xc D S ↔ cL D * x * (cL D)⁻¹ ∈ rootSpan Tag.E8 D.L S := Iff.rfl

theorem xlink2 (S : Set (Fin Tag.E8.rank → ℤ)) (hH : D.frame S ≤ H) :
    (toSetup2 D H).XLink (Xc D S) := by
  intro l₀ hl₀ hx
  rw [mem_Xc] at hx
  refine hH ((mem_frame_iff' D S l₀).2 ⟨hl₀, ?_⟩)
  have e : cL D * ((gE D * cL D)⁻¹ * baseChangeGL (algebraMap K D.L) l₀ * (gE D * cL D)) *
      (cL D)⁻¹ = (gE D)⁻¹ * baseChangeGL (algebraMap K D.L) l₀ * gE D := by group
  change (gE D)⁻¹ * baseChangeGL (algebraMap K D.L) l₀ * gE D ∈ rootSpan Tag.E8 D.L S
  rw [← e]
  exact hx

theorem pinnedX_mem_Xc {S : Set (Fin Tag.E8.rank → ℤ)} {γ : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot Tag.E8 γ) (hS : νW • γ ∈ S) (t : D.L) : pinnedX Tag.E8 D.L γ t ∈ Xc D S := by
  rw [mem_Xc]
  obtain ⟨-, hc⟩ := mono_canonicalRep (L := D.L) νW γ hγ
  have : cL D * pinnedX Tag.E8 D.L γ t * (cL D)⁻¹ = pinnedX Tag.E8 D.L (νW • γ) (sgn νW γ * t) :=
    hc t
  rw [this]
  exact pinnedX_mem_rootSpan hS _

theorem listA_mem_Xc : ∀ γ ∈ listA, ∀ t : D.L,
    pinnedX Tag.E8 D.L γ t ∈ Xc D TwClass.e8Ten.S₁ := by
  intro γ hγ t
  have hr := (listA_data γ hγ).1
  have h := νm_listA γ hγ
  refine pinnedX_mem_Xc D (mem_rootFinset.1 hr) ?_ t
  rw [νW_smul]
  exact ⟨mem_rootFinset.1 h.1, fun α hα => h.2 α (mem_rootFinset.2 hα.1) hα.2⟩

theorem listB_mem_Xc : ∀ γ ∈ listB, ∀ t : D.L,
    pinnedX Tag.E8 D.L γ t ∈ Xc D TwClass.e8Ten.S₂ := by
  intro γ hγ t
  have hr := (listB_data γ hγ).1
  have h := νm_listB γ hγ
  refine pinnedX_mem_Xc D (mem_rootFinset.1 hr) ?_ t
  rw [νW_smul]
  exact ⟨mem_rootFinset.1 h.1, h.2⟩

theorem Uθ_le_Xc : ∀ u ∈ Heis.Uθ Tag.E8 D.L, u ∈ Xc D TwClass.e8Ten.S₂ := by
  intro u hu
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hu
  refine pinnedX_mem_Xc D (isRoot_highRoot _) ?_ t
  rw [νW_theta]
  exact ⟨mem_rootFinset.1 theta2_S₂.1, theta2_S₂.2⟩

theorem Uneg_le_Xc : ∀ u ∈ Heis.Uneg Tag.E8 D.L, u ∈ Xc D TwClass.e8Ten.S₂ := by
  intro u hu
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hu
  refine pinnedX_mem_Xc D (isRoot_neg_highRoot _) ?_ t
  have : νW • (-highRoot Tag.E8) = -theta2 := by rw [νW_smul, νm_negTheta]
  rw [this]
  exact ⟨mem_rootFinset.1 neg_theta2_S₂.1, neg_theta2_S₂.2⟩

theorem hker₁ (hH1 : D.frame TwClass.e8Ten.S₁ ≤ H) :
    ∀ l ∈ Qrat (K := K) (toSetup D H).h, l ∈ adjointGroup Tag.E8 K →
      Cc (toSetup D H).h l = 0 → l ∈ H := by
  intro l hl hladj h0
  have hQ : (toSetup D H).h⁻¹ * baseChangeGL (algebraMap K D.L) l * (toSetup D H).h ∈
      Qθ Tag.E8 D.L := hl
  have hU := ((heisCoord_spec Tag.E8 D.L).eq_zero_iff _ hQ).1 h0
  exact xlink D H _ hH1 l hladj
    (rootSubgroup_le_rootSpan_of_mem (TwBasicAux.highRoot_mem_S₁ TwClass.e8Ten) hU)

theorem hker₂ (hH2 : D.frame TwClass.e8Ten.S₂ ≤ H) :
    ∀ l ∈ Qrat (K := K) (toSetup2 D H).h, l ∈ adjointGroup Tag.E8 K →
      Cc (toSetup2 D H).h l = 0 → l ∈ H := by
  intro l hl hladj h0
  have hQ : (toSetup2 D H).h⁻¹ * baseChangeGL (algebraMap K D.L) l * (toSetup2 D H).h ∈
      Qθ Tag.E8 D.L := hl
  have hU := ((heisCoord_spec Tag.E8 D.L).eq_zero_iff _ hQ).1 h0
  exact xlink2 D H _ hH2 l hladj (Uθ_le_Xc D _ hU)

end Pos

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
