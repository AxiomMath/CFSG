module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenDescent

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExcTwo

section Conj

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_conj_rootElt (F : RootOperatorFamily τ) (a : Fin τ.rank → Kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : K) :
    rootDiagUnit τ a * F.eltUnit K ⟨γ, hγ⟩ t * (rootDiagUnit τ a)⁻¹ =
      F.eltUnit K ⟨γ, hγ⟩ (((rootChar a γ : Kˣ) : K) * t) := by
  have hs := F.pinnedFamilySign_mul_self K γ
  have e1 : ∀ s : K, F.eltUnit K ⟨γ, hγ⟩ s =
      pinnedX τ K γ ((F.pinnedFamilySign γ : K) * s) := by
    intro s
    rw [F.pinnedX_eq_eltUnit K hγ, ← mul_assoc, hs, one_mul]
  rw [e1, e1, rootDiagUnit_conj_pinnedX a hγ]
  congr 1
  ring

theorem rootDiagAut_eltElement {K : Type} [Field K] (a : Fin Tag.E7.rank → Kˣ)
    {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot Tag.E7 δ) (c : K) :
    rootDiagAut Tag.E7 K a ((rootOperatorFamily Tag.E7).eltElement ⟨δ, hδ⟩ c) =
      (rootOperatorFamily Tag.E7).eltElement ⟨δ, hδ⟩ (((rootChar a δ : Kˣ) : K) * c) := by
  refine Subtype.ext ?_
  rw [coe_rootDiagAut, RootOperatorFamily.coe_eltElement, RootOperatorFamily.coe_eltElement]
  exact rootDiagUnit_conj_rootElt (rootOperatorFamily Tag.E7) a hδ c

end Conj

section Frame

theorem rootGroup_le_comap_rootDiagAut {K : Type} [Field K] (a : Fin Tag.E7.rank → Kˣ)
    {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot Tag.E7 δ)
    (hle : CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily Tag.E7) K δ ≤
      e7FrameGroup K) :
    CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily Tag.E7) K δ ≤
      (e7FrameGroup K).comap (rootDiagAut Tag.E7 K a).toMonoidHom := by
  have hF : CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily Tag.E7) K δ =
      (rootOperatorFamily Tag.E7).rootSubgroup K ⟨δ, hδ⟩ := by
    unfold CFSG.LieType.Steinberg.Adjoint.rootGroup
    exact dif_pos hδ
  intro x hx
  rw [hF] at hx
  obtain ⟨c, rfl⟩ := (rootOperatorFamily Tag.E7).mem_rootSubgroup.1 hx
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, rootDiagAut_eltElement a hδ c]
  refine hle ?_
  rw [hF]
  exact (rootOperatorFamily Tag.E7).eltElement_mem_rootSubgroup ⟨δ, hδ⟩ _

theorem e7FrameGroup_le_comap_rootDiagAut {K : Type} [Field K] (a : Fin Tag.E7.rank → Kˣ) :
    e7FrameGroup K ≤ (e7FrameGroup K).comap (rootDiagAut Tag.E7 K a).toMonoidHom := by
  show (⨆ i, rootPairE7 K (frameE7Root i)) ≤ _
  refine iSup_le fun i => sup_le ?_ ?_
  · exact rootGroup_le_comap_rootDiagAut a (e7Frame_isRoot i)
      (le_sup_left.trans (le_iSup (fun j => rootPairE7 K (frameE7Root j)) i))
  · exact rootGroup_le_comap_rootDiagAut a (IsRoot.neg (e7Frame_isRoot i))
      (le_sup_right.trans (le_iSup (fun j => rootPairE7 K (frameE7Root j)) i))

end Frame

theorem e7TorusNormalizesFrame_holds : E7TorusNormalizesFrame := by
  unfold E7TorusNormalizesFrame
  intro K _ _ a y hy
  exact ⟨rootDiagAut Tag.E7 K a y, Subgroup.mem_comap.1 (e7FrameGroup_le_comap_rootDiagAut a hy),
    coe_rootDiagAut a y⟩

end CFSG.LieType.SeitzGeneration.ExcHigh

end
