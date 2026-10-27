module

public import CFSG.FeitThompson.Representations.CoherentExtensionNonrealConjPairs
public import CFSG.FeitThompson.Representations.IntegralRemainderOneCharacterExtension
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L G : Type*} [Group L] [Group G] {X Y : Set (L → ℂ)}

def restrictBaseline {S T : Set (L → ℂ)} (hST : S ⊆ T)
    (τ : charSpanZero T →+ virtualChars G) : charSpanZero S →+ virtualChars G :=
  τ.comp (Submodule.inclusion (FeitExtension.charSpanZero_mono hST)).toAddMonoidHom

theorem restrictBaseline_apply {S T : Set (L → ℂ)} (hST : S ⊆ T)
    (τ : charSpanZero T →+ virtualChars G) (f : charSpanZero S) :
    restrictBaseline hST τ f = τ (Submodule.inclusion (FeitExtension.charSpanZero_mono hST) f) :=
  (rfl)

theorem restrictBaseline_coe_mk {S T : Set (L → ℂ)} (hST : S ⊆ T)
    (τ : charSpanZero T →+ virtualChars G) {v : L → ℂ} (hv : v ∈ charSpanZero S)
    (hv' : v ∈ charSpanZero T) :
    (restrictBaseline hST τ ⟨v, hv⟩ : G → ℂ) = (τ ⟨v, hv'⟩ : G → ℂ) := by
  have h : Submodule.inclusion (FeitExtension.charSpanZero_mono hST) ⟨v, hv⟩ = ⟨v, hv'⟩ :=
    Subtype.ext (by simp)
  rw [restrictBaseline_apply, h]

omit [Group L] in
theorem star_mem_union (hXstar : ∀ χ ∈ X, star χ ∈ X) (hYstar : ∀ χ ∈ Y, star χ ∈ Y) :
    ∀ χ ∈ X ∪ Y, star χ ∈ X ∪ Y := by
  rintro χ (h | h)
  · exact Or.inl (hXstar χ h)
  · exact Or.inr (hYstar χ h)

omit [Group L] in
theorem two_le_ncard_of_star_ne {S : Set (L → ℂ)} (hSfin : S.Finite) (hSne : S.Nonempty)
    (hSstar : ∀ χ ∈ S, star χ ∈ S) (hSnr : ∀ χ ∈ S, star χ ≠ χ) : 2 ≤ S.ncard := by
  obtain ⟨χ, hχ⟩ := hSne
  have hsub : ({χ, star χ} : Set (L → ℂ)) ⊆ S := by
    rintro y (rfl | rfl)
    · exact hχ
    · exact hSstar χ hχ
  have := Set.ncard_le_ncard hsub hSfin
  rwa [Set.ncard_pair (Ne.symm (hSnr χ hχ))] at this

section Main

variable [Fintype L] [Fintype G]

open scoped Classical in
theorem cfInner_coherentVal_coherentVal_eq_zero_of_disjoint
    (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L) (hXY : Disjoint X Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hYstar : ∀ χ ∈ Y, star χ ∈ Y)
    (hXnr : ∀ χ ∈ X, star χ ≠ χ) (hYnr : ∀ χ ∈ Y, star χ ≠ χ)
    {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτ1 : ∀ f : charSpanZero (X ∪ Y), (τ f : G → ℂ) 1 = 0)
    (hτiso : ∀ f g : charSpanZero (X ∪ Y),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτstar : ∀ f : charSpanZero (X ∪ Y),
      (τ (starCharSpanZero (star_mem_union hXstar hYstar) f) : G → ℂ) = star ((τ f : G → ℂ)))
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    (ξ : X) (η : Y) :
    cfInner (coherentVal νX ξ) (coherentVal νY η) = 0 := by
  set hUstar := star_mem_union hXstar hYstar with hUstardef
  have hU : X ∪ Y ⊆ Irr L := Set.union_subset hX hY
  have hX2 : 2 ≤ X.ncard := two_le_ncard_of_star_ne (finite_Irr.subset hX) hXne hXstar hXnr
  have hY2 : 2 ≤ Y.ncard := two_le_ncard_of_star_ne (finite_Irr.subset hY) hYne hYstar hYnr
  have hτX1 : ∀ f : charSpanZero X,
      (restrictBaseline Set.subset_union_left τ f : G → ℂ) 1 = 0 := fun f => hτ1 _
  have hτY1 : ∀ f : charSpanZero Y,
      (restrictBaseline Set.subset_union_right τ f : G → ℂ) 1 = 0 := fun f => hτ1 _
  have hτXstar : ∀ f : charSpanZero X,
      (restrictBaseline Set.subset_union_left τ (starCharSpanZero hXstar f) : G → ℂ)
        = star ((restrictBaseline Set.subset_union_left τ f : G → ℂ)) := by
    intro f
    have h : Submodule.inclusion
        (FeitExtension.charSpanZero_mono (Set.subset_union_left (s := X) (t := Y)))
          (starCharSpanZero hXstar f)
        = starCharSpanZero hUstar (Submodule.inclusion
          (FeitExtension.charSpanZero_mono (Set.subset_union_left (s := X) (t := Y))) f) :=
      Subtype.ext (by simp)
    rw [restrictBaseline_apply, h, hτstar, restrictBaseline_apply]
  have hτYstar : ∀ f : charSpanZero Y,
      (restrictBaseline Set.subset_union_right τ (starCharSpanZero hYstar f) : G → ℂ)
        = star ((restrictBaseline Set.subset_union_right τ f : G → ℂ)) := by
    intro f
    have h : Submodule.inclusion
        (FeitExtension.charSpanZero_mono (Set.subset_union_right (s := X) (t := Y)))
          (starCharSpanZero hYstar f)
        = starCharSpanZero hUstar (Submodule.inclusion
          (FeitExtension.charSpanZero_mono (Set.subset_union_right (s := X) (t := Y))) f) :=
      Subtype.ext (by simp)
    rw [restrictBaseline_apply, h, hτstar, restrictBaseline_apply]
  obtain ⟨ε, hε, a, -, haIrr, haeq, hanr, hastar⟩ :=
    exists_sign_nonreal_root_of_isCoherentWith hX hX2 hXstar hXnr hτX1 hτXstar hνX
  obtain ⟨δ, hδ, b, -, hbIrr, hbeq, hbnr, hbstar⟩ :=
    exists_sign_nonreal_root_of_isCoherentWith hY hY2 hYstar hYnr hτY1 hτYstar hνY
  have hne : a ξ ≠ b η := by
    intro hab
    set fX : charSpanZero (X ∪ Y) := ⟨(ξ : L → ℂ) - star (ξ : L → ℂ),
      sub_star_mem_charSpanZero hU hUstar (Or.inl ξ.2)⟩ with hfXdef
    set fY : charSpanZero (X ∪ Y) := ⟨(η : L → ℂ) - star (η : L → ℂ),
      sub_star_mem_charSpanZero hU hUstar (Or.inr η.2)⟩ with hfYdef
    have hτfX : (τ fX : G → ℂ) = ε • a ξ - ε • star (a ξ) := by
      have h := coherentVal_sub_coherentVal_starElem hX hXstar hνX ξ
      rw [haeq ξ, haeq (starElem hXstar ξ), hastar ξ,
        restrictBaseline_coe_mk _ _ _ (sub_star_mem_charSpanZero hU hUstar (Or.inl ξ.2))] at h
      exact h.symm
    have hτfY : (τ fY : G → ℂ) = δ • b η - δ • star (b η) := by
      have h := coherentVal_sub_coherentVal_starElem hY hYstar hνY η
      rw [hbeq η, hbeq (starElem hYstar η), hbstar η,
        restrictBaseline_coe_mk _ _ _ (sub_star_mem_charSpanZero hU hUstar (Or.inr η.2))] at h
      exact h.symm
    have hzero : cfInner (τ fX : G → ℂ) (τ fY : G → ℂ) = 0 := by
      rw [hτiso]
      have h1 : ∀ u ∈ X, ∀ v ∈ Y, cfInner u v = 0 := fun u hu v hv =>
        cfInner_eq_zero_of_mem_Irr (hX hu) (hY hv)
          (fun h => Set.disjoint_left.1 hXY hu (by rw [h]; exact hv))
      change cfInner ((ξ : L → ℂ) - star (ξ : L → ℂ)) ((η : L → ℂ) - star (η : L → ℂ)) = 0
      rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
        h1 _ ξ.2 _ η.2, h1 _ ξ.2 _ (hYstar _ η.2), h1 _ (hXstar _ ξ.2) _ η.2,
        h1 _ (hXstar _ ξ.2) _ (hYstar _ η.2)]
      ring
    rw [hτfX, hτfY, hab, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
      cfInner_smul_smul_of_mem_Irr _ _ (hbIrr η) (hbIrr η),
      cfInner_smul_smul_of_mem_Irr _ _ (hbIrr η) (star_mem_Irr (hbIrr η)),
      cfInner_smul_smul_of_mem_Irr _ _ (star_mem_Irr (hbIrr η)) (hbIrr η),
      cfInner_smul_smul_of_mem_Irr _ _ (star_mem_Irr (hbIrr η)) (star_mem_Irr (hbIrr η)),
      if_pos rfl, if_pos rfl, if_neg (Ne.symm (hbnr η)), if_neg (hbnr η)] at hzero
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num at hzero
  rw [haeq ξ, hbeq η, cfInner_smul_smul_of_mem_Irr _ _ (haIrr ξ) (hbIrr η), if_neg hne]

theorem cfInner_apply_apply_eq_zero_of_disjoint
    (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L) (hXY : Disjoint X Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hYstar : ∀ χ ∈ Y, star χ ∈ Y)
    (hXnr : ∀ χ ∈ X, star χ ≠ χ) (hYnr : ∀ χ ∈ Y, star χ ≠ χ)
    {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτ1 : ∀ f : charSpanZero (X ∪ Y), (τ f : G → ℂ) 1 = 0)
    (hτiso : ∀ f g : charSpanZero (X ∪ Y),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτstar : ∀ f : charSpanZero (X ∪ Y),
      (τ (starCharSpanZero (star_mem_union hXstar hYstar) f) : G → ℂ) = star ((τ f : G → ℂ)))
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    {ξ η : L → ℂ} (hξ : ξ ∈ X) (hη : η ∈ Y) :
    cfInner (νX ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ)
      (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ) = 0 := by
  have h := cfInner_coherentVal_coherentVal_eq_zero_of_disjoint hX hY hXY hXne hYne hXstar hYstar
    hXnr hYnr hτ1 hτiso hτstar hνX hνY ⟨ξ, hξ⟩ ⟨η, hη⟩
  rwa [coherentVal_apply, coherentVal_apply] at h

end Main

end CFSG.FeitThompson
