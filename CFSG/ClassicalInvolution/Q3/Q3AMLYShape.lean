module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYEdge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Shape


variable {G : Type} [Group G] [Finite G]

theorem layerFam_inClass3 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) : InClass3 (layerFam Ω M a) :=
  inClass3_oddQuotient (secData3_nbrCoreFam h hint hM ha).inClass3

theorem layer_shape [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) :
    (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∈
        layerFam Ω K z ∨
      LayerL3 Ω K z ∨ LayerM11 Ω K z ∨ LayerS3 Ω K z := by
  classical
  have hstd := h.std
  have hK : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  by_cases hTop : (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∈ layerFam Ω K z
  · exact Or.inl hTop
  right
  obtain ⟨ι, hfin, ⟨D₃⟩⟩ := nbrLayer_lieSystem h hint hK hz
  have hno := layerFam_noCommute h hint hN
  have hcl3 := layerFam_inClass3 h hint hK hz
  have hconj : ConjInvariant (layerFam Ω K z) := hcl3.conjInvariant
  obtain ⟨L₀, hL₀⟩ := hcl3.nonempty
  obtain ⟨i₀, -⟩ := D₃.fundamental L₀ hL₀
  have hsub : Subsingleton ι := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    obtain ⟨R', -, hR⟩ := D₃.meets i
    obtain ⟨S', -, hS⟩ := D₃.meets j
    refine hno _ hR _ hS ?_
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact D₃.commute i j hij a b
  have hone : ∀ i : ι, i = i₀ := fun i => Subsingleton.elim i i₀
  let D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) (layerFam Ω K z) :=
    { kind := fun _ => D₃.kind i₀
      valid := fun _ => by
        rcases D₃.valid i₀ with ⟨t, n, ht, hadm, hc⟩ | hc | hc
        · exact Or.inl ⟨t, n, 1, ht, hadm, Or.inl rfl, hc⟩
        · exact Or.inr ⟨by norm_num, Or.inl hc⟩
        · exact Or.inr ⟨by norm_num, Or.inr hc⟩
      hom := fun _ => D₃.hom i₀
      ker_le_center := fun _ => D₃.ker_le_center i₀
      commute := fun i j hij => absurd (Subsingleton.elim i j) hij
      generate := by
        rw [← D₃.generate]
        refine le_antisymm (iSup_le fun _ => le_iSup (fun j => (D₃.hom j).range) i₀)
          (iSup_le fun j => ?_)
        rw [hone j]
        exact le_iSup (fun _ : Fin 1 => (D₃.hom i₀).range) 0
      fundamental := fun L hL => by
        obtain ⟨i, R', hR, e⟩ := D₃.fundamental L hL
        obtain rfl := hone i
        exact ⟨0, R', hR, e⟩
      meets := fun _ => D₃.meets i₀
      card_eq := fun _ => D₃.card_eq }
  have hΦne : (layerFam Ω K z).Nonempty := ⟨L₀, hL₀⟩
  rcases Q3T8.tag_cases_of_sysData D hconj hno hΦne hTop with ⟨t', k, htag, hc⟩ | hc
  · obtain ⟨e, he, hft, hadm, hkind⟩ := hc
    have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩ <;> omega
    subst he1
    have hk : D₃.kind i₀ = CompData.model t' k := hkind
    rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ι, hfin, D₃, i₀, hone, hk⟩
    · exact Or.inr (Or.inr ⟨ι, hfin, D₃, i₀, hone, Or.inl hk⟩)
    · exact Or.inr (Or.inr ⟨ι, hfin, D₃, i₀, hone, Or.inr (Or.inl hk)⟩)
    · exact Or.inr (Or.inr ⟨ι, hfin, D₃, i₀, hone, Or.inr (Or.inr hk)⟩)
  · exact Or.inr (Or.inl ⟨ι, hfin, D₃, i₀, hone, hc⟩)

end Shape

end CFSG.ClassicalInvolution.Q3.Q3AM
