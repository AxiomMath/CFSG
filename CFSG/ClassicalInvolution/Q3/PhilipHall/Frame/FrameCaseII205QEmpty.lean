module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205QTransport
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205AzTri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

@[expose] def PairBarEmpty {A : Type} [Group A] (K₁ K₂ : Subgroup A) : Prop :=
  ∀ X : Subgroup A,
    ∀ J ∈ quotFamily (restrictFamily (AzTri.pairFam K₁ K₂) X) (classicalInvolutionOddCore ↥X),
      AEmpty (quotFamily (restrictFamily (AzTri.pairFam K₁ K₂) X)
        (classicalInvolutionOddCore ↥X)) J

section Hom

theorem exists_sectionQuot_hom' {C : Type} [Group C] [Finite C] (P : Subgroup C) :
    ∃ F : ↥(P.map (QuotientGroup.mk' (classicalInvolutionOddCore C))) →*
        (↥P ⧸ classicalInvolutionOddCore ↥P),
      Function.Surjective F ∧ Odd (Nat.card F.ker) ∧
        ∀ x : ↥P, ∀ hx : QuotientGroup.mk' (classicalInvolutionOddCore C) (x : C) ∈
          P.map (QuotientGroup.mk' (classicalInvolutionOddCore C)),
          F ⟨QuotientGroup.mk' (classicalInvolutionOddCore C) (x : C), hx⟩ =
            QuotientGroup.mk' (classicalInvolutionOddCore ↥P) x :=
  exists_sectionQuot_hom P

end Hom

section Bar

variable {A : Type} [Group A] [Finite A]

abbrev oqMk (A : Type) [Group A] : A →* A ⧸ classicalInvolutionOddCore A :=
  QuotientGroup.mk' (classicalInvolutionOddCore A)

theorem exists_mulEquiv_section (X : Subgroup A) :
    ∃ θ : (↥(X.map (oqMk A)) ⧸ classicalInvolutionOddCore ↥(X.map (oqMk A))) ≃*
        (↥X ⧸ classicalInvolutionOddCore ↥X),
      ∀ x : ↥X, ∀ hx : oqMk A (x : A) ∈ X.map (oqMk A),
        θ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(X.map (oqMk A)))
          ⟨oqMk A (x : A), hx⟩) = QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x := by
  obtain ⟨F, hFs, hFk, hFp⟩ := exists_sectionQuot_hom' X
  have hker : F.ker = classicalInvolutionOddCore ↥(X.map (oqMk A)) := by
    apply le_antisymm
    · exact CFSG.ComponentClassification.OddCore.maximal ↥(X.map (oqMk A)) F.ker inferInstance hFk
    · intro x hx
      have hnorm : ((classicalInvolutionOddCore ↥(X.map (oqMk A))).map F).Normal :=
        Subgroup.Normal.map inferInstance F hFs
      have hodd2 : Odd (Nat.card ↥((classicalInvolutionOddCore ↥(X.map (oqMk A))).map F)) :=
        (CFSG.ComponentClassification.OddCore.odd_card ↥(X.map (oqMk A))).of_dvd_nat
          (Subgroup.card_map_dvd _ F)
      have hle : (classicalInvolutionOddCore ↥(X.map (oqMk A))).map F ≤
          classicalInvolutionOddCore (↥X ⧸ classicalInvolutionOddCore ↥X) :=
        CFSG.ComponentClassification.OddCore.maximal (↥X ⧸ classicalInvolutionOddCore ↥X)
          _ hnorm hodd2
      have hbot : classicalInvolutionOddCore (↥X ⧸ classicalInvolutionOddCore ↥X) = ⊥ :=
        CFSG.ComponentClassification.OddCore.quotient_corefree X
      rw [hbot] at hle
      rw [MonoidHom.mem_ker]
      have := hle (Subgroup.mem_map_of_mem F hx)
      simpa using this
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective F hFs), fun x hx => ?_⟩
  exact hFp x hx

theorem pairBarEmpty_of_bar {Λ : Set (Subgroup A)} (hΛ : HypOmegaGen Λ) {K₁ K₂ : Subgroup A}
    (h₁ : K₁ ∈ Λ) (h₂ : K₂ ∈ Λ)
    (hA₁ : AEmpty (oddQuotientFamily Λ) (K₁.map (oqMk A)))
    (hA₂ : AEmpty (oddQuotientFamily Λ) (K₂.map (oqMk A))) :
    PairBarEmpty K₁ K₂ := by
  classical
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore A)) :=
    CFSG.ComponentClassification.OddCore.odd_card A
  have hΛb : HypOmegaGen (oddQuotientFamily Λ) := hypOmegaGen_quotFamily_odd hΛ hodd
  have hK₁b : K₁.map (oqMk A) ∈ oddQuotientFamily Λ := map_mem_quotFamily h₁
  have hK₂b : K₂.map (oqMk A) ∈ oddQuotientFamily Λ := map_mem_quotFamily h₂
  have hsubb : AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A)) ⊆ oddQuotientFamily Λ :=
    AzTri.pairFam_subset hΛb.conjInvariant hK₁b hK₂b
  have hΛp : HypOmegaGen (AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A))) :=
    TL4.hypOmegaGen_sub hΛb hsubb (AzTri.conjInvariant_pairFam _ _)
  have hA₁' : AEmpty (AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A))) (K₁.map (oqMk A)) :=
    Thm4Twin.aEmpty_sub hΛb hsubb hA₁
  have hA₂' : AEmpty (AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A))) (K₂.map (oqMk A)) :=
    Thm4Twin.aEmpty_sub hΛb hsubb hA₂
  have hAall : ∀ L ∈ AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A)),
      AEmpty (AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A))) L := by
    rintro L ⟨y, rfl | rfl⟩
    · exact aEmpty_conj hΛp.conjInvariant hA₁' y
    · exact aEmpty_conj hΛp.conjInvariant hA₂' y
  intro X J hJ
  have hΛX' := hypOmegaGen_restrict hΛp (X.map (oqMk A))
  have hodd' : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(X.map (oqMk A)))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(X.map (oqMk A))
  have hres : ∀ L ∈ restrictFamily (AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A)))
      (X.map (oqMk A)), AEmpty (restrictFamily (AzTri.pairFam (K₁.map (oqMk A))
        (K₂.map (oqMk A))) (X.map (oqMk A))) L := by
    rintro _ ⟨L₀, hL₀, hL₀X, rfl⟩
    exact Thm4Twin.aEmpty_restrict hΛp (subset_refl _) hL₀X (hAall L₀ hL₀)
  have hΔ := hypOmegaGen_quotFamily_odd hΛX' hodd'
  have hAq := TwinADescent2.aEmpty_quotFamily_gen hΛX' hΔ hodd' hres
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_section X
  have hmemG : ∀ L₀ ∈ AzTri.pairFam K₁ K₂, L₀ ≤ X →
      ((L₀.map (oqMk A)).subgroupOf (X.map (oqMk A))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(X.map (oqMk A)))) ∈
          quotFamily (restrictFamily (AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A)))
            (X.map (oqMk A))) (classicalInvolutionOddCore ↥(X.map (oqMk A))) := by
    intro L₀ hL₀ hL₀X
    have hLb : L₀.map (oqMk A) ∈ AzTri.pairFam (K₁.map (oqMk A)) (K₂.map (oqMk A)) := by
      obtain ⟨y, rfl | rfl⟩ := hL₀
      · exact ⟨oqMk A y, Or.inl (AscQuot.map_conjSub (oqMk A) y K₁)⟩
      · exact ⟨oqMk A y, Or.inr (AscQuot.map_conjSub (oqMk A) y K₂)⟩
    exact ⟨_, ⟨L₀.map (oqMk A), hLb, Subgroup.map_mono hL₀X, rfl⟩, rfl⟩
  have hkey : ∀ L₀ : Subgroup A, L₀ ≤ X →
      ((L₀.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))).map
          θ.symm.toMonoidHom =
        ((L₀.map (oqMk A)).subgroupOf (X.map (oqMk A))).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(X.map (oqMk A)))) := by
    intro L₀ hL₀X
    let ψ : ↥X →* ↥(X.map (oqMk A)) :=
      ((oqMk A).comp X.subtype).codRestrict (X.map (oqMk A))
        (fun x => Subgroup.mem_map_of_mem _ x.2)
    have hM' : (L₀.map (oqMk A)).subgroupOf (X.map (oqMk A)) = (L₀.subgroupOf X).map ψ := by
      ext x'
      constructor
      · intro hx'
        obtain ⟨l, hl, hlx⟩ := Subgroup.mem_subgroupOf.mp hx'
        exact ⟨⟨l, hL₀X hl⟩, Subgroup.mem_subgroupOf.mpr hl, Subtype.ext hlx⟩
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    have hcomp : θ.symm.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) =
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(X.map (oqMk A)))).comp ψ := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [MulEquiv.symm_apply_eq]
      exact (hθ x _).symm
    rw [hM', Subgroup.map_map, Subgroup.map_map, hcomp]
  obtain ⟨_, ⟨L₀, hL₀, hL₀X, rfl⟩, rfl⟩ := hJ
  refine QTransport.aEmpty_of_mapFam_sub θ.symm hΔ ?_ ?_
  · rintro _ ⟨_, ⟨_, ⟨L₁, hL₁, hL₁X, rfl⟩, rfl⟩, rfl⟩
    rw [hkey L₁ hL₁X]
    exact hmemG L₁ hL₁ hL₁X
  · rw [hkey L₀ hL₀X]
    exact hAq _ (hmemG L₀ hL₀ hL₀X)

end Bar

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
