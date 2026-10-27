module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC3
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.R10

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.G2D4Models
  CFSG.Assembly.LowTwoRank

variable {Y : Type} [Group Y] [Finite Y] {p f n : ℕ} [Fact p.Prime]


theorem all_mem_compMembers (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Λ : Set (Subgroup Y)}
    (hΛ : HypOmegaMod p f Λ)
    (htw : ∀ M₁ ∈ Λ, ∀ M₂ ∈ omegaNbr Λ M₁, M₂ ∈ twinSet Λ M₁)
    (D : OmegaLie p f (oddQuotientFamily Λ)) {i : Fin D.card}
    (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {K : Subgroup Y} (hK : K ∈ Λ)
    (hKmem : K.map (oddQuot Y) ∈ compMembers D i) :
    ∀ M ∈ oddQuotientFamily Λ, M ∈ compMembers D i := by
  have hΦ : HypOmegaMod p f (oddQuotientFamily Λ) :=
    oddQuotHyp p f hp2 hq Y Λ hΛ (classicalInvolutionOddCore Y)
      (CFSG.ComponentClassification.OddCore.odd_card Y)
  intro M hMΦ
  by_contra hMi
  have hcomm := commutes_of_not_mem_compMembers D hMΦ hMi hKmem
  have hne : M ≠ K.map (oddQuot Y) := fun h => hMi (h ▸ hKmem)
  have hnbr := mem_omegaNbr_of_commutes hMΦ hne hcomm
  obtain ⟨M₀, hM₀, rfl⟩ := hMΦ
  obtain ⟨n, hnN, hn⟩ := exists_conj_omegaNbr hp2 hq hΛ hΦ
    (CFSG.ComponentClassification.OddCore.odd_card Y) hK hM₀ hnbr
  have hKn : conjSub n K ∈ Λ := hΛ.conjInvariant n K hK
  obtain ⟨-, w, hw1, hw2⟩ := htw _ hKn _ hn
  have hπn : oddQuot Y n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
  have himg : (conjSub n K).map (oddQuot Y) = K.map (oddQuot Y) := by
    rw [AscQuot.map_conjSub, hπn, conjSub_one]
  have h1 : IsUniqueInvolution (K.map (oddQuot Y)) (oddQuot Y w) := by
    rw [← himg]
    exact isUniqueInvolution_map_mk_of_odd (odd_natCard_oddCore_inf _) hw1
  have h2 : IsUniqueInvolution (M₀.map (oddQuot Y)) (oddQuot Y w) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_oddCore_inf _) hw2
  exact hMi (twin_mem_compMembers hp2 D hi hKmem
    ⟨mem_oddQuotientFamily hM₀, oddQuot Y w, h1, h2⟩)


theorem section_of_all_mem {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hp2 : p ≠ 2) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {i : Fin D.card}
    (hG2 : D.tag i = .G2) (hall : ∀ M ∈ Φ, M ∈ compMembers D i) :
    D.card = 1 ∧ (D.hom i).range = omegaGen Φ ∧ ((D.hom i).range).Normal ∧
      IsSimpleGroup ↥((D.hom i).range) ∧
      Nonempty (Ih8Model p f (restrictFamily Φ ((D.hom i).range)) (D.tag i) (D.rank i)
        (D.exp i)) := by
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inl hG2
  have hcard : D.card = 1 := D.card_eq_one_of_all_le hΦ (i₀ := i) (fun L hL => by
    obtain ⟨R, -, rfl⟩ := hall L hL
    exact Subgroup.map_le_range _ _)
  have hcompEq : (D.hom i).range = omegaGen Φ := by
    refine le_antisymm (D.comp_le_omegaGen i) ?_
    rw [← D.iSup_comp]
    exact iSup_le fun j => by rw [D.index_eq hcard j i]; exact le_rfl
  have hnorm : ((D.hom i).range).Normal := by
    rw [hcompEq]
    exact omegaGen_normal hΦ.conjInvariant
  have hinj := hom_injective_of_g2d4 hp2 D hi
  have hsimple : IsSimpleGroup ↥((D.hom i).range) :=
    haveI := isSimpleGroup_model_of_g2d4 hp2 (D.admissible i) hi
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective hinj).symm
  refine ⟨hcard, hcompEq, hnorm, hsimple, ⟨?_⟩⟩
  exact
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := (D.hom i).rangeRestrict
      ker_le_center := by
        rw [MonoidHom.ker_rangeRestrict]
        exact D.ker_le_center i
      surj := (D.hom i).rangeRestrict_surjective
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := by
        intro L
        rw [mem_restrictFamily_iff]
        constructor
        · intro hL
          obtain ⟨R, hR, hLR⟩ := (D.mem_iff_exists_cls hcard i).mp hL
          refine ⟨R, hR, Subgroup.map_injective ((D.hom i).range).subtype_injective ?_⟩
          rw [hLR, Subgroup.map_map]
          rfl
        · rintro ⟨R, hR, rfl⟩
          have h2 : (R.map (D.hom i).rangeRestrict).map ((D.hom i).range).subtype =
              R.map (D.hom i) := by
            rw [Subgroup.map_map]
            rfl
          rw [h2]
          exact hR.2
      cls_conj := fun R hR g => D.cls_conj hΦ.conjInvariant i hR g }


theorem map_map_conjNormal {X : Type} [Group X] (E : Subgroup X) [E.Normal] (g : X)
    (L : Subgroup ↥E) :
    (L.map (MulAut.conjNormal g : MulAut ↥E).toMonoidHom).map E.subtype =
      conjSub g (L.map E.subtype) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isUniqueInvolution_map_of_injective {A B : Type} [Group A] [Group B] {ψ : A →* B}
    (hψ : Function.Injective ψ) {L : Subgroup A} {c : A} (h : IsUniqueInvolution L c) :
    IsUniqueInvolution (L.map ψ) (ψ c) where
  mem := Subgroup.mem_map_of_mem ψ h.mem
  ne_one := fun h1 => h.ne_one (hψ (h1.trans (map_one ψ).symm))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    have hy2' : y * y = 1 := hψ (by rw [map_mul, hy2, map_one])
    rcases h.unique y hy hy2' with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])


end CFSG.ClassicalInvolution.Asc77.R10
