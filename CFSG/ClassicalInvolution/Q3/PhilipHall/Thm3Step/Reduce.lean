module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf17Inst
public import CFSG.ClassicalInvolution.Q3.TL4SepMin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Aux

variable {Y : Type} [Group Y] [Finite Y]

theorem concl_restrict_of_below {m : ℕ} (hb : Thm3RBelowG m) (hY : Nat.card Y = m)
    (hO : classicalInvolutionOddCore Y = ⊥) {Φ : Set (Subgroup Y)} (hΦ : TypeRHyp Φ)
    {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) (hgen : omegaGen Φ ≠ ⊤) :
    Thm3RConclG (restrictFamily Φ (omegaGen Φ)) (K.subgroupOf (omegaGen Φ)) := by
  have hKH : K ≤ omegaGen Φ := le_omegaGen hK
  have hHn : (omegaGen Φ).Normal := omegaGen_normal hΦ.hyp.conjInvariant
  have hOH : classicalInvolutionOddCore ↥(omegaGen Φ) = ⊥ := TL4.oddCore_eq_bot_of_normal hO hHn
  have hlt : Nat.card ↥(omegaGen Φ) < m := hY ▸ lt_of_le_of_ne (Subgroup.card_le_card_group _)
    fun h => hgen ((Subgroup.card_eq_iff_eq_top _).mp h)
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  have hJH : J ≤ omegaGen Φ := le_omegaGen hv.mem
  exact hb _ hlt ↥(omegaGen Φ) rfl hOH _ (hΦ.restrict _) _ (subgroupOf_mem_restrictFamily hK hKH)
    (not_aEmpty_iff.mpr ⟨_, _, _, aViol_restrict_gen hΦ.hyp hKH hJH hv⟩)

theorem isSimpleGroup_of_fstar_eq_top (hs : IsSimpleGroup ↥(genFittingFStar Y))
    (htop : genFittingFStar Y = ⊤) : IsSimpleGroup Y :=
  ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.isSimpleGroup

theorem eq_conjClass_of_subClass {Φ : Set (Subgroup Y)} {K : Subgroup Y} (hinv : ConjInvariant Φ)
    (hK : K ∈ Φ) (h : SubClass Φ K ⊤) : Φ = CoreAssembly.conjClass K := by
  ext L
  constructor
  · intro hL
    obtain ⟨t, -, ht⟩ := h L hL
    exact ⟨t, ht⟩
  · rintro ⟨g, rfl⟩
    exact hinv g K hK

end Aux

section Step


theorem conclG_of_parts {m : ℕ} (h2 : Thm3RLiftSub) (h3 : Thm3RTwoOrbit m) (h4 : Thm3RThmB m)
    (h5 : Thm3RO2Lift m) (h6 : Thm3RFStar) (h7 : Thm3RTwoClass m) (h7' : Thm3RTwoClassG23 m)
    (h8 : Thm3RStdSimple m) (h9 : Thm3RStdOuter m) {Y : Type} [Group Y] [Finite Y]
    (hih : StepIH m) (hY : Nat.card Y = m) (hO : classicalInvolutionOddCore Y = ⊥)
    {Φ : Set (Subgroup Y)} (hin : InnerIH Y Φ) (hΦ : TypeRHyp Φ) {K : Subgroup Y} (hK : K ∈ Φ)
    (hA : ¬ AEmpty Φ K) : Thm3RConclG Φ K := by
  by_cases hgen : omegaGen Φ = ⊤
  swap
  · exact h2 Y Φ hΦ K hK hA (concl_restrict_of_below hih.below hY hO hΦ hK hA hgen)
  have hc : Ctx m Y Φ K := ⟨hih, hY, hin, hΦ, hK, hA, hO, hgen⟩
  by_cases htw : TwinOrbits Φ K
  swap
  · exact h3 Y Φ K hc htw
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 K hK).1
  by_cases hzQ : TightInO2 z
  · exact h4 Y Φ K hc htw z hz hzQ
  have hno : ∀ z' : Y, IsUniqueInvolution K z' → ¬ TightInO2 z' := fun z' hz' =>
    hz.eq hz' ▸ hzQ
  by_cases hQ : NoNormalTwo Y
  swap
  · exact h5 Y Φ K hc htw hno hQ
  have hF : FStarSimple Y := h6 Y Φ K hΦ hK hO hgen htw hQ
  by_cases hcl : SubClass Φ K (genFittingFStar Y)
  swap
  · by_cases hG : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .G2 0 3 1
    · exact h7' Y Φ K hc htw hQ hF hcl hG
    · exact h7 Y Φ K hc htw hQ hF hcl hG
  exfalso
  by_cases htop : genFittingFStar Y = ⊤
  · haveI : IsSimpleGroup Y := isSimpleGroup_of_fstar_eq_top hF.1 htop
    have hcl' : SubClass Φ K ⊤ := htop ▸ hcl
    have hcc : Φ = CoreAssembly.conjClass K :=
      eq_conjClass_of_subClass hΦ.hyp.conjInvariant hK hcl'
    subst hcc
    exact h8 Y hY hih K hΦ hA
  · exact h9 Y Φ K hc hQ hF hcl htop

theorem thm3RStepG_at_of_parts {m : ℕ} (h2 : Thm3RLiftSub) (h3 : Thm3RTwoOrbit m)
    (h4 : Thm3RThmB m) (h5 : Thm3RO2Lift m) (h6 : Thm3RFStar) (h7 : Thm3RTwoClass m)
    (h7' : Thm3RTwoClassG23 m) (h8 : Thm3RStdSimple m) (h9 : Thm3RStdOuter m) :
    Thm3RStepG m := by
  intro hc hp hb Y _ _ hY hO
  have hih : StepIH m := ⟨hc, hp, hb⟩
  suffices key : ∀ (n : ℕ) (Φ : Set (Subgroup Y)), Φ.ncard = n → TypeRHyp Φ → ∀ K ∈ Φ,
      ¬ AEmpty Φ K → Thm3RConclG Φ K from
    fun Φ hΦ K hK hA => key _ Φ rfl hΦ K hK hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro Φ hn hΦ K hK hA
    refine conclG_of_parts h2 h3 h4 h5 h6 h7 h7' h8 h9 hih hY hO ?_ hΦ hK hA
    intro Φ' hlt hΦ' K' hK' hA'
    exact ihn _ (hn ▸ hlt) Φ' rfl hΦ' K' hK' hA'

theorem thm3RStepG_of_parts (h2 : Thm3RLiftSub) (h3 : ∀ m, Thm3RTwoOrbit m)
    (h4 : ∀ m, Thm3RThmB m) (h5 : ∀ m, Thm3RO2Lift m) (h6 : Thm3RFStar)
    (h7 : ∀ m, Thm3RTwoClass m) (h7' : ∀ m, Thm3RTwoClassG23 m) (h8 : ∀ m, Thm3RStdSimple m)
    (h9 : ∀ m, Thm3RStdOuter m) : ∀ m, Thm3RStepG m :=
  fun m => thm3RStepG_at_of_parts h2 (h3 m) (h4 m) (h5 m) h6 (h7 m) (h7' m) (h8 m) (h9 m)

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
