module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.ReduceDstar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.ReduceStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Reduce

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem aStar_eq_of_twinOrbits (hb : Thm3RBelowG (Nat.card Y)) (hΦ : TypeRHyp Φ)
    (hO : classicalInvolutionOddCore Y = ⊥) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hgen : omegaGen Φ = ⊤) (htw : TwinOrbits Φ K) {z : Y} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) : aStar Φ K = Φ := by
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hzO
  have h := QFam.of_twinOrbits hΦ hO hK hA htw hz hQn hQ2 hzQ
  exact h.aStar_eq_of_dstarComp_eq hb hK hgen htw (h.dstarComp_eq hb hK htw)

theorem vStar_eq_of_twinOrbits (hb : Thm3RBelowG (Nat.card Y)) (hΦ : TypeRHyp Φ)
    (hO : classicalInvolutionOddCore Y = ⊥) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hgen : omegaGen Φ = ⊤) (htw : TwinOrbits Φ K) {z : Y} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) : vStar Φ K = Φ := by
  have hA' := aStar_eq_of_twinOrbits hb hΦ hO hK hA hgen htw hz hzO
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hzO
  have h := QFam.of_twinOrbits hΦ hO hK hA htw hz hQn hQ2 hzQ
  refine Set.Subset.antisymm (fun M hM => hM.1) fun M hM => h.aStar_subset_vStar hK ?_
  rw [hA']
  exact hM

theorem thm3One_of_twinOrbits (hb : Thm3RBelowG (Nat.card Y)) (hΦ : TypeRHyp Φ)
    (hO : classicalInvolutionOddCore Y = ⊥) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hgen : omegaGen Φ = ⊤) (htw : TwinOrbits Φ K) {z : Y} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) :
    aStar Φ K = vStar Φ K ∧
      ∀ L ∈ Φ, L ∉ vStar Φ K → ∀ M ∈ vStar Φ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M := by
  have hV := vStar_eq_of_twinOrbits hb hΦ hO hK hA hgen htw hz hzO
  refine ⟨(aStar_eq_of_twinOrbits hb hΦ hO hK hA hgen htw hz hzO).trans hV.symm, ?_⟩
  intro L hL hLV
  rw [hV] at hLV
  exact absurd hL hLV

theorem thm3RConclG_of_twinOrbits (hb : Thm3RBelowG (Nat.card Y)) (hΦ : TypeRHyp Φ)
    (hO : classicalInvolutionOddCore Y = ⊥) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hgen : omegaGen Φ = ⊤) (htw : TwinOrbits Φ K) {z : Y} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) (hrow : Thm3RowsG Φ ⊤) : Thm3RConclG Φ K := by
  refine ⟨thm3One_of_twinOrbits hb hΦ hO hK hA hgen htw hz hzO, ?_⟩
  rw [aStar_eq_of_twinOrbits hb hΦ hO hK hA hgen htw hz hzO, hgen]
  exact hrow

end Reduce

section Step


theorem aStar_eq_of_ctx {m : ℕ} {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    {K : Subgroup Y} (hc : Ctx m Y Φ K) (htw : TwinOrbits Φ K) {z : Y}
    (hz : IsUniqueInvolution K z) (hzO : TightInO2 z) : aStar Φ K = Φ :=
  aStar_eq_of_twinOrbits (hc.card ▸ hc.ih.below) hc.hyp hc.odd hc.mem hc.notEmpty hc.gen htw hz
    hzO

theorem thm3RThmB_of_rows {m : ℕ}
    (hrows : ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y),
      Ctx m Y Φ K → TwinOrbits Φ K → ∀ z : Y, IsUniqueInvolution K z → TightInO2 z →
        aStar Φ K = Φ → Thm3RowsG Φ ⊤) :
    Thm3RThmB m := by
  intro Y _ _ Φ K hc htw z hz hzO
  exact thm3RConclG_of_twinOrbits (hc.card ▸ hc.ih.below) hc.hyp hc.odd hc.mem hc.notEmpty
    hc.gen htw hz hzO (hrows Y Φ K hc htw z hz hzO (aStar_eq_of_ctx hc htw hz hzO))

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
