module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinNC
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinCtx
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TIVOr2
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinMFCommutantOn)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


section Main

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem spinGroup_mfNC3 [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 9 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {𝓕 : Set (Subgroup (spinGroup Q))} {Z' : Subgroup (V ≃ₗ[F] V)}
    (cq : Q3W.CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) Z')
    (hnc : ∀ S ∈ 𝓕, ∀ r ∈ S, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    {R R' : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕) (hne : R ≠ R')
    {x x' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) {R'' : Subgroup (spinGroup Q)}
    (hR'' : R'' ∈ 𝓕) (hS : ∀ S ∈ 𝓕, Commutes S R → Commutes S R' → Commutes R'' S) :
    R'' = R ∨ R'' = R' := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, hF₁, hF₁', -, -⟩ := Q3TY.exists_pair_frame3 hodd hrange hZ (by omega) hproj
    (cq.map_inj hR hR') (cq.map_mem R hR) (cq.map_mem R' hR') (hnc R hR) (hnc R' hR') hne hx hcx
    hx1 hx' hcx' hx'1 hsame
  obtain ⟨i'', F'', hF'', -⟩ := cq.map_mem R'' hR''
  have hcomm : ∀ G : OFrame Q, G.span ≤ F₁.perp → Commutes F''.La.range G.La.range := by
    intro G hG
    obtain ⟨S, hS𝓕, hSG⟩ := cq.surj G.La.range ⟨G.La (-1), IsFundamental.of_frame G⟩
    have hperpF : ∀ (X Y : Matrix (Fin 2) (Fin 2) F), polar Q (G.incl X) (F₁.incl Y) = 0 :=
      fun X Y => (Frame.mem_perp_iff_forall_incl F₁).mp (hG ⟨X, rfl⟩) Y
    have h1 : Commutes S R := (cq.commutes_iff hS𝓕).mp (by
      rw [hSG, hF₁]
      exact RouteD.TwinY.commutes_La_range hperpF)
    have h1' : Commutes S R' := (cq.commutes_iff hS𝓕).mp (by
      rw [hSG, hF₁']
      refine RouteD.TwinY.commutes_La_range (fun X Y => ?_)
      have hY : F₁.swap.incl Y ∈ F₁.span := by
        rw [← Frame.span_eq_swap_span]
        exact ⟨Y, rfl⟩
      obtain ⟨Y', hY'⟩ := hY
      rw [← hY']
      exact hperpF X Y')
    have h3 := hS S hS𝓕 h1 h1'
    have h4 := (cq.commutes_iff hR'').mpr h3
    rwa [hF'', hSG] at h4
  have hi := RouteD.TwinY.La_neg_one_eq_of_commutes_frames hodd hQ hV hcomm
  rcases Frame.La_range_eq_or_eq_swap h2 hi with h | h
  · left
    exact cq.map_inj hR'' hR (by rw [hF'', hF₁, h])
  · right
    exact cq.map_inj hR'' hR' (by rw [hF'', hF₁', h])

end Main

section Ctx

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] {Q : QuadraticForm F (ι → F)}

theorem twinMFCommutantOn3_of_ctx {tY : StatedLieTag} {nY : ℕ}
    {D : UniversalRootDatum (spinGroup Q)}
    (hM : modelUniv tY nY 3 1 Nat.prime_three = ⟨spinGroup Q, D⟩) (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    (hperf : Group.IsPerfect (spinGroup Q)) (hZ : CenterScalar Q)
    (hV : 9 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups tY D) (fundSet Q) Z')
    (hnc : ∀ R ∈ fundamentalSubgroups tY D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) →
      r = 1) :
    TwinMFCommutantOn tY (modelUniv tY nY 3 1 Nat.prime_three) := by
  generalize modelUniv tY nY 3 1 Nat.prime_three = M at hM ⊢
  subst hM
  intro R R' x x' hd R'' hR'' hc
  have := hperf
  exact spinGroup_mfNC3 hodd hQ hrange hZ hV hproj cq hnc hd.mem hd.mem' hd.ne hd.hx hd.cx hd.nx
    hd.hx' hd.cx' hd.nx' hd.same hR'' hc

end Ctx

theorem twinMFCommutantOn3_odd {n : ℕ} (hn : 4 ≤ n) :
    TwinMFCommutantOn .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three) := by
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 := ⟨Nat.prime_three, le_rfl, hn3, by norm_num⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hY := Q3W.yData3_odd hn3 hadm
  exact twinMFCommutantOn3_of_ctx (tY := .POmegaOdd) (nY := n)
    (D := oddDatum n (GaloisField 3 1)) rfl Q3W.odd_gf3
    (nondegenerate_polarBilin_quadOdd n _ h2) (range_spinAction_quadOdd h2 hn3)
    (isPerfect_spinGroup_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega)
    (fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj Q3W.odd_gf3 F₁ F₂ h
      omega)
    (Q3TWY.centralQuot3_odd hn3) hY.central

theorem twinMFCommutantOn3_minus {n : ℕ} (hn : 5 ≤ n) :
    TwinMFCommutantOn .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three) := by
  have hn4 : 4 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 := ⟨Nat.prime_three, le_rfl, hn4⟩
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hY := Q3W.yData3_minus hn4 hadm
  exact twinMFCommutantOn3_of_ctx (tY := .POmegaMinus) (nY := n)
    (D := Twisted.minusDatum n (minusCoeffs_irr 3 1)) rfl Q3W.odd_gf3
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr 3 1))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1))
    (isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr 3 1))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) (by omega)
    (fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj Q3W.odd_gf3 F₁ F₂ h
      omega)
    (Q3TY.centralQuot3_minus hadm) hY.central

theorem twinMFCommutantOn3_plus {n : ℕ} (hn : 5 ≤ n) :
    TwinMFCommutantOn .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three) := by
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaPlus n 3 1 := ⟨Nat.prime_three, le_rfl, hn4⟩
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hY := Q3W.yData3_plus hn4 hadm
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField 3 1) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus n (GaloisField 3 1))) → r = 1 := by
    have := hY.central
    rw [e] at this
    exact this
  exact twinMFCommutantOn3_of_ctx (tY := .POmegaPlus) (nY := n)
    (D := plusDatum n (GaloisField 3 1) hn3) e Q3W.odd_gf3
    (nondegenerate_polarBilin_quadPlus n _) (range_spinAction_quadPlus hn3)
    (isPerfect_spinGroup_quadPlus hn3) (centerScalar_quadPlus hn3) (by omega)
    (fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj Q3W.odd_gf3 F₁ F₂ h
      omega)
    (Q3TY.centralQuot3_plus hn4) hnc

theorem twinMFCommutantOn3_large {tY : StatedLieTag} {nY : ℕ} (h : TwinRowLarge3 tY nY) :
    TwinMFCommutantOn tY (modelUniv tY nY 3 1 Nat.prime_three) := by
  rcases h with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · exact twinMFCommutantOn3_plus hn
  · exact twinMFCommutantOn3_minus hn
  · exact twinMFCommutantOn3_odd hn

end CFSG.ClassicalInvolution.Q3.Q3TIY
