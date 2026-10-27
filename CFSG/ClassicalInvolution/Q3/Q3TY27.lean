module

public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.RouteD.TWT8Class
public import CFSG.ClassicalInvolution.RouteD.TWT8V
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinusNormalized
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fixed
public import CFSG.ClassicalInvolution.RouteD.TWEB6YBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWT8 CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (normalized_span eigen_planes_of_inverted
  polarNondegOn_span mem_negSpace_iff' mem_posSpace_iff' eq_self_of_perp_plane)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Spin


theorem class_spin_td5_3
    {𝓕 : Set (Subgroup (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)))}
    (cq : CentralQuot3 (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) 𝓕 (fundSet (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) (scalars (GaloisField 3 1) (Vm 5 (GaloisField 3 1))))
    {g₀ h : Vm 5 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 5 (GaloisField 3 1)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (hg2 : g₀ * g₀ = 1)
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (hh2 : h * h = 1)
    {RM RM' RJ RN₁ RN₂ : Subgroup (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hRM : RM ∈ 𝓕) (hRM' : RM' ∈ 𝓕) (hRJ : RJ ∈ 𝓕) (hRN₁ : RN₁ ∈ 𝓕) (hRN₂ : RN₂ ∈ 𝓕)
    (FM : OFrame (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (hFM : RM.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) = FM.La.range)
    (hFM' : RM'.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) = FM.swap.La.range)
    (hRJM : RJ ≠ RM) (hRJM' : RJ ≠ RM')
    (hcomm : Commutes (RM.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))) (RJ.map (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))))
    (hfixM : ∀ l ∈ RM.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), g₀ * l = l * g₀)
    (hfixN₁ : ∀ l ∈ RN₁.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), g₀ * l = l * g₀)
    (hfixN₂ : ∀ l ∈ RN₂.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), g₀ * l = l * g₀)
    (hnormJ : ∀ l ∈ RJ.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), g₀ * l * g₀ ∈ RJ.map (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    {x₀ : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)}
    (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ 3 = 1)
    (hx₀inv : ∀ v, g₀ (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) x₀ v) = (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x₀).symm (g₀ v))
    (hhneg : negSpace h ≤ FM.span) (hhdim : Module.finrank (GaloisField 3 1) (negSpace h) = 2)
    (hN₁h : ∀ l ∈ RN₁.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), h * l = l * h)
    (hN₂h : ∀ l ∈ RN₂.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), h * l = l * h)
    (hbr : BridgeOmega (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
      (RN₁.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2))) (RN₂.map (spinAction (quadMinus 5 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))) :
    ∃ (x' : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (ε : GaloisField 3 1), (ε = 1 ∨ ε = -1) ∧
      RJ = ((rootSL2 (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
          (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x'
          ((minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
          (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x'
          ((minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = ε • y := by
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr 3 1
  have hQ : (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField 3 1) hirr)
  have hQ' : (polarBilin (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField 3 1) hirr
  have hdim10 : Module.finrank (GaloisField 3 1) (Vm 5 (GaloisField 3 1)) = 10 := by
    rw [finrank_minus 3 1 5 (by omega)]
  obtain ⟨iJ, hiJ⟩ := cq.map_mem _ hRJ
  obtain ⟨FJ, hFJ, hiJe⟩ := hiJ
  have hiMf : IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (RM.map (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  have hiJf : IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (RJ.map (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) (FJ.La (-1)) := by
    rw [hFJ]
    exact IsFundamental.of_frame FJ
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  have hJspan : ∀ x ∈ FJ.span, g₀ x ∈ FJ.span :=
    normalized_span hodd hgO hg2 FJ (by rw [← hFJ]; exact hnormJ)
  have hx₀mem : spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) x₀ ∈ FJ.La.range := by
    rw [← hFJ]
    exact ⟨x₀, hx₀J, rfl⟩
  obtain ⟨A, hA⟩ := hx₀mem
  have hAp : A ^ 3 = 1 := by
    apply FJ.La_injective
    rw [map_pow, hA, ← map_pow, hx₀p, map_one, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    exact hx₀1 (cq.inj RJ hRJ x₀ hx₀J hA.symm)
  have hinv : ∀ v, g₀ (FJ.La A v) = (FJ.La A).symm (g₀ v) := by
    intro v
    rw [hA]
    exact hx₀inv v
  obtain ⟨π, ρ, hπρ, hsup, hgπ, hgρ⟩ := eigen_planes_of_inverted hodd hQ' (p := 3) hgO hg2 FJ
    hJspan hA1 hAp hinv
  have hMJ : ∀ x ∈ FM.span, ∀ y ∈ FJ.span, polar (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x y = 0 := by
    rcases orth_or_twin hodd hiMf hiJf hcomm with ho | ht
    · intro x hx y hy
      exact ho x (by rw [negSpace_La_neg_one h2]; exact hx)
        y (by rw [negSpace_La_neg_one h2]; exact hy)
    · exfalso
      have ht' : FJ.La (-1) = FM.La (-1) := ht
      rcases Frame.La_range_eq_or_eq_swap h2 ht' with h | h
      · exact hRJM (cq.map_inj hRJ hRM (by rw [hFJ, h, hFM]))
      · exact hRJM' (cq.map_inj hRJ hRM' (by rw [hFJ, h, hFM']))
  obtain ⟨π', ρ', hπρ', hsup', hgπ', hgρ'⟩ : ∃ π' ρ' : HypPair (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2), π'.Orth ρ' ∧
      hypPlane π' ⊔ hypPlane ρ' = FJ.span ∧
      (∀ x ∈ hypPlane π', g₀ x = (-εM) • x) ∧ (∀ x ∈ hypPlane ρ', g₀ x = εM • x) := by
    rcases hεM with rfl | rfl
    · exact ⟨π, ρ, hπρ, hsup, fun x hx => by rw [hgπ x hx]; simp, fun x hx => by
        rw [hgρ x hx]; simp⟩
    · exact ⟨ρ, π, hπρ.symm, by rw [sup_comm]; exact hsup, fun x hx => by
        rw [hgρ x hx]; simp, fun x hx => by rw [hgπ x hx]; simp⟩
  obtain ⟨hS₁, hS₂, hSne, hSnc, hSnorm⟩ := hbr
  obtain ⟨s₁, hs₁⟩ := cq.map_mem _ hRN₁
  obtain ⟨s₂, hs₂⟩ := cq.map_mem _ hRN₂
  obtain ⟨ε₁, hε₁, hg₁⟩ := sign_of_commute h2 hs₁ hgO hg2 hfixN₁
  obtain ⟨ε₂, hε₂, hg₂⟩ := sign_of_commute h2 hs₂ hgO hg2 hfixN₂
  have hhN : ∀ {L : Subgroup (Vm 5 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 5 (GaloisField 3 1))}
      {s : Vm 5 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 5 (GaloisField 3 1)},
      IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) L s →
      (∀ l ∈ L, h * l = l * h) → ∀ x ∈ negSpace s, h x = x := by
    intro L s hL hc
    obtain ⟨ε', hε', he⟩ := sign_of_commute h2 hL hhO hh2 hc
    rcases hε' with rfl | rfl
    · intro x hx
      simpa using he x hx
    · exfalso
      have hle : negSpace s ≤ negSpace h := fun x hx =>
        mem_negSpace_iff'.mpr (by rw [he x hx]; simp)
      have h4 := Submodule.finrank_mono hle
      rw [finrank_negSpace hodd hL, hhdim] at h4
      omega
  have hW₁ : Module.finrank (GaloisField 3 1) (negSpace s₁) = 4 := finrank_negSpace hodd hs₁
  have hW₂ : Module.finrank (GaloisField 3 1) (negSpace s₂) = 4 := finrank_negSpace hodd hs₂
  have hsN : s₂ ∈ Subgroup.normalizer ((RN₁.map (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) : Subgroup _) : Set _) := hSnorm s₂ hs₂
  have hc12 : s₁ * s₂ = s₂ * s₁ := by
    have hmem := (Subgroup.mem_normalizer_iff.mp hsN s₁).mp (hs₁.mem)
    have h1 : s₂ * s₁ * s₂⁻¹ = s₁ := by
      refine IsFundamental.eq_of_orderOf_eq_two hodd hs₁ hmem ?_
      refine orderOf_eq_prime ?_ ?_
      · have hs1 : s₁ * s₁ = 1 := hs₁.mul_self
        calc (s₂ * s₁ * s₂⁻¹) ^ 2 = (s₂ * s₁ * s₂⁻¹) * (s₂ * s₁ * s₂⁻¹) := pow_two _
          _ = s₂ * (s₁ * s₁) * s₂⁻¹ := by group
          _ = 1 := by rw [hs1]; group
      · intro h
        have : s₁ = 1 := by
          have := congrArg (fun w => s₂⁻¹ * w * s₂) h
          simpa [mul_assoc] using this
        exact hs₁.ne_one hodd this
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hC : s₂ ∉ Subgroup.centralizer ((RN₁.map (spinAction (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) : Subgroup _) : Set _) := fun hcen =>
    hSnc ((IsFundamental.commute_iff hodd hs₁ hs₂ hc12 hSne).mpr hcen)
  have hF12 : Module.finrank (GaloisField 3 1) ↥(negSpace s₁ ⊓ negSpace s₂) = 2 :=
    finrank_inf_negSpace hodd hs₁ hs₂ hc12 hsN hC
  have hnd₁ : PolarNondegOn (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (negSpace s₁) := by
    obtain ⟨F₁N, -, rfl⟩ := hs₁
    rw [negSpace_La_neg_one h2]
    exact polarNondegOn_span F₁N
  have hnorth : ¬ ∀ x ∈ negSpace s₁, ∀ y ∈ negSpace s₂, polar (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x y = 0 := by
    intro hall
    have hbot : negSpace s₁ ⊓ negSpace s₂ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hx' := Submodule.mem_inf.mp hx
      refine hnd₁ x hx'.1 fun y hy => ?_
      rw [polar_comm]
      exact hall y hy x hx'.2
    rw [hbot, finrank_bot] at hF12
    omega
  have hperp := eq_smul_of_perp_td5 h2 hdim10 hgO hg2 hh2 (WM := FM.span) (WJ := FJ.span)
    FM.finrank_span (polarNondegOn_span FM) hMJ hεM hgM' π' ρ' hsup' hgπ' hgρ' hhneg hhdim
    hW₁ hW₂ hF12 hnorth hε₁ hε₂ hg₁ hg₂ (fun x hx => hhN hs₁ hN₁h x hx)
    (fun x hx => hhN hs₂ hN₂h x hx)
  set F₀ : HypFrame (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
    (5 - 1) := (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame with hF₀
  have hspanG : FJ.span = (mkFrame π' ρ' hπρ').span := by
    rw [frame_span_eq (mkFrame π' ρ' hπρ')]
    exact hsup'.symm
  have hii : FJ.La (-1) = (mkFrame π' ρ' hπρ').La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFJP1⟩ : ∃ (P1 : HypPair (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) (h : π'.Orth (swapPair P1)),
      hypPlane P1 = hypPlane ρ' ∧ FJ.La.range = (mkFrame π' (swapPair P1) h).La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with hA | hB
    · exact ⟨swapPair ρ', hπρ', by rw [hypPlane_swapPair], hA⟩
    · exact ⟨ρ', orth_swapPair hπρ', rfl, hB⟩
  have hπle : hypPlane π' ≤ FJ.span := by
    rw [← hsup']
    exact le_sup_left
  have hP1le : hypPlane P1 ≤ FJ.span := by
    rw [hP1pl, ← hsup']
    exact le_sup_right
  have hFMP : hypPlane FM.P ≤ FM.span := by
    rw [frame_span_eq]
    exact le_sup_left
  have hFMP' : hypPlane FM.P' ≤ FM.span := by
    rw [frame_span_eq]
    exact le_sup_right
  have horth : ∀ (A B : HypPair (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), hypPlane A ≤ FJ.span → hypPlane B ≤ FM.span → A.Orth B :=
    fun A B hA hB => orth_of_polar_hypPlane fun x hx y hy => by
      rw [polar_comm]
      exact hMJ y (hB hy) x (hA hx)
  have o01 : π'.Orth P1 := orth_swapPair hP1o
  have o02 : π'.Orth FM.P := horth _ _ hπle hFMP
  have o03 : π'.Orth FM.P' := horth _ _ hπle hFMP'
  have o12 : P1.Orth FM.P := horth _ _ hP1le hFMP
  have o13 : P1.Orth FM.P' := horth _ _ hP1le hFMP'
  have o23 : FM.P.Orth FM.P' := FM.orth
  let Pn : ℕ → HypPair (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) :=
    fun k => if k = 0 then π' else if k = 1 then P1 else if k = 2 then FM.P else FM.P'
  have hPn : ∀ a b, a < 4 → b < 4 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o03, o03.symm, o12, o12.symm, o13, o13.symm, o23,
          o23.symm]
  let P : Fin (5 - 1) → HypPair (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) := fun i => Pn i.val
  have hPo : ∀ i j : Fin (5 - 1), i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨3, by omega⟩ : Fin (5 - 1))
  have hP0 : π'.e = spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π'.f = spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π' := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) x' (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨1, by omega⟩ = P1 := by simp [P, Pn]
    rw [e] at this
    exact this
  have hrange := La_range_eq_of_pairs F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega) true
    false x' hP1o hP0 ⟨hP1.2, hP1.1⟩
  have hRJeq : RJ = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x').toMonoidHom) :=
    cq.map_inj hRJ (cq.rootSL2_conj_mem F₀ _ _ _ true false x')
      (by rw [hFJ, hFJP1, hrange])
  refine ⟨x', εM, hεM, hRJeq, fun y h1 h2' => hperp y ?_⟩
  rw [← hP0.1] at h1
  rw [← hP0.2] at h2'
  exact HypPair.mem_perp.mpr ⟨h1, h2'⟩


end Spin

end CFSG.ClassicalInvolution.Q3.Q3TY
