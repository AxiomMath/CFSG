module

public import CFSG.ClassicalInvolution.RouteD.TWYCount
public import CFSG.ClassicalInvolution.RouteD.TWYEven
public import CFSG.ClassicalInvolution.RouteD.TWYOdd
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinCtx
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd fundCorr_minus)
open CFSG.GroupTheory.WeirSylow (IsPlusType not_isPlusType_quadMinus)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Context

structure SpinCtxS (t : StatedLieTag) {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    (Q : QuadraticForm F (ι → F)) (D : UniversalRootDatum (spinGroup Q)) : Prop where
  hodd : Odd (Nat.card F)
  h5 : 5 ≤ Nat.card F
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  perfect : Group.IsPerfect (spinGroup Q)
  hZ : CenterScalar Q
  hV : 7 ≤ Module.finrank F (ι → F)
  hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False
  hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q
  hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L
  hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆
  hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1

end Context

section Count

variable {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
  {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}

theorem SpinCtxS.card_fund_centralizing_twin (c : SpinCtxS t Q D) {R R' : Subgroup (spinGroup Q)}
    {x x' a a' : spinGroup Q} (hd : TwinDatumOn t ⟨spinGroup Q, D⟩ R R' x x') (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ X : Submodule F (ι → F), PolarNondegOn Q X ∧
      Module.finrank F X + 2 = Module.finrank F (ι → F) ∧
      Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
      2 * Nat.card (OFrame (Q.restrict X)) ∧
    ∃ W : Submodule F (ι → F), IsCompl X W ∧ (∀ x ∈ X, ∀ y ∈ W, polar Q x y = 0) ∧
      PolarNondegOn Q W ∧ Module.finrank F W = 2 ∧
      (IsPlusType (Q.restrict W) ↔ IsSquare (-1 : F)) := by
  classical
  have := c.perfect
  have hker := ker_spinAction_le_center Q
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ :=
    exists_twin_frame c.hodd c.hrange c.hZ c.hV c.hproj (c.hperf R hd.mem)
      (c.hperf R' hd.mem') (c.hcorr R hd.mem) (c.hcorr R' hd.mem') (c.hnc R hd.mem)
      (c.hnc R' hd.mem') hd.ne hd.hx hd.cx hd.nx hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq'
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card c.hodd
  have hθu : spinAction Q (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have huO : twinInv F₁ A A' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    twinInv_mem_orthogonalGroup F₁ A A'
  have hu2 : twinInv F₁ A A' * twinInv F₁ A A' = 1 :=
    LinearEquiv.ext fun v => twinInv_twinInv F₁ hAA hA'A' v
  have hdet : LinearEquiv.det (twinInv F₁ A A') = 1 := by
    have := CFSG.ClassicalInvolution.Asc77.T7H.det_spinAction_eq_one (a * a')
    rwa [hθu] at this
  have hfin := CFSG.ClassicalInvolution.Asc77.T7H.finrank_plusSp_twinInv h2 F₁ hAA hA'A' hdet
  have hmin := CFSG.ClassicalInvolution.Asc77.T7H.finrank_minusSp_twinInv h2 F₁ hAA hA'A' hdet
  have hV4 : 7 ≤ Module.finrank F (ι → F) := c.hV
  refine ⟨plusSp (twinInv F₁ A A'), ?_, by omega, ?_, ?_⟩
  · exact CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl c.hQ
      (isCompl_plusSp_minusSp h2 hu2) (fun x hx y hy => polar_plusSp_minusSp h2 huO hx hy)
  · set X := plusSp (twinInv F₁ A A') with hX
    have hminus_lt : Module.finrank F (minusSp (twinInv F₁ A A')) < 4 := by omega
    have hperfS : ∀ S ∈ fundamentalSubgroups t D, ⁅S, S⁆ = S := fun S hS =>
      le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
        S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)) (c.hperf S hS)
    have hLa : ∀ fr : OFrame Q, fr.La.range ≤ Subgroup.centralizer
        ({twinInv F₁ A A'} : Set ((ι → F) ≃ₗ[F] (ι → F))) ↔ fr.span ≤ X := fun fr =>
      La_range_le_centralizer_iff h2 fr huO hu2 hminus_lt
    let Lset : Set (Subgroup ((ι → F) ≃ₗ[F] (ι → F))) :=
      {L | ∃ fr : OFrame Q, fr.La.range = L ∧ fr.span ≤ X}
    have hmem : ∀ S : {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
        S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))},
        S.1.map (spinAction Q) ∈ Lset := by
      rintro ⟨S, hS, hSc⟩
      obtain ⟨i₀, fr, hfr, -⟩ := c.hcorr S hS
      refine ⟨fr, hfr.symm, (hLa fr).mp ?_⟩
      have := (Gaps.le_centralizer_iff_map (spinAction Q) hker (c.hperf S hS) (a * a')).mp hSc
      rw [hfr, hθu] at this
      exact this
    have hNat : Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
        S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} = Lset.ncard := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_congr (Equiv.ofBijective (fun S => ⟨S.1.map (spinAction Q), hmem S⟩)
        ⟨?_, ?_⟩)
      · intro S₁ S₂ h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect
          (spinAction Q) hker (hperfS _ S₁.2.1) (hperfS _ S₂.2.1) h')
      · rintro ⟨L, fr, hfr, hspan⟩
        have hL : L ∈ fundSet Q := ⟨_, hfr ▸ IsFundamental.of_frame fr⟩
        obtain ⟨S, hS, hSL⟩ := c.hsurj L hL
        refine ⟨⟨S, hS, ?_⟩, Subtype.ext hSL⟩
        refine (Gaps.le_centralizer_iff_map (spinAction Q) hker (c.hperf S hS) (a * a')).mpr ?_
        rw [hSL, ← hfr, hθu]
        exact (hLa fr).mpr hspan
    have h1 := two_mul_card_frames_span_le (Q := Q) c.hodd X
    have h3 := card_frames_span_le_restrict (Q := Q) X
    rw [hNat]
    calc Lset.ncard * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F)))
        = 2 * Nat.card {fr : OFrame Q // fr.span ≤ X} := h1.symm
      _ = 2 * Nat.card (OFrame (Q.restrict X)) := by rw [h3]
  · exact ⟨minusSp (twinInv F₁ A A'), isCompl_plusSp_minusSp h2 hu2,
      fun x hx y hy => polar_plusSp_minusSp h2 huO hx hy,
      CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl c.hQ
        (isCompl_plusSp_minusSp h2 hu2).symm
        (fun x hx y hy => by rw [polar_comm]; exact polar_plusSp_minusSp h2 huO hy hx),
      hmin, isPlusType_restrict_minusSp_twinInv_iff h2 F₁ hAA hA'A' hmin⟩

theorem SpinCtxS.card_fund_centralizing_even (c : SpinCtxS t Q D) {m : ℕ} (hm : 4 ≤ m)
    (hdim : Module.finrank F (ι → F) = 2 * m) {R R' : Subgroup (spinGroup Q)}
    {x x' a a' : spinGroup Q} (hd : TwinDatumOn t ⟨spinGroup Q, D⟩ R R' x x') (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ((IsPlusType Q ↔ IsSquare (-1 : F)) →
      Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
      2 * framesPlus (Nat.card F) (m - 3)) ∧
    (¬ (IsPlusType Q ↔ IsSquare (-1 : F)) →
      Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
      2 * framesMinus (Nat.card F) (m - 4)) := by
  obtain ⟨X, hX, hXd, hcount, W, hc', horth, hW, hWd, hWt⟩ :=
    c.card_fund_centralizing_twin hd ha ha' hsq hsq'
  have hXd' : Module.finrank F X = 2 * (m - 1) := by omega
  have hnd := nondegenerate_polarBilin_restrict hX
  have htype := isPlusType_iff_of_isCompl hc' horth hX hW (a := m - 1) (b := 1) (by omega) le_rfl
    hXd' (by omega)
  have hPX : IsPlusType (Q.restrict X) ↔ (IsPlusType Q ↔ IsSquare (-1 : F)) := by
    have h1 := htype
    have h2 := hWt
    tauto
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [hcount, card_frame_regular_plus hnd (j := m - 3) (by omega) (hPX.mpr hs)]
  · rw [hcount, card_frame_regular_minus c.hodd hnd (j := m - 4) (by omega)
      (fun h => hs (hPX.mp h))]

end Count

section Models

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem spinCtxS_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n)
    (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    SpinCtxS .POmegaOdd (quadOdd n (GaloisField p f)) (oddDatum n (GaloisField p f)) := by
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := n) (e := f) trivial hadm
    (by omega)
  have hnc := CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := f)
    (t := .POmegaOdd) (n := n) trivial hadm (by simp)
  have hc := fundCorr_odd hp2 hq hadm
  have : Group.IsPerfect (spinGroup (quadOdd n (GaloisField p f))) :=
    isPerfect_spinGroup_quadOdd h2 hn
  exact ⟨hodd, CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq,
    nondegenerate_polarBilin_quadOdd n _ h2, range_spinAction_quadOdd h2 hn, this,
    centerScalar_quadOdd h2 hn, by omega, fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega, hc.1, hc.2, hperf, hnc⟩

theorem spinCtxS_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n p f) :
    SpinCtxS .POmegaMinus
      (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
      (Twisted.minusDatum n (minusCoeffs_irr p f)) := by
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := isPerfect_spinGroup_quadMinus hn (minusCoeffs_irr p f)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := f) trivial hadm
    (by omega)
  have hnc := CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := f)
    (t := .POmegaMinus) (n := n) trivial hadm (by simp)
  have hc := fundCorr_minus hp2 hq hadm
  show SpinCtxS .POmegaMinus (quadMinus n (GaloisField p f) (minusCoeffs p f).1
    (minusCoeffs p f).2) (Twisted.minusDatum n (minusCoeffs_irr p f))
  exact ⟨hodd, CFSG.ClassicalInvolution.Asc77.five_le_card_galoisField hq,
    nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p f),
    range_spinAction_quadMinus hn (minusCoeffs_irr p f), this,
    centerScalar_quadMinus hn (minusCoeffs_irr p f), by omega,
    fun F₁ F₂ h => CFSG.ClassicalInvolution.Asc77.hproj_quadMinus hp2 hq hn F₁ F₂ h,
    hc.1, hc.2, hperf, hnc⟩

theorem card_fund_centralizing_odd3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (modelUniv .POmegaOdd 3 p f Fact.out).K}
    {x x' a a' : (modelUniv .POmegaOdd 3 p f Fact.out).K}
    (hd : TwinDatumOn .POmegaOdd (modelUniv .POmegaOdd 3 p f Fact.out) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 3 p f Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 3 p f Fact.out).K) :
    Nat.card {S : Subgroup (modelUniv .POmegaOdd 3 p f Fact.out).K //
        S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 p f Fact.out).D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set (modelUniv .POmegaOdd 3 p f Fact.out).K)} *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
    2 * framesOdd (p ^ f) 0 := by
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨Fact.out, he, by omega, hp2⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadOdd 3 (GaloisField p f)),
      oddDatum 3 (GaloisField p f)⟩ → ∀ {R R' : Subgroup M.K} {x x' a a' : M.K},
      TwinDatumOn .POmegaOdd M R R' x x' → a ∈ R → a' ∈ R' →
      a * a * x⁻¹ ∈ Subgroup.center M.K → a' * a' * x'⁻¹ ∈ Subgroup.center M.K →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaOdd M.D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set M.K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesOdd (p ^ f) 0 := by
    intro M hM
    subst hM
    intro R R' x x' a a' hd ha ha' hsq hsq'
    have c := spinCtxS_odd hp2 hq (le_refl 3) hadm
    obtain ⟨X, hX, hdim, hcount, -⟩ := c.card_fund_centralizing_twin hd ha ha' hsq hsq'
    have hV : Module.finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) = 7 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit]
    have hXdim : Module.finrank (GaloisField p f) X = 2 * (0 + 2) + 1 := by omega
    have hfr := card_frame_regular_odd c.hodd (nondegenerate_polarBilin_restrict hX) hXdim
    rw [hcount, hfr, hcard]
  exact key _ rfl hd ha ha' hsq hsq'

theorem card_fund_centralizing_minus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K}
    {x x' a a' : (modelUniv .POmegaMinus 4 p f Fact.out).K}
    (hd : TwinDatumOn .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K) :
    (IsSquare (-1 : GaloisField p f) →
      Nat.card {S : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K //
          S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} :
              Set (modelUniv .POmegaMinus 4 p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesMinus (p ^ f) 0) ∧
    (¬ IsSquare (-1 : GaloisField p f) →
      Nat.card {S : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K //
          S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D ∧
            S ≤ Subgroup.centralizer ({a * a'} :
              Set (modelUniv .POmegaMinus 4 p f Fact.out).K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * framesPlus (p ^ f) 1) := by
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus 4 p f := ⟨Fact.out, he, le_refl 4⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have c := spinCtxS_minus hp2 hq (le_refl 4) hadm
  have hdim : Module.finrank (GaloisField p f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p f) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hmain := c.card_fund_centralizing_even (le_refl 4) hdim hd ha ha' hsq hsq'
  have hP : ¬ IsPlusType (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) := not_isPlusType_quadMinus (by omega) (minusCoeffs_irr p f)
  rw [hcard] at hmain
  exact ⟨fun hs => hmain.2 (fun h => hP (h.mpr hs)), fun hs => hmain.1 (iff_of_false hP hs)⟩

end Models

end CFSG.ClassicalInvolution.RouteD.TWS6
