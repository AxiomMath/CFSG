module

public import CFSG.ClassicalInvolution.RouteD.TWYEven
public import CFSG.ClassicalInvolution.RouteD.TWYOdd
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk3
public import CFSG.ClassicalInvolution.Q3.Q3TWY4
public import CFSG.ClassicalInvolution.Q3.Q3E8BCent
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TWY CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.GroupTheory.WeirSylow (IsPlusType not_isPlusType_quadMinus isPlusType_quadPlus)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


structure SpinCtx3 (t : StatedLieTag) {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    (Q : QuadraticForm F (ι → F)) (D : UniversalRootDatum (spinGroup Q)) : Prop where
  hodd : Odd (Nat.card F)
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  perfect : Group.IsPerfect (spinGroup Q)
  hZ : CenterScalar Q
  hV : 7 ≤ Module.finrank F (ι → F)
  hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False
  hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1
  cq : ∃ Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F)),
    Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups t D) (fundSet Q) Z'

section Count

variable {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
  {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}

theorem card_fund_centralizing_twin3 (c : SpinCtx3 t Q D) {R R' : Subgroup (spinGroup Q)}
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
  obtain ⟨Z', cq⟩ := c.cq
  have := c.perfect
  have hker := ker_spinAction_le_center Q
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ :=
    Q3TY.exists_twin_frame3 c.hodd c.hrange c.hZ (by have := c.hV; omega) c.hproj
      (cq.map_inj hd.mem hd.mem') (cq.map_mem R hd.mem) (cq.map_mem R' hd.mem')
      (c.hnc R hd.mem) (c.hnc R' hd.mem') hd.ne hd.hx hd.cx hd.nx hd.hx' hd.cx' hd.nx' hd.same
      ha ha' hsq hsq'
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd c.hodd
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
  have hV4 : 7 ≤ Module.finrank F (ι → F) := by have := c.hV; omega
  refine ⟨plusSp (twinInv F₁ A A'), ?_, by omega, ?_, ?_⟩
  · exact CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl c.hQ
      (isCompl_plusSp_minusSp h2 hu2) (fun x hx y hy => polar_plusSp_minusSp h2 huO hx hy)
  · set X := plusSp (twinInv F₁ A A') with hX
    have hminus_lt : Module.finrank F (minusSp (twinInv F₁ A A')) < 4 := by omega
    have hLa : ∀ fr : OFrame Q, fr.La.range ≤ Subgroup.centralizer
        ({twinInv F₁ A A'} : Set ((ι → F) ≃ₗ[F] (ι → F))) ↔ fr.span ≤ X := fun fr =>
      La_range_le_centralizer_iff h2 fr huO hu2 hminus_lt
    let Lset : Set (Subgroup ((ι → F) ≃ₗ[F] (ι → F))) :=
      {L | ∃ fr : OFrame Q, fr.La.range = L ∧ fr.span ≤ X}
    have hmem : ∀ S : {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
        S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))},
        S.1.map (spinAction Q) ∈ Lset := by
      rintro ⟨S, hS, hSc⟩
      obtain ⟨i₀, fr, hfr, -⟩ := cq.map_mem S hS
      refine ⟨fr, hfr.symm, (hLa fr).mp ?_⟩
      have := (Q3W.le_centralizer_iff_map3 (spinAction Q) cq.ker_le cq.cop (cq.pow3 S hS)
        (a * a')).mp hSc
      rw [hfr, hθu] at this
      exact this
    have hNat : Nat.card {S : Subgroup (spinGroup Q) // S ∈ fundamentalSubgroups t D ∧
        S ≤ Subgroup.centralizer ({a * a'} : Set (spinGroup Q))} = Lset.ncard := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_congr (Equiv.ofBijective (fun S => ⟨S.1.map (spinAction Q), hmem S⟩)
        ⟨?_, ?_⟩)
      · intro S₁ S₂ h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (cq.map_inj S₁.2.1 S₂.2.1 h')
      · rintro ⟨L, fr, hfr, hspan⟩
        have hL : L ∈ fundSet Q := ⟨_, hfr ▸ IsFundamental.of_frame fr⟩
        obtain ⟨S, hS, hSL⟩ := cq.surj L hL
        refine ⟨⟨S, hS, ?_⟩, Subtype.ext hSL⟩
        refine (Q3W.le_centralizer_iff_map3 (spinAction Q) cq.ker_le cq.cop (cq.pow3 S hS)
          (a * a')).mpr ?_
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

theorem card_fund_centralizing3_even (c : SpinCtx3 t Q D) {m : ℕ}
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
  obtain ⟨X, hX, hXd, hcount, W, hc, horth, hW, hWd, hWt⟩ :=
    card_fund_centralizing_twin3 c hd ha ha' hsq hsq'
  have hV := c.hV
  have hXd' : Module.finrank F X = 2 * (m - 1) := by omega
  have hnd := nondegenerate_polarBilin_restrict hX
  have htype := isPlusType_iff_of_isCompl hc horth hX hW (a := m - 1) (b := 1) (by omega) le_rfl
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

theorem not_isSquare_neg_one_gf3 : ¬ IsSquare (-1 : GaloisField 3 1) := fun ⟨c, hc⟩ =>
  Q3TWY.nsq_gf3 c hc.symm

theorem spinCtx3_odd {n : ℕ} (hn3 : 3 ≤ n) :
    SpinCtx3 .POmegaOdd (quadOdd n (GaloisField 3 1)) (oddDatum n (GaloisField 3 1)) := by
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 := ⟨Nat.prime_three, le_rfl, hn3, by norm_num⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hY := Q3W.yData3_odd hn3 hadm
  exact ⟨Q3W.odd_gf3, nondegenerate_polarBilin_quadOdd n _ h2, range_spinAction_quadOdd h2 hn3,
    isPerfect_spinGroup_quadOdd h2 hn3, centerScalar_quadOdd h2 hn3, by omega,
    fun F₁ F₂ h => ModelFacts.TG3.hproj_odd F₁ F₂ h, hY.central,
    ⟨_, Q3TWY.centralQuot3_odd hn3⟩⟩

theorem spinCtx3_minus {n : ℕ} (hn4 : 4 ≤ n) :
    SpinCtx3 .POmegaMinus (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
      (Twisted.minusDatum n (minusCoeffs_irr 3 1)) := by
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 := ⟨Nat.prime_three, le_rfl, hn4⟩
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hY := Q3W.yData3_minus hn4 hadm
  exact ⟨Q3W.odd_gf3, nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr 3 1),
    range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1),
    isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr 3 1),
    centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1), by omega,
    fun F₁ F₂ h => ModelFacts.TG3.hproj_minus (minusCoeffs_irr 3 1) hn4 F₁ F₂ h, hY.central,
    ⟨_, Q3TY.centralQuot3_minus hadm⟩⟩

theorem spinCtx3_plus {n : ℕ} (hn : 5 ≤ n) (hn3 : 3 ≤ n) :
    SpinCtx3 .POmegaPlus (quadPlus n (GaloisField 3 1)) (plusDatum n (GaloisField 3 1) hn3) := by
  have hn4 : 4 ≤ n := by omega
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
  exact ⟨Q3W.odd_gf3, nondegenerate_polarBilin_quadPlus n _, range_spinAction_quadPlus hn3,
    isPerfect_spinGroup_quadPlus hn3, centerScalar_quadPlus hn3, by omega,
    fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj Q3W.odd_gf3 F₁ F₂ h
      omega, hnc, ⟨_, Q3TY.centralQuot3_plus hn4⟩⟩

theorem card_fund_centralizing3_plus {nY : ℕ} (hn : 5 ≤ nY)
    {R R' : Subgroup (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).K}
    {x x' a a' : (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .POmegaPlus (modelUniv .POmegaPlus nY 3 1 Nat.prime_three) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).K) :
    Nat.card {S : Subgroup (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).K //
        S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).D ∧
          S ≤ Subgroup.centralizer ({a * a'} :
            Set (modelUniv .POmegaPlus nY 3 1 Nat.prime_three).K)} *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
    2 * framesMinus 3 (nY - 4) := by
  have hn3 : 3 ≤ nY := by omega
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus nY (GaloisField 3 1)),
      plusDatum nY (GaloisField 3 1) hn3⟩ → ∀ {R R' : Subgroup M.K} {x x' a a' : M.K},
      TwinDatumOn .POmegaPlus M R R' x x' → a ∈ R → a' ∈ R' →
      a * a * x⁻¹ ∈ Subgroup.center M.K → a' * a' * x'⁻¹ ∈ Subgroup.center M.K →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set M.K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      2 * framesMinus 3 (nY - 4) := by
    intro M hM
    subst hM
    intro R R' x x' a a' hd ha ha' hsq hsq'
    have c := spinCtx3_plus hn hn3
    have hdim : Module.finrank (GaloisField 3 1) (Fin nY ⊕ Fin nY → GaloisField 3 1) =
        2 * nY := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    have hmain := card_fund_centralizing3_even c hdim hd ha ha' hsq hsq'
    have hP : IsPlusType (quadPlus nY (GaloisField 3 1)) := isPlusType_quadPlus _ nY
    have := hmain.2 (fun h => not_isSquare_neg_one_gf3 (h.mp hP))
    rw [Q3W.card_gf3] at this
    exact this
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3) hd ha ha' hsq hsq'

theorem card_fund_centralizing3_minus {nY : ℕ} (hn : 4 ≤ nY)
    {R R' : Subgroup (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).K}
    {x x' a a' : (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .POmegaMinus (modelUniv .POmegaMinus nY 3 1 Nat.prime_three) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).K) :
    Nat.card {S : Subgroup (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).K //
        S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).D ∧
          S ≤ Subgroup.centralizer ({a * a'} :
            Set (modelUniv .POmegaMinus nY 3 1 Nat.prime_three).K)} *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
    2 * framesPlus 3 (nY - 3) := by
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (nY - 1) ⊕ Fin (nY - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * nY := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hmain := card_fund_centralizing3_even (spinCtx3_minus hn) hdim hd ha ha' hsq hsq'
  have hP : ¬ IsPlusType (quadMinus nY (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) := not_isPlusType_quadMinus (by omega) (minusCoeffs_irr 3 1)
  have := hmain.1 (iff_of_false hP not_isSquare_neg_one_gf3)
  rw [Q3W.card_gf3] at this
  exact this

theorem card_fund_centralizing3_odd {nY : ℕ} (hn : 3 ≤ nY)
    {R R' : Subgroup (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).K}
    {x x' a a' : (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .POmegaOdd (modelUniv .POmegaOdd nY 3 1 Nat.prime_three) R R' x x')
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).K) :
    Nat.card {S : Subgroup (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).K //
        S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).D ∧
          S ≤ Subgroup.centralizer ({a * a'} :
            Set (modelUniv .POmegaOdd nY 3 1 Nat.prime_three).K)} *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
    2 * framesOdd 3 (nY - 3) := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadOdd nY (GaloisField 3 1)),
      oddDatum nY (GaloisField 3 1)⟩ → ∀ {R R' : Subgroup M.K} {x x' a a' : M.K},
      TwinDatumOn .POmegaOdd M R R' x x' → a ∈ R → a' ∈ R' →
      a * a * x⁻¹ ∈ Subgroup.center M.K → a' * a' * x'⁻¹ ∈ Subgroup.center M.K →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaOdd M.D ∧
          S ≤ Subgroup.centralizer ({a * a'} : Set M.K)} *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      2 * framesOdd 3 (nY - 3) := by
    intro M hM
    subst hM
    intro R R' x x' a a' hd ha ha' hsq hsq'
    have c := spinCtx3_odd hn
    obtain ⟨X, hX, hdim, hcount, -⟩ := card_fund_centralizing_twin3 c hd ha ha' hsq hsq'
    have hV : Module.finrank (GaloisField 3 1) (Fin nY ⊕ Fin nY ⊕ Unit → GaloisField 3 1) =
        2 * nY + 1 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit]
      ring
    have hXdim : Module.finrank (GaloisField 3 1) X = 2 * ((nY - 3) + 2) + 1 := by omega
    have hfr := card_frame_regular_odd Q3W.odd_gf3 (nondegenerate_polarBilin_restrict hX) hXdim
    rw [hcount, hfr, Q3W.card_gf3]
  exact key _ rfl hd ha ha' hsq hsq'

end CFSG.ClassicalInvolution.Q3.Q3TIY
