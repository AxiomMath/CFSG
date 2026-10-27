module

public import CFSG.ClassicalInvolution.RouteD.TwinYR3Frames
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinCtx
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinFrame
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinV
public import CFSG.ClassicalInvolution.Asc77.AscT7HS2
public import CFSG.ClassicalInvolution.RouteD.TWYPlane

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Count

variable {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
  {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}

theorem card_fund_centralizing_twin (c : SpinCtx t Q D) {R R' : Subgroup (spinGroup Q)}
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
    exists_twin_frame c.hodd c.hrange c.hZ (by have := c.hV; omega) c.hproj (c.hperf R hd.mem)
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
  have hV4 : 7 ≤ Module.finrank F (ι → F) := by have := c.hV; omega
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

end Count

end CFSG.ClassicalInvolution.RouteD.TWY
