module

public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinFrame
public import CFSG.ClassicalInvolution.RouteD.TWT9Twin
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T7H CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.TG3
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frames

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem swap_of_twin_pair3 [Finite F] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q) [Nontrivial V]
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (huniq : R.map (spinAction Q) = R'.map (spinAction Q) → R = R')
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) {H : Type} [Group H]
    (ψ : spinGroup Q →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hxx' : ψ x = ψ x') :
    ∃ F₁ : Frame Q, R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
        spinAction Q x' = F₁.swap.La (-1) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set θ := spinAction Q with hθ
  obtain ⟨i₁, F₁, hF₁, -⟩ := hR
  obtain ⟨i₂, F₂, hF₂, -⟩ := hR'
  have hθx : θ x = F₁.La (-1) := by
    have hmem : θ x ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ hx
    have hsq : θ x * θ x = 1 := by rw [← map_mul, hx2, map_one]
    have hne1 : θ x ≠ 1 := fun h => hx1 (hinj x hx h)
    have hord : orderOf (θ x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁).eq_of_orderOf_eq_two hodd hmem hord
  have hθx' : θ x' = F₂.La (-1) := by
    have hmem : θ x' ∈ F₂.La.range := hF₂ ▸ Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₂).eq_of_orderOf_eq_two hodd hmem hord
  have hc : x' * x⁻¹ ∈ Subgroup.center (spinGroup Q) :=
    hψ (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxx', mul_inv_cancel])
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hc
  have hF₁sq : F₁.La (-1) * F₁.La (-1) = 1 := F₁.La_neg_one_mul_self
  have hF₂sq : F₂.La (-1) * F₂.La (-1) = 1 := F₂.La_neg_one_mul_self
  have hF₁w : ∀ w, F₁.La (-1) (F₁.La (-1) w) = w := fun w => by
    have := congrArg (fun g : V ≃ₗ[F] V => g w) hF₁sq
    simpa using this
  have hrel : ∀ w, F₂.La (-1) w = μ • F₁.La (-1) w := by
    intro w
    have h1 := hμ (F₁.La (-1) w)
    rw [map_mul, map_inv, hθx', hθx] at h1
    have hinv : (F₁.La (-1))⁻¹ = F₁.La (-1) := inv_eq_of_mul_eq_one_right hF₁sq
    rw [hinv] at h1
    simpa only [LinearEquiv.mul_apply, hF₁w] using h1
  have hμ2 : μ * μ = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have h1 : F₂.La (-1) (F₂.La (-1) w) = w := by
      have := congrArg (fun g : V ≃ₗ[F] V => g w) hF₂sq
      simpa using this
    rw [hrel w, map_smul, hrel (F₁.La (-1) w), smul_smul, hF₁w] at h1
    have h4 : (μ * μ - 1) • w = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw)
  have hμ1 : μ = 1 := by
    rcases mul_self_eq_one_iff.mp hμ2 with h | h
    · exact h
    · exfalso
      refine hproj F₁ F₂ (LinearEquiv.ext fun w => ?_)
      rw [hrel, h, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_one_smul]
  have hFeq : F₂.La (-1) = F₁.La (-1) := LinearEquiv.ext fun w => by rw [hrel, hμ1, one_smul]
  rcases Frame.La_range_eq_or_eq_swap h2 hFeq with h | h
  · exfalso
    apply hne
    apply huniq
    rw [hF₁, hF₂, h]
  · refine ⟨F₁, hF₁, hF₂.trans h, hθx, ?_⟩
    have hmem : θ x' ∈ F₁.swap.La.range := by
      rw [← h, ← hF₂]
      exact Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁.swap).eq_of_orderOf_eq_two hodd hmem hord


theorem exists_pair_frame3 [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 1 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (huniq : R.map (spinAction Q) = R'.map (spinAction Q) → R = R')
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ F₁ : OFrame Q, R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
      spinAction Q x' = F₁.swap.La (-1) := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      hnc r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      hnc' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hsqx : ∀ {R₀ : Subgroup (spinGroup Q)} {y : spinGroup Q}, R₀.map (spinAction Q) ∈ fundSet Q →
      (∀ r ∈ R₀, spinAction Q r = 1 → r = 1) → y ∈ R₀ → (∀ r ∈ R₀, y * r = r * y) → y * y = 1 := by
    intro R₀ y hR₀ hinj₀ hy hcy
    obtain ⟨i, FR, hFR, -⟩ := hR₀
    have hθy : spinAction Q y ∈ FR.La.range := hFR ▸ Subgroup.mem_map_of_mem _ hy
    have hθyc : ∀ h ∈ FR.La.range, spinAction Q y * h = h * spinAction Q y := by
      intro h hh
      rw [← hFR] at hh
      obtain ⟨r, hr, rfl⟩ := hh
      rw [← map_mul, ← map_mul, hcy r hr]
    have h1 := TwinY.sq_eq_one_of_central_le_la FR hθy hθyc
    apply hinj₀ (y * y) (R₀.mul_mem hy hy)
    rw [map_mul]
    exact h1
  have hx2 : x * x = 1 := hsqx hR hinj hx hcx
  have hx'2 : x' * x' = 1 := hsqx hR' hinj' hx' hcx'
  have hψ : (QuotientGroup.mk' (Subgroup.center (spinGroup Q))).ker ≤
      Subgroup.center (spinGroup Q) := by
    rw [QuotientGroup.ker_mk']
  have hxx' : QuotientGroup.mk' (Subgroup.center (spinGroup Q)) x =
      QuotientGroup.mk' (Subgroup.center (spinGroup Q)) x' := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using hsame
  exact swap_of_twin_pair3 hodd hrange hZ hproj huniq hR hR' hinj hinj' hne hx hx2 hx1 hx' hx'2
    hx'1 (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) hψ hxx'

theorem exists_twin_frame3 [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (huniq : R.map (spinAction Q) = R'.map (spinAction Q) → R = R')
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' a a' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ (F₁ : OFrame Q) (A A' : SL(2, F)), R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
      spinAction Q x' = F₁.swap.La (-1) ∧ spinAction Q a = F₁.La A ∧
      spinAction Q a' = F₁.swap.La A' ∧ (A : Matrix (Fin 2) (Fin 2) F) * A = -1 ∧
      (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1 := by
  classical
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := exists_pair_frame3 hodd hrange hZ (by omega) hproj huniq
    hR hR' hnc hnc' hne hx hcx hx1 hx' hcx' hx'1 hsame
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), F₁.La A = spinAction Q a := by
    have : spinAction Q a ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ ha
    exact this
  obtain ⟨A', hA'⟩ : ∃ A' : SL(2, F), F₁.swap.La A' = spinAction Q a' := by
    have : spinAction Q a' ∈ F₁.swap.La.range := hF₁' ▸ Subgroup.mem_map_of_mem _ ha'
    exact this
  have hperp : ∀ fr : OFrame Q, fr.perp ≠ ⊥ := by
    intro fr h
    have h1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    rw [h, finrank_bot] at h1
    omega
  have hAA := TwinY.sq_eq_neg_one_of_sq_mem_center hrange hZ F₁ (hperp F₁) hA hθx hsq
  have hA'A' := TwinY.sq_eq_neg_one_of_sq_mem_center hrange hZ F₁.swap (hperp F₁.swap) hA' hθx' hsq'
  refine ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hA.symm, hA'.symm, ?_, ?_⟩
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hAA
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hA'A'
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this


end Frames

section Layer


theorem exists_twin_inv_four3
    {R R' : Subgroup (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)))
    (hne : R ≠ R')
    {x x' a a' : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)} (hx : x ∈ R)
    (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx' : x' ∈ R')
    (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) :
    ∃ (FM : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
        (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (g' : Vm 4 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 4 (GaloisField 3 1)),
      R.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = FM.La.range ∧
      R'.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = FM.swap.La.range ∧
      g' = spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (a * a') ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) y w = 0) → g' y = y) ∧
      Module.finrank (GaloisField 3 1) (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      (¬ IsSquare (-1 : GaloisField 3 1) → ∀ y ∈ FM.span, g' y = y → y ≠ 0 →
        quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2 y ≠ 0) := by
  classical
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ 4; omega⟩
  have cq := centralQuot3_minus hadm
  have hY := yData3_minus (by norm_num : 4 ≤ 4) hadm
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := isPerfect_spinGroup_quadMinus (by norm_num : 4 ≤ 4) hirr
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hV : 7 ≤ Module.finrank (GaloisField 3 1) (Vm 4 (GaloisField 3 1)) := by
    rw [finrank_minus 3 1 4 (by omega)]
    omega
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame3 odd_gf3
    (range_spinAction_quadMinus (by norm_num) hirr) (centerScalar_quadMinus (by norm_num) hirr)
    hV (fun F₁ F₂ h => hproj_minus hirr (by norm_num) F₁ F₂ h) (cq.map_inj hR hR')
    (cq.map_mem R hR) (cq.map_mem R' hR') (hY.central R hR) (hY.central R' hR') hne hx hcx hx1 hx'
    hcx' hx'1 hsame ha ha' hsq hsq'
  have hθu : spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
      (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have hdet : LinearEquiv.det (twinInv F₁ A A') = 1 := by
    rw [← hθu]
    exact det_spinAction_eq_one _
  have hii : twinInv F₁ A A' * twinInv F₁ A A' = 1 :=
    LinearEquiv.ext fun v => twinInv_twinInv F₁ hAA hA'A' v
  refine ⟨F₁, twinInv F₁ A A', hF₁, hF₁', hθu.symm, twinInv_mem_orthogonalGroup F₁ A A', hii,
    ?_, finrank_minusSp_twinInv h2 F₁ hAA hA'A' hdet, ?_, ?_⟩
  · intro y hy
    exact twinInv_perp F₁ A A' ((Frame.mem_perp_iff_forall_incl F₁).mpr fun Y => hy _ ⟨Y, rfl⟩)
  · intro y hy
    have : y ∈ eigIn (twinInv F₁ A A') (-1) F₁.span := by
      rw [← minusSp_twinInv_eq h2 F₁]
      exact hy
    exact (mem_eigIn_iff.mp this).1
  · intro hnsq y hy hyfix hy0 hQy
    obtain ⟨X, rfl⟩ := hy
    rw [twinInv_incl] at hyfix
    have hAX := F₁.incl_injective hyfix
    have hX0 : X ≠ 0 := fun h => hy0 (by rw [h, map_zero])
    have hXd : X.det = 0 := by
      rw [← F₁.Q_incl]
      exact hQy
    exact TWT9.no_singular_of_fixed h2 hnsq hAA hA'A' hX0 hXd hAX


end Layer

end CFSG.ClassicalInvolution.Q3.Q3TY
