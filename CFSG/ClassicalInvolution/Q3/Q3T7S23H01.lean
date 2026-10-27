module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22TSF
public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Ord
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Asc77.AscT7HS4
public import CFSG.ClassicalInvolution.Asc77.AscT7HS3
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Base
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Main
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77.T7H
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
open CFSG.ClassicalInvolution.ModelFacts hiding modelUniv fundamentalSubgroups
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups


section Spin

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem spin_twin_sq_false3 (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V) (hV4 : ¬ 4 ∣ Module.finrank F V - 2)
    (hcop : ∀ z ∈ (spinAction Q).ker, ¬ 3 ∣ orderOf z)
    {R R' : Subgroup (spinGroup Q)} (hRp : Q3W.Pow3 R) (hR'p : Q3W.Pow3 R')
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') (hcomm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {x x' : spinGroup Q} (hx : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    {c : spinGroup Q} (hc : c ∈ Subgroup.center (spinGroup Q)) (hcc : c * c = x * x') : False := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  set θ := spinAction Q with hθ
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hc
  obtain ⟨w, hw⟩ : ∃ w : V, Q w ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (eq_zero_of_polar_eq_zero hQ fun y => by
      rw [polar, hall, hall, hall]; simp)
  have hμ2 : μ * μ = 1 := by
    have h1 := map_spinAction Q c w
    rw [hμ w, QuadraticMap.map_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ hw (by rw [one_mul]; exact h1)
  have hθcc : θ c * θ c = 1 := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, hμ v, map_smul, hμ v, smul_smul, hμ2, one_smul]
    rfl
  have hxx' : θ x * θ x' = 1 := by
    rw [← map_mul, ← hcc, map_mul]
    exact hθcc
  have hx'sq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
  have hord : θ x = θ x' := mul_right_cancel (hxx'.trans hx'sq.symm)
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ :=
    Q3TD.swap_of_twin_pair_ord3 hodd hcop hRp hR'p hR hR' hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1
      hord
  obtain ⟨a, haR, hθa⟩ : ∃ a ∈ R, θ a = F₁.La (J2 F) := by
    have : F₁.La (J2 F) ∈ R.map θ := by rw [hF₁]; exact ⟨J2 F, rfl⟩
    obtain ⟨a, ha, h⟩ := this
    exact ⟨a, ha, h⟩
  obtain ⟨a', ha'R, hθa'⟩ : ∃ a' ∈ R', θ a' = F₁.swap.La (J2 F) := by
    have : F₁.swap.La (J2 F) ∈ R'.map θ := by rw [hF₁']; exact ⟨J2 F, rfl⟩
    obtain ⟨a', ha', h⟩ := this
    exact ⟨a', ha', h⟩
  have haa : a * a = x := by
    have h1 : θ (a * a * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hθa, hθx, ← map_mul, J2_mul_self]
      exact mul_inv_cancel _
    have := hinj (a * a * x⁻¹) (R.mul_mem (R.mul_mem haR haR) (R.inv_mem hx)) h1
    rwa [mul_inv_eq_one] at this
  have ha'a' : a' * a' = x' := by
    have h1 : θ (a' * a' * x'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hθa', hθx', ← map_mul, J2_mul_self]
      exact mul_inv_cancel _
    have := hinj' (a' * a' * x'⁻¹) (R'.mul_mem (R'.mul_mem ha'R ha'R) (R'.inv_mem hx')) h1
    rwa [mul_inv_eq_one] at this
  have hcomm' : a' * a = a * a' := (hcomm a haR a' ha'R).symm
  have huu : a * a' * (a * a') = x * x' := by
    calc a * a' * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [hcomm']
      _ = (a * a) * (a' * a') := by group
      _ = x * x' := by rw [haa, ha'a']
  have hcinv : c⁻¹ ∈ Subgroup.center (spinGroup Q) := inv_mem hc
  have hvv : (a * a' * c⁻¹) * (a * a' * c⁻¹) = 1 := by
    calc a * a' * c⁻¹ * (a * a' * c⁻¹) = a * a' * (c⁻¹ * (a * a')) * c⁻¹ := by group
      _ = a * a' * ((a * a') * c⁻¹) * c⁻¹ := by
          rw [← Subgroup.mem_center_iff.mp hcinv (a * a')]
      _ = (a * a' * (a * a')) * (c⁻¹ * c⁻¹) := by group
      _ = 1 := by rw [huu, ← hcc]; group
  have h4 := four_dvd_finrank_minusSp_of_sq_one h2 hQ hvv (det_spinAction_eq_one _)
  have hAA : ((J2 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (J2 F : Matrix (Fin 2) (Fin 2) F) =
      -1 := coe_J2_mul_self
  have hdetu : LinearEquiv.det (twinInv F₁ (J2 F) (J2 F)) = 1 := by
    have := det_spinAction_eq_one (a * a')
    rwa [map_mul, hθa, hθa'] at this
  have hθv : θ (a * a' * c⁻¹) = twinInv F₁ (J2 F) (J2 F) * (θ c)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hθa, hθa']
    rfl
  rcases mul_self_eq_one_iff.mp hμ2 with h | h
  · have hθc : θ c = 1 := LinearEquiv.ext fun v => by rw [hμ v, h, one_smul]; rfl
    rw [hθv, hθc, inv_one, mul_one, finrank_minusSp_twinInv h2 F₁ hAA hAA hdetu] at h4
    omega
  · have hθc : θ c = LinearEquiv.neg F := LinearEquiv.ext fun v => by
      rw [hμ v, h, neg_one_smul]; rfl
    have hneg : (LinearEquiv.neg F : V ≃ₗ[F] V)⁻¹ = LinearEquiv.neg F := by
      refine inv_eq_of_mul_eq_one_right (LinearEquiv.ext fun v => ?_)
      simp
    have hms : minusSp (twinInv F₁ (J2 F) (J2 F) * LinearEquiv.neg F) =
        plusSp (twinInv F₁ (J2 F) (J2 F)) := by
      ext v
      rw [mem_minusSp, mem_plusSp, LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg, neg_inj]
    rw [hθv, hθc, hneg, hms, finrank_plusSp_twinInv h2 F₁ hAA hAA hdetu] at h4
    exact hV4 h4

theorem spin_family_twin_no_sq3 (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V) (hV4 : ¬ 4 ∣ Module.finrank F V - 2)
    {Φ : Set (Subgroup (spinGroup Q))} {Z' : Subgroup (V ≃ₗ[F] V)}
    (cq : Q3W.CentralQuot3 (spinAction Q) Φ (fundSet Q) Z') :
    ∀ R ∈ Φ, ∀ R' ∈ Φ, R ≠ R' → (∀ a ∈ R, ∀ b ∈ R', a * b = b * a) →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (spinGroup Q), c * c = x * x' → False := by
  intro R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hc hcc
  exact spin_twin_sq_false3 hodd hQ hrange hZ hV hV4 cq.cop (cq.pow3 R hR) (cq.pow3 R' hR')
    (cq.map_mem R hR) (cq.map_mem R' hR') (cq.inj R hR) (cq.inj R' hR') hne hcomm hx hx2 hx1 hx'
    hx'2 hx'1 hc hcc

end Spin

section Rows

theorem psp2_twin_no_sq3 (hadm : StatedLieAdmissible .PSp 2 3 1) :
    ∀ R ∈ ModelFund 3 .PSp 2 1, ∀ R' ∈ ModelFund 3 .PSp 2 1, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .PSp 2 3 1 Fact.out).K, c * c = x * x' → False := by
  intro R hR R' hR' hne hcomm x hxR x' hx'R' hx2 hx1 hx'2 hx'1 c hc hcc
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  exact sp4_twin_sq_false h2 ((fund_iff_isLongRootSp2 hadm h2 R).mp hR)
    ((fund_iff_isLongRootSp2 hadm h2 R').mp hR') hne hcomm hxR hx2 hx1 hx'R' hx'2 hx'1 hc hcc

theorem psl4_twin_no_sq3 :
    ∀ R ∈ ModelFund 3 .PSL 4 1, ∀ R' ∈ ModelFund 3 .PSL 4 1, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .PSL 4 3 1 Fact.out).K, c * c = x * x' → False := by
  intro R hR R' hR' hne hcomm x hxR x' hx'R' hx2 hx1 hx'2 hx'1 c hc hcc
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hfund := Exotic.fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := 3) (by norm_num)
  have hR1 : R ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num) := by
    rw [← hfund]
    exact hR
  have hR1' : R' ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num) := by
    rw [← hfund]
    exact hR'
  have h4 := pow_mod_four_eq_one_of_isSquare_neg_one (p := 3) (e := 1) (by norm_num) one_ne_zero
    (sl4_twin_sq h2 hR1 hR1' hne hcomm hxR hx2 hx1 hx'R' hx'2 hx'1 hc hcc)
  norm_num at h4

theorem twin_no_sq3_of_ctx {ι : Type} [Fintype ι]
    {Q : QuadraticForm (GaloisField 3 1) (ι → GaloisField 3 1)} {tY : StatedLieTag} {nY : ℕ}
    {D : UniversalRootDatum (spinGroup Q)}
    (hM : modelUniv tY nY 3 1 Fact.out = ⟨spinGroup Q, D⟩)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    (hperf : Group.IsPerfect (spinGroup Q)) (hZ : CenterScalar Q)
    (hV : 7 ≤ Module.finrank (GaloisField 3 1) (ι → GaloisField 3 1))
    (hV4 : ¬ 4 ∣ Module.finrank (GaloisField 3 1) (ι → GaloisField 3 1) - 2)
    {Z' : Subgroup ((ι → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (ι → GaloisField 3 1))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups tY D) (fundSet Q) Z') :
    ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Fact.out).D,
      ∀ R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Fact.out).D, R ≠ R' → Commutes R R' →
        ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
          ∀ c ∈ Subgroup.center (modelUniv tY nY 3 1 Fact.out).K, c * c = x * x' → False := by
  generalize modelUniv tY nY 3 1 Fact.out = M at hM ⊢
  subst hM
  have := hperf
  exact spin_family_twin_no_sq3 Q3W.odd_gf3 hQ hrange hZ hV hV4 cq

theorem spinOdd_twin_no_sq3 :
    ∀ R ∈ ModelFund 3 .POmegaOdd 3 1, ∀ R' ∈ ModelFund 3 .POmegaOdd 3 1, R ≠ R' →
      Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .POmegaOdd 3 3 1 Fact.out).K, c * c = x * x' → False := by
  have hn3 : 3 ≤ 3 := le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  exact twin_no_sq3_of_ctx (tY := .POmegaOdd) (nY := 3) (D := oddDatum 3 (GaloisField 3 1)) rfl
    (nondegenerate_polarBilin_quadOdd 3 _ h2) (range_spinAction_quadOdd h2 hn3)
    (isPerfect_spinGroup_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega)
    (by rw [hdim]; decide) (Q3TWY.centralQuot3_odd hn3)

theorem spinMinus_twin_no_sq3 (hadm : StatedLieAdmissible .POmegaMinus 4 3 1) :
    ∀ R ∈ ModelFund 3 .POmegaMinus 4 1, ∀ R' ∈ ModelFund 3 .POmegaMinus 4 1, R ≠ R' →
      Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .POmegaMinus 4 3 1 Fact.out).K,
          c * c = x * x' → False := by
  have hn4 : 4 ≤ 4 := le_rfl
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  exact twin_no_sq3_of_ctx (tY := .POmegaMinus) (nY := 4)
    (D := Twisted.minusDatum 4 (minusCoeffs_irr 3 1)) rfl
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr 3 1))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1))
    (isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr 3 1))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) (by omega) (by rw [hdim]; decide)
    (Q3TY.centralQuot3_minus hadm)

theorem spinPlus_twin_no_sq3 :
    ∀ R ∈ ModelFund 3 .POmegaPlus 4 1, ∀ R' ∈ ModelFund 3 .POmegaPlus 4 1, R ≠ R' →
      Commutes R R' → ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .POmegaPlus 4 3 1 Fact.out).K, c * c = x * x' →
          False := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  have hdim : Module.finrank (GaloisField 3 1) (Fin 4 ⊕ Fin 4 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  exact twin_no_sq3_of_ctx (tY := .POmegaPlus) (nY := 4) (D := plusDatum 4 (GaloisField 3 1) hn3)
    (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3) (nondegenerate_polarBilin_quadPlus 4 _)
    (range_spinAction_quadPlus hn3) (isPerfect_spinGroup_quadPlus hn3) (centerScalar_quadPlus hn3)
    (by omega) (by rw [hdim]; decide) (Q3TY.centralQuot3_plus hn4)

end Rows

theorem twinSquareFact3_rows : TwinSquareFact3 := by
  intro t k e he hadm htag R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 _ hc
  subst he
  obtain ⟨c, hcZ, hcc⟩ := hc
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (psp2_twin_no_sq3 hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hcZ
      hcc).elim
  · exact (psl4_twin_no_sq3 R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hcZ hcc).elim
  · exact ⟨rfl, rfl⟩
  · exact (spinOdd_twin_no_sq3 R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hcZ
      hcc).elim
  · exact (spinPlus_twin_no_sq3 R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hcZ
      hcc).elim
  · exact (spinMinus_twin_no_sq3 hadm R hR R' hR' hne hcomm x hx x' hx' hx2 hx1 hx'2 hx'1 c hcZ
      hcc).elim

end CFSG.ClassicalInvolution.Q3.Q3T7S23
