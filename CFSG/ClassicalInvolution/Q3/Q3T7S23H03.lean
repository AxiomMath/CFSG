module

public import CFSG.ClassicalInvolution.Asc77.AscT7L12
public import CFSG.ClassicalInvolution.Asc77.AscT7L14
public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Ord
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Generic (modelUniv)


theorem exists_omega_three : ∃ ω : GaloisField 3 (2 * 1), ω * ω = -1 ∧
    unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 ω = -ω := by
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have : Fintype (GaloisField 3 (2 * 1)) := Fintype.ofFinite _
  obtain ⟨ω, hω⟩ : ∃ ω : GaloisField 3 (2 * 1), ω * ω = -1 := by
    have hsq : IsSquare (-1 : GaloisField 3 (2 * 1)) := by
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
      norm_num
    obtain ⟨ω, hω⟩ := hsq
    exact ⟨ω, hω.symm⟩
  refine ⟨ω, hω, ?_⟩
  rw [unitaryInvolution_apply, pow_one]
  linear_combination ω * hω

theorem twinCentralSU3 (hadm : StatedLieAdmissible .PSU 4 3 1) : TwinCentralAt 3 .PSU 4 1 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨ω, hω, hσω⟩ := exists_omega_three
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRφ := (hφ R).mp hR
  have hR'φ := (hφ R').mp hR'
  have hneφ : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hc : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
    have hxinv : (φ x)⁻¹ = φ x := by rw [← map_inv, inv_eq_of_mul_eq_one_right hx2]
    rw [hxinv, ← map_mul, ← hcomm x hx x' hx']
    exact (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ _).mpr hxx'
  obtain ⟨R'', hR'', hcomm''⟩ := T7L.exists_longRootU_comm_ab hK hp2 hω hσω hRφ hR'φ hneφ
    (x := φ x) (x' := φ x') ⟨x, hx, rfl⟩ (by rw [← map_mul, hx2, map_one])
    (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨x', hx', rfl⟩
    (by rw [← map_mul, hx'2, map_one])
    (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc (a := φ a) (b := φ b)
    ⟨a, ha, rfl⟩ (by rw [← map_mul, haa]) ⟨b, hb, rfl⟩ (by rw [← map_mul, hbb])
  refine ⟨R''.map φ.symm.toMonoidHom, (hφ _).mpr ?_, ?_⟩
  · have : (R''.map φ.symm.toMonoidHom).map φ.toMonoidHom = R'' := by
      rw [Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
        ext y
        simp
      rw [this, Subgroup.map_id]
    rw [this]
    exact hR''
  · rintro _ ⟨r, hr, rfl⟩
    apply φ.injective
    rw [map_mul, map_mul]
    have := hcomm'' r hr
    simpa using this


section Spin


open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem exists_fund_comm_ab_of_frame3 (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hV : 7 ≤ Module.finrank F (ι → F)) {t : StatedLieTag}
    (D : UniversalRootDatum (spinGroup Q)) {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups t D) (fundSet Q) Z')
    (fr : OFrame Q) {R R' : Subgroup (spinGroup Q)}
    (hR : R.map (spinAction Q) = fr.La.range) (hR' : R'.map (spinAction Q) = fr.swap.La.range)
    {x x' a b : spinGroup Q} (hθx : spinAction Q x = fr.La (-1))
    (hθx' : spinAction Q x' = fr.swap.La (-1)) (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R')
    (hbb : b * b = x') :
    ∃ R'' ∈ fundamentalSubgroups t D, ∀ r ∈ R'', (a * b) * r = r * (a * b) := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set θ := spinAction Q with hθ
  obtain ⟨A, hA⟩ : θ a ∈ fr.La.range := hR ▸ Subgroup.mem_map_of_mem _ ha
  obtain ⟨A', hA'⟩ : θ b ∈ fr.swap.La.range := hR' ▸ Subgroup.mem_map_of_mem _ hb
  have hAA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1 := by
    have h1 : fr.La (A * A) = fr.La (-1) := by
      rw [map_mul, hA, ← map_mul, haa, hθx]
    have h3 : A * A = -1 := fr.La_injective h1
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simpa using this
  have hA'A' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1 := by
    have h1 : fr.swap.La (A' * A') = fr.swap.La (-1) := by
      rw [map_mul, hA', ← map_mul, hbb, hθx']
    have h3 : A' * A' = -1 := fr.swap.La_injective h1
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simpa using this
  obtain ⟨F'', hF''⟩ := T7L.exists_frame_fixed_by_twinInv hodd hQ hV fr hAA hA'A'
  have hu : θ (a * b) = twinInv fr A A' := by
    rw [map_mul, ← hA, ← hA']
    rfl
  obtain ⟨R'', hR'', hR''θ⟩ := cq.surj F''.La.range ⟨_, IsFundamental.of_frame F''⟩
  refine ⟨R'', hR'', ?_⟩
  have hc : ∀ g ∈ Subgroup.zpowers (a * b), ∀ l ∈ R'', θ g * θ l = θ l * θ g := by
    intro g hg l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨B, hB⟩ : θ l ∈ F''.La.range := hR''θ ▸ Subgroup.mem_map_of_mem _ hl
    have hc0 : Commute (twinInv fr A A') (F''.La B) := T7L.twinInv_commute_La h2 fr F'' hF'' B
    rw [map_zpow, hu, ← hB]
    exact (hc0.zpow_left k).eq
  exact fun r hr => Q3W.commutes_of_map_commute_exponent3 θ cq.ker_le cq.cop (cq.pow3 R'' hR'')
    hc (a * b) (Subgroup.mem_zpowers _) r hr

omit [DecidableEq ι] in
theorem exists_fund_comm_ab_of_ord3 (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hV : 7 ≤ Module.finrank F (ι → F)) {t : StatedLieTag}
    (D : UniversalRootDatum (spinGroup Q)) {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups t D) (fundSet Q) Z')
    {R R' : Subgroup (spinGroup Q)} (hR : R ∈ fundamentalSubgroups t D)
    (hR' : R' ∈ fundamentalSubgroups t D) (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') {a b : spinGroup Q} (ha : a ∈ R) (haa : a * a = x)
    (hb : b ∈ R') (hbb : b * b = x') :
    ∃ R'' ∈ fundamentalSubgroups t D, ∀ r ∈ R'', (a * b) * r = r * (a * b) := by
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := Q3TD.swap_of_twin_pair_ord3 hodd cq.cop (cq.pow3 R hR)
    (cq.pow3 R' hR') (cq.map_mem R hR) (cq.map_mem R' hR') (cq.inj R hR) (cq.inj R' hR') hne hx
    hx2 hx1 hx' hx'2 hx'1 hord
  exact exists_fund_comm_ab_of_frame3 hodd hQ hV D cq F₁ hF₁ hF₁' hθx hθx' ha haa hb hbb

theorem fund_involution_central3 (hodd : Odd (Nat.card F)) {t : StatedLieTag}
    {D : UniversalRootDatum (spinGroup Q)} {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups t D) (fundSet Q) Z')
    {R : Subgroup (spinGroup Q)} (hR : R ∈ fundamentalSubgroups t D) {x : spinGroup Q} (hx : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : ∀ r ∈ R, x * r = r * x := by
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  have hmem : spinAction Q x ∈ R.map (spinAction Q) := Subgroup.mem_map_of_mem _ hx
  have hne1 : spinAction Q x ≠ 1 := fun h => hx1 (cq.inj R hR x hx h)
  have hord : orderOf (spinAction Q x) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hx2, map_one]) hne1
  have hxi : spinAction Q x = i := hi.eq_of_orderOf_eq_two hodd hmem hord
  intro r hr
  have hcomm : i * spinAction Q r = spinAction Q r * i :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hi.le_centralizer ⟨r, hr, rfl⟩)).symm
  have h1 : x * r * (r * x)⁻¹ = 1 := by
    refine cq.inj R hR _ (R.mul_mem (R.mul_mem hx hr) (R.inv_mem (R.mul_mem hr hx))) ?_
    rw [map_mul, map_mul, map_inv, map_mul, hxi, hcomm, mul_inv_cancel]
  exact mul_inv_eq_one.mp h1

omit [DecidableEq ι] in
theorem twinCentralOn_of_spin3 (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q)
    (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (fundamentalSubgroups t D) (fundSet Q) Z') :
    TwinCentralOn t ⟨spinGroup Q, D⟩ := by
  classical
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hsame : (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) x =
      (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) x' := by
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨x * x', hxx', by rw [← mul_assoc, hx2, one_mul]⟩
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := Q3TY.swap_of_twin_pair3 hodd hrange hZ hproj
    (fun h => cq.map_inj hR hR' h) (cq.map_mem R hR) (cq.map_mem R' hR') (cq.inj R hR)
    (cq.inj R' hR') hne hx hx2 hx1 hx' hx'2 hx'1
    (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) (by simp) hsame
  exact exists_fund_comm_ab_of_frame3 hodd hQ hV D cq F₁ hF₁ hF₁' hθx hθx' ha haa hb hbb

end Spin


section Rows


open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.TwinY
open scoped MatrixGroups commutatorElement

theorem twinCentralSpin7_3 : TwinCentralAt 3 .POmegaOdd 3 1 := by
  have hn3 : 3 ≤ 3 := le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) =
      2 * 3 + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  show TwinCentralOn .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField 3 1)),
    oddDatum 3 (GaloisField 3 1)⟩
  exact twinCentralOn_of_spin3 Q3W.odd_gf3 (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega)
    (fun F₁ F₂ h => by
      have := finrank_eq_eight_of_proj Q3W.odd_gf3 F₁ F₂ h
      omega)
    _ (Q3TWY.centralQuot3_odd hn3)

theorem twinCentralD4M_3 (hadm : StatedLieAdmissible .POmegaMinus 4 3 1) :
    TwinCentralAt 3 .POmegaMinus 4 1 := by
  have hn4 : 4 ≤ 4 := le_rfl
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  show TwinCentralOn .POmegaMinus ⟨spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2), Twisted.minusDatum 4 (minusCoeffs_irr 3 1)⟩
  exact twinCentralOn_of_spin3 Q3W.odd_gf3
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr 3 1))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) (by omega)
    (fun F₁ F₂ h => CFSG.ClassicalInvolution.ModelFacts.TG3.hproj_minus (minusCoeffs_irr 3 1) hn4
      F₁ F₂ h) _ (Q3TY.centralQuot3_minus hadm)

theorem twinCentralD4P_3 : TwinCentralAt 3 .POmegaPlus 4 1 := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  have cq := Q3TY.centralQuot3_plus hn4
  have hdim : Module.finrank (GaloisField 3 1) (Fin 4 ⊕ Fin 4 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hfin : Finite (spinGroup (quadPlus 4 (GaloisField 3 1))) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField 3 1)),
      plusDatum 4 (GaloisField 3 1) hn3⟩ → TwinCentralOn .POmegaPlus M := by
    intro M hM
    subst hM
    intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
    have hxinv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    have hc : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) := by
      rw [hxinv]
      exact hxx'
    have hd : TwinDatumOn .POmegaPlus ⟨spinGroup (quadPlus 4 (GaloisField 3 1)),
        plusDatum 4 (GaloisField 3 1) hn3⟩ R R' x x' :=
      { mem := hR, mem' := hR', ne := hne, comm := hcomm, hx := hx, hx' := hx',
        cx := fund_involution_central3 Q3W.odd_gf3 cq hR hx hx2 hx1,
        cx' := fund_involution_central3 Q3W.odd_gf3 cq hR' hx' hx'2 hx'1, nx := hx1, nx' := hx'1,
        same := hc }
    obtain ⟨σ, hσ, -, hord⟩ := Q3TD.exists_ordinary_datum3 hd hx2 hx'2
    have hneσ : R.map σ.toMonoidHom ≠ R'.map σ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective σ.injective h)
    obtain ⟨R'', hR'', hcomm''⟩ := exists_fund_comm_ab_of_ord3 Q3W.odd_gf3
      (nondegenerate_polarBilin_quadPlus 4 _) (by omega) _ cq (hσ R hR) (hσ R' hR') hneσ
      (x := σ x) (x' := σ x') ⟨x, hx, rfl⟩ (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (σ.injective (by rw [h, map_one]))) ⟨x', hx', rfl⟩
      (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (σ.injective (by rw [h, map_one]))) hord (a := σ a) (b := σ b)
      ⟨a, ha, rfl⟩ (by rw [← map_mul, haa]) ⟨b, hb, rfl⟩ (by rw [← map_mul, hbb])
    obtain ⟨S, hS, hSσ⟩ := T7L.exists_mem_map_eq _ σ hσ hR''
    refine ⟨S, hS, fun s hs => ?_⟩
    apply σ.injective
    have := hcomm'' (σ s) (hSσ ▸ Subgroup.mem_map_of_mem _ hs)
    simpa only [map_mul] using this
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3)

end Rows

end CFSG.ClassicalInvolution.Q3.Q3T7S23
