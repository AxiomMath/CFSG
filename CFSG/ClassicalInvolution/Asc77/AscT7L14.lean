module

public import CFSG.ClassicalInvolution.Asc77.AscT7L13
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

@[expose] def TwinCentralOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ R ∈ fundamentalSubgroups t M.D, ∀ R' ∈ fundamentalSubgroups t M.D, R ≠ R' → Commutes R R' →
    ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
      x * x' ∈ Subgroup.center M.K →
      ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
        ∃ R'' ∈ fundamentalSubgroups t M.D, ∀ r ∈ R'', (a * b) * r = r * (a * b)

namespace T7L

section Spin

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem twinCentralOn_of_spin [Group.IsPerfect (spinGroup Q)] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q)
    (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : (∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q) ∧
      ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinCentralOn t ⟨spinGroup Q, D⟩ := by
  classical
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hR r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hR' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hsame : (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) x =
      (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) x' := by
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨x * x', hxx', by rw [← mul_assoc, hx2, one_mul]⟩
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := swap_of_twin_pair hodd hrange hZ hproj (hperf R hR)
    (hperf R' hR') (hcorr.1 R hR) (hcorr.1 R' hR') hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1
    (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) (by simp) hsame
  exact exists_fund_comm_ab_of_frame hodd hQ hV D hcorr.2 hperf (ker_spinAction_le_center Q) F₁
    hF₁ hF₁' hθx hθx' ha haa hb hbb

omit [DecidableEq ι] in
theorem exists_fund_comm_ab_of_ord [Group.IsPerfect (spinGroup Q)] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hV : 7 ≤ Module.finrank F (ι → F)) {t : StatedLieTag}
    (D : UniversalRootDatum (spinGroup Q))
    (hcorr : (∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q) ∧
      ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    {R R' : Subgroup (spinGroup Q)} (hR : R ∈ fundamentalSubgroups t D)
    (hR' : R' ∈ fundamentalSubgroups t D) (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') {a b : spinGroup Q} (ha : a ∈ R) (haa : a * a = x)
    (hb : b ∈ R') (hbb : b * b = x') :
    ∃ R'' ∈ fundamentalSubgroups t D, ∀ r ∈ R'', (a * b) * r = r * (a * b) := by
  classical
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hR r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hR' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := G2D4Models.Twin.swap_of_twin_pair_ord hodd (hperf R hR)
    (hperf R' hR')
    (hcorr.1 R hR) (hcorr.1 R' hR') hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1 hord
  exact exists_fund_comm_ab_of_frame hodd hQ hV D hcorr.2 hperf (ker_spinAction_le_center Q) F₁
    hF₁ hF₁' hθx hθx' ha haa hb hbb

theorem exists_mem_map_eq {K : Type} [Group K] [Finite K] (S : Set (Subgroup K)) (σ : K ≃* K)
    (hσ : ∀ R ∈ S, R.map σ.toMonoidHom ∈ S) {T : Subgroup K} (hT : T ∈ S) :
    ∃ R ∈ S, R.map σ.toMonoidHom = T := by
  have hmaps : Set.MapsTo (fun R : Subgroup K => R.map σ.toMonoidHom) S S := fun R hR => hσ R hR
  have hinj : Set.InjOn (fun R : Subgroup K => R.map σ.toMonoidHom) S := fun R _ R' _ h =>
    Subgroup.map_injective σ.injective h
  have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite S) hmaps).mp hinj
  obtain ⟨R, hR, hRT⟩ := hbij.surjOn hT
  exact ⟨R, hR, hRT⟩

end Spin

section Rows

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic

variable (p : ℕ) [Fact p.Prime]

theorem twinCentralSpin7 : TwinCentralSpin7 p := by
  intro e hadm hp2 hq
  have hn3 : 3 ≤ 3 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) =
      2 * 3 + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := 3) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := 3) trivial hadm
    (by simp)
  show TwinCentralOn .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField p e)),
    oddDatum 3 (GaloisField p e)⟩
  refine twinCentralOn_of_spin hodd (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega)
    (fun F₁ F₂ h => ?_) _ (fundCorr_odd hp2 hq hadm) hperf hnc
  have := finrank_eq_eight_of_proj hodd F₁ F₂ h
  omega

theorem twinCentralD4M : TwinCentralD4M p := by
  intro e hadm hp2 hq
  have hn4 : 4 ≤ 4 := le_rfl
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := 4) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := 4) trivial
    hadm (by simp)
  show TwinCentralOn .POmegaMinus ⟨spinGroup (quadMinus 4 (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum 4 (minusCoeffs_irr p e)⟩
  exact twinCentralOn_of_spin hodd
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h) _ (fundCorr_minus hp2 hq hadm) hperf hnc

theorem twinCentralD4P : TwinCentralD4P p := by
  intro e hadm hp2 hq
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := e) (by omega)
  obtain ⟨ρ, hρ⟩ := G2D4Models.Twin.exists_triality hadm h4 hF
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p e) hn3),
      R ≤ ⁅R, R⁆ :=
    Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := 4) (e := e) trivial hadm (by omega)
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p e) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p e))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := 4) trivial hadm
      (by simp)
  have hcorr := Exotic.fundCorr_plus hp2 hq (le_refl 4)
  have hfin : Finite (spinGroup (quadPlus 4 (GaloisField p e))) :=
    (CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (t := .POmegaPlus) (n := 4) (e := e) hp2
      Fact.out trivial hadm : Finite (modelUniv .POmegaPlus 4 p e Fact.out).K)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
      plusDatum 4 (GaloisField p e) hn3⟩ → TwinCentralOn .POmegaPlus M := by
    intro M hM
    subst hM
    intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
    have hxinv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    have hcom' : x * x' = x' * x := hcomm x hx x' hx'
    have hc : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p e))) := by
      rw [hxinv]
      exact hxx'
    have hc2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
      rw [hxinv]
      calc x * x' * (x * x') = x * (x' * x) * x' := by group
        _ = x * (x * x') * x' := by rw [hcom']
        _ = (x * x) * (x' * x') := by group
        _ = 1 := by rw [hx2, hx'2, one_mul]
    obtain ⟨σ, hσ, hθ⟩ := G2D4Models.Twin.exists_aut_ordinary hp2 hadm ρ hρ hc hc2
    have hord : spinAction (quadPlus 4 (GaloisField p e)) (σ x) =
        spinAction (quadPlus 4 (GaloisField p e)) (σ x') := by
      rw [map_mul, map_inv, map_mul, map_inv] at hθ
      exact mul_inv_eq_one.mp hθ
    have hneσ : R.map σ.toMonoidHom ≠ R'.map σ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective σ.injective h)
    obtain ⟨R'', hR'', hcomm''⟩ := exists_fund_comm_ab_of_ord hodd
      (nondegenerate_polarBilin_quadPlus 4 _) (by omega) _ hcorr hperf hnc (hσ R hR)
      (hσ R' hR') hneσ (x := σ x) (x' := σ x') ⟨x, hx, rfl⟩ (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (σ.injective (by rw [h, map_one]))) ⟨x', hx', rfl⟩
      (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (σ.injective (by rw [h, map_one]))) hord (a := σ a) (b := σ b)
      ⟨a, ha, rfl⟩ (by rw [← map_mul, haa]) ⟨b, hb, rfl⟩ (by rw [← map_mul, hbb])
    obtain ⟨S, hS, hSσ⟩ := exists_mem_map_eq _ σ hσ hR''
    refine ⟨S, hS, fun s hs => ?_⟩
    apply σ.injective
    have := hcomm'' (σ s) (hSσ ▸ Subgroup.mem_map_of_mem _ hs)
    simpa only [map_mul] using this
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3)

end Rows

end T7L

end CFSG.ClassicalInvolution.Asc77
