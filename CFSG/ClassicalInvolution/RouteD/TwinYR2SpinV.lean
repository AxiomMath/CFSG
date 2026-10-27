module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinGen
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinRestrict

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Eigen

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem span_le_plusSp_of_commute (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {u : V ≃ₗ[F] V}
    (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hu2 : u * u = 1)
    (hcomm : ∀ A : SL(2, F), u * fr.La A = fr.La A * u) (hneg : ¬ fr.span ≤ minusSp u) :
    fr.span ≤ plusSp u := by
  have hLneg : u * fr.La (-1) = fr.La (-1) * u := hcomm (-1)
  have hinc : ∀ Y, fr.incl (fr.transport u Y) = u (fr.incl Y) := fun Y =>
    Frame.incl_transport h2 hLneg Y
  have hT : ∀ (A : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F),
      fr.transport u ((A : Matrix (Fin 2) (Fin 2) F) * X) =
        (A : Matrix (Fin 2) (Fin 2) F) * fr.transport u X := by
    intro A X
    have h1 : u (fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * X)) =
        fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * fr.transport u X) := by
      rw [← Frame.La_apply_incl, ← Frame.La_apply_incl, hinc X]
      exact LinearEquiv.congr_fun (hcomm A) (fr.incl X)
    rw [Frame.transport_apply, h1, Frame.coords_incl]
  have hT2 : ∀ X, fr.transport u (fr.transport u X) = X := by
    intro X
    rw [Frame.transport_apply, hinc X]
    have : u (u (fr.incl X)) = fr.incl X := by
      have := LinearEquiv.congr_fun hu2 (fr.incl X)
      simpa using this
    rw [this, Frame.coords_incl]
  have hdet : ∀ X, (fr.transport u X).det = X.det := by
    intro X
    rw [← Frame.Q_incl fr (fr.transport u X), hinc X, map_of_mem hu (fr.incl X),
      Frame.Q_incl fr X]
  rcases eq_one_or_eq_neg_one_of_commute_left h2 hT hT2 hdet with h | h
  · rintro _ ⟨X, rfl⟩
    rw [mem_plusSp, ← hinc, h]
    rfl
  · exfalso
    apply hneg
    rintro _ ⟨X, rfl⟩
    rw [mem_minusSp, ← hinc, h]
    simp

theorem minusSp_le_span [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (fr : OFrame Q)
    {u : V ≃ₗ[F] V} (hperp : ∀ x ∈ fr.perp, u x = x) (hspan : ∀ x ∈ fr.span, u x ∈ fr.span)
    (hne : ∃ x ∈ fr.span, x ≠ 0 ∧ u x = x) :
    minusSp u ≤ fr.span ∧ Module.finrank F (minusSp u) < 4 := by
  have hle : minusSp u ≤ fr.span := by
    intro v hv
    obtain ⟨x, hxs, y, hyp, hvxy⟩ : ∃ x ∈ fr.span, ∃ y ∈ fr.perp, v = x + y :=
      ⟨fr.incl (fr.coords v), ⟨_, rfl⟩, v - fr.incl (fr.coords v), by
        rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self], by abel⟩
    subst hvxy
    have huv : u (x + y) = -(x + y) := mem_minusSp.mp hv
    have h1 : u x + x = (-2 : F) • y := by
      have h3 := huv
      rw [map_add, hperp y hyp] at h3
      have h4 : u x = -(x + y) - y := eq_sub_of_add_eq h3
      rw [h4]
      module
    have hmem1 : u x + x ∈ fr.span := fr.span.add_mem (hspan x hxs) hxs
    have hmem2 : (-2 : F) • y ∈ fr.perp := fr.perp.smul_mem _ hyp
    have hz : (-2 : F) • y = 0 := by
      have hdis := (Frame.isCompl_span_perp fr).disjoint
      rw [Submodule.disjoint_def] at hdis
      exact hdis _ (h1 ▸ hmem1) hmem2
    have hy0 : y = 0 := by
      have : (-2 : F) ≠ 0 := neg_ne_zero.mpr h2
      exact (smul_eq_zero.mp hz).resolve_left this
    rw [hy0, add_zero]
    exact hxs
  refine ⟨hle, ?_⟩
  by_contra hge
  push Not at hge
  have h4 : Module.finrank F (minusSp u) = 4 :=
    le_antisymm (by rw [← Frame.finrank_span fr]; exact Submodule.finrank_mono hle) hge
  have heq : minusSp u = fr.span :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h4, Frame.finrank_span])
  obtain ⟨x, hxs, hx0, hux⟩ := hne
  have := mem_minusSp.mp (heq ▸ hxs)
  rw [hux] at this
  have h2x : (2 : F) • x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [this]
    exact neg_add_cancel x
  exact hx0 ((smul_eq_zero.mp h2x).resolve_left h2)

end Eigen

section Main

open CFSG.ClassicalInvolution.Generic (conjSub Commutes mem_conjSub_iff conj_mem_conjSub)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem commutes_La_range {fr fr' : OFrame Q} (h : ∀ X Y, polar Q (fr.incl X) (fr'.incl Y) = 0) :
    Commutes fr.La.range fr'.La.range := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact LinearEquiv.ext fun x => LinearEquiv.congr_fun (Frame.La_comm_of_orth h A B) x

theorem spinGroup_mfV [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 9 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' a a' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) {S : Subgroup (spinGroup Q)}
    (hS : S.map (spinAction Q) ∈ fundSet Q) (hSp : S ≤ ⁅S, S⁆)
    (hSc : ∀ s ∈ S, (a * a') * s = s * (a * a')) :
    ∃ g : spinGroup Q, g * (a * a') = (a * a') * g ∧ Commutes (conjSub g S) R ∧
      Commutes (conjSub g S) R' := by
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame hodd hrange
    hZ (by omega) hproj hRp hR'p hR hR' hnc hnc' hne hx hcx hx1 hx' hcx' hx'1 hsame ha ha' hsq hsq'
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have T := twinDatum_of_frame F₁ h2 hQ hAA hA'A' (by omega)
  have hθu : spinAction Q (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have huO : twinInv F₁ A A' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    twinInv_mem_orthogonalGroup F₁ A A'
  have hu2 : twinInv F₁ A A' * twinInv F₁ A A' = 1 :=
    LinearEquiv.ext fun v => twinInv_twinInv F₁ hAA hA'A' v
  obtain ⟨iS, FS, hFS, -⟩ := hS
  have hcommS : ∀ B : SL(2, F), twinInv F₁ A A' * FS.La B = FS.La B * twinInv F₁ A A' := by
    intro B
    have hmem : FS.La B ∈ S.map (spinAction Q) := hFS ▸ ⟨B, rfl⟩
    obtain ⟨s, hs, hsB⟩ := hmem
    rw [← hsB, ← hθu, ← map_mul, ← map_mul, hSc s hs]
  obtain ⟨hMle, hMlt⟩ := minusSp_le_span h2 F₁ (fun x hx => twinInv_perp F₁ A A' hx)
    (fun x hx => twinInv_mem_span F₁ hx) (by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot T.ne₂
      obtain ⟨hvs, huv⟩ := mem_eigIn_iff.mp hv
      exact ⟨v, hvs, hv0, by rw [huv, one_smul]⟩)
  have hneg : ¬ FS.span ≤ minusSp (twinInv F₁ A A') := by
    intro h
    have := Submodule.finrank_mono h
    rw [Frame.finrank_span] at this
    omega
  have hFSplus := span_le_plusSp_of_commute h2 FS huO hu2 hcommS hneg
  have hW : PolarNondegOn Q F₁.perp := CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ F₁
  have hWdim : 5 ≤ Module.finrank F F₁.perp := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₁
    omega
  obtain ⟨F', hF'⟩ := CFSG.ClassicalInvolution.Asc77.exists_frame_le_of_five_le hodd hQ hW hWdim
  have hV₁nd : PolarNondegOn Q (plusSp (twinInv F₁ A A')) :=
    CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hu2)
      (fun x hx y hy => polar_plusSp_minusSp h2 huO hx hy)
  have hV₁dim : 6 ≤ Module.finrank F (plusSp (twinInv F₁ A A')) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_plusSp_minusSp h2 hu2)
    omega
  have hF'plus : F'.span ≤ plusSp (twinInv F₁ A A') := fun y hy =>
    mem_plusSp.mpr (twinInv_perp F₁ A A' (hF' hy))
  obtain ⟨h, hh, hconj⟩ := exists_elemOn_conj hodd hV₁nd hV₁dim hFSplus hF'plus
  have hlift := elemOn_le_map_centralizer_of_fix hodd h5 hrange (g := a * a')
    hV₁nd (by omega) (by rw [hθu]; exact huO) (fun y hy => by rw [hθu]; exact mem_plusSp.mp hy)
  obtain ⟨g, hg, hgh⟩ := hlift hh
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mp hg, ?_⟩
  have hconjS : (conjSub g S).map (spinAction Q) = F'.La.range := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hs : g⁻¹ * w * g ∈ S := mem_conjSub_iff.mp hw
      have hs' : spinAction Q (g⁻¹ * w * g) ∈ FS.La.range := hFS ▸ Subgroup.mem_map_of_mem _ hs
      obtain ⟨B, hB⟩ := hs'
      refine ⟨B, ?_⟩
      calc F'.La B = h * FS.La B * h⁻¹ := hconj B
        _ = h * spinAction Q (g⁻¹ * w * g) * h⁻¹ := by rw [hB]
        _ = spinAction Q g * spinAction Q (g⁻¹ * w * g) * (spinAction Q g)⁻¹ := by rw [hgh]
        _ = spinAction Q (g * (g⁻¹ * w * g) * g⁻¹) := by simp only [map_mul, map_inv]
        _ = spinAction Q w := by congr 1; group
    · rintro ⟨B, rfl⟩
      have hs' : FS.La B ∈ S.map (spinAction Q) := hFS ▸ ⟨B, rfl⟩
      obtain ⟨s, hs, hsB⟩ := hs'
      refine ⟨g * s * g⁻¹, conj_mem_conjSub hs, ?_⟩
      rw [hconj B, map_mul, map_mul, map_inv, hgh, hsB]
  have hSS : ⁅S, S⁆ = S := le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hSp
  have hperfL : ⁅conjSub g S, conjSub g S⁆ = conjSub g S := by
    unfold conjSub
    rw [← Subgroup.map_commutator, hSS]
  have hperpF : ∀ (X Y : Matrix (Fin 2) (Fin 2) F), polar Q (F'.incl X) (F₁.incl Y) = 0 :=
    fun X Y => (Frame.mem_perp_iff_forall_incl F₁).mp (hF' ⟨X, rfl⟩) Y
  refine ⟨?_, ?_⟩
  · rw [← CFSG.ClassicalInvolution.RouteD.Gaps.commutes_map_iff hker hperfL, hconjS, hF₁]
    exact commutes_La_range hperpF
  · rw [← CFSG.ClassicalInvolution.RouteD.Gaps.commutes_map_iff hker hperfL, hconjS, hF₁']
    refine commutes_La_range (fun X Y => ?_)
    have hY : F₁.swap.incl Y ∈ F₁.span := by
      rw [← Frame.span_eq_swap_span]
      exact ⟨Y, rfl⟩
    obtain ⟨Y', hY'⟩ := hY
    rw [← hY']
    exact hperpF X Y'

end Main

section Spin

open CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem twinMFCentralizingOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 9 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinMFCentralizingOn t ⟨spinGroup Q, D⟩ := by
  intro R R' x x' hd a ha a' ha' hsq hsq' S hS hSc
  exact spinGroup_mfV hodd h5 hQ hrange hZ hV hproj (hperf R hd.mem) (hperf R' hd.mem')
    (hcorr R hd.mem) (hcorr R' hd.mem') (hnc R hd.mem) (hnc R' hd.mem') hd.ne hd.hx hd.cx hd.nx
    hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq' (hcorr S hS) (hperf S hS) hSc

end Spin

end CFSG.ClassicalInvolution.RouteD.TwinY
