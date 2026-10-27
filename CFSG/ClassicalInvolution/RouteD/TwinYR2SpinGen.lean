module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Gen
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthSide

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Perfect

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem elemOn_perfect [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {S : Submodule F V} (hS : PolarNondegOn Q S)
    (h3 : 3 ≤ Module.finrank F S) : ⁅elemOn Q S, elemOn Q S⁆ = elemOn Q S := by
  obtain ⟨𝓗, h𝓗, hcover⟩ := layerGenOn hodd h5 (nondegenerate_polarBilin_restrict hS) h3
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) (hcover.trans ?_)
  refine iSup₂_le fun H hH => ?_
  obtain ⟨hle, hq, -⟩ := h𝓗 H hH
  have hHp : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hq.1)
  calc H = ⁅H, H⁆ := hHp.symm
    _ ≤ ⁅elemOn Q S, elemOn Q S⁆ := Subgroup.commutator_mono hle hle

end Perfect

section Gen

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem elemOn_le_map_centralizer_of_fix [Finite F] [FiniteDimensional F V]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hrange : (spinAction Q).range = elementaryGroup Q) {g : spinGroup Q} {S : Submodule F V}
    (hS : PolarNondegOn Q S) (h3 : 3 ≤ Module.finrank F S)
    (hs : spinAction Q g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ y ∈ S, spinAction Q g y = y) :
    elemOn Q S ≤ (Subgroup.centralizer ({g} : Set (spinGroup Q))).map (spinAction Q) := by
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have key := le_map_fixedGroup (spinAction Q) hker (MulAut.conj g) (spinAction Q g)
    (fun y => by simp [MulAut.conj_apply, map_mul, map_inv]) (elemOn_perfect hodd h5 hS h3)
    (by rw [hrange]; exact elemOn_le_elementaryGroup)
    (fun n hn => comm_of_scalar_elemOn hs (by simp : (1 : F) * 1 = 1)
      (fun x hx => by rw [hfix x hx, one_smul]) hn)
  have hfg : CFSG.ClassicalInvolution.Balance.fixedGroup (MulAut.conj g) =
      Subgroup.centralizer ({g} : Set (spinGroup Q)) := by
    ext y
    rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup, Subgroup.mem_centralizer_singleton_iff,
      MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  rwa [hfg] at key

theorem spinGroup_eq_centralizer_sup [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    (hcomm : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r)
    {x x' a a' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    Subgroup.centralizer ({a * a'} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup Q)) = ⊤ := by
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame hodd hrange
    hZ hV hproj hRp hR'p hR hR' hnc hnc' hne hx hcx hx1 hx' hcx' hx'1 hsame ha ha' hsq hsq'
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have T := twinDatum_of_frame F₁ h2 hQ hAA hA'A' hV
  have hθu : spinAction Q (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have hxu : x * (a * a') = (a * a') * x := by
    have h1 : x * a = a * x := hcx a ha
    have h2' : x * a' = a' * x := hcomm x hx a' ha'
    calc x * (a * a') = (x * a) * a' := by group
      _ = (a * x) * a' := by rw [h1]
      _ = a * (x * a') := by group
      _ = a * (a' * x) := by rw [h2']
      _ = (a * a') * x := by group
  have hθxu : spinAction Q (x * (a * a')) = twinInv F₁ A A' * F₁.La (-1) := by
    rw [hxu, map_mul, hθu, hθx]
  have hd3 : ∀ S : Submodule F V, F₁.perp ≤ S → 3 ≤ Module.finrank F S := fun S hS =>
    le_trans T.dW (Submodule.finrank_mono hS)
  have h₁ := elemOn_le_map_centralizer_of_fix hodd h5 hrange (g := a * a')
    T.toSplitDatum.nd_sup₂W (hd3 _ le_sup_right)
    (by rw [hθu]; exact twinInv_mem_orthogonalGroup F₁ A A')
    (fun y hy => by rw [hθu]; exact T.fix₁ y hy)
  have h₂ := elemOn_le_map_centralizer_of_fix hodd h5 hrange (g := x * (a * a'))
    T.toSplitDatum.nd_sup₁W (hd3 _ le_sup_right)
    (by rw [hθxu]; exact elementaryGroup_le_orthogonalGroup Q T.mem₂)
    (fun y hy => by rw [hθxu]; exact T.fix₂ y hy)
  have hgen := elementaryGroup_le_join_of_decomp hodd hQ T.ndW T.dW T.o₁W T.o₂W T.top
  have hE : (spinAction Q).range ≤ (Subgroup.centralizer ({a * a'} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup Q))).map (spinAction Q) := by
    rw [hrange, Subgroup.map_sup]
    exact hgen.trans (sup_le_sup h₁ h₂)
  exact eq_top_of_range_le_map (spinAction Q) hker hE

end Gen

section Spin

open CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem twinMFGenerationOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinMFGenerationOn t ⟨spinGroup Q, D⟩ := by
  intro R R' x x' hd a ha a' ha' hsq hsq' S _
  have h := spinGroup_eq_centralizer_sup hodd h5 hQ hrange hZ hV hproj (hperf R hd.mem)
    (hperf R' hd.mem') (hcorr R hd.mem) (hcorr R' hd.mem') (hnc R hd.mem) (hnc R' hd.mem')
    hd.ne hd.comm hd.hx hd.cx hd.nx hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq'
  have h2 : (⊤ : Subgroup (spinGroup Q)) ≤ Subgroup.centralizer ({x} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({a * a'} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup Q)) := by
    rw [← h]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  exact le_top.trans h2

end Spin

end CFSG.ClassicalInvolution.RouteD.TwinY
