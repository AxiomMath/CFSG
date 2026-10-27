module

public import CFSG.ClassicalInvolution.Asc77.AscT7OL
public import CFSG.ClassicalInvolution.Asc77.AscT7JSq

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15.T7O
open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

section Transport

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}


theorem twinSqAlphaOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinSqAlphaOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair k hk hkk v hvR hvR' hvv
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hpair.mem r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hpair.mem' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  obtain ⟨F₁, -, -, hθx, hθx'⟩ := swap_of_twin_pair hodd hrange hZ hproj (hperf R hpair.mem)
    (hperf R' hpair.mem') (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne hpair.hx
    hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 ψ hpair.ker hpair.same
  have hord : spinAction Q x = spinAction Q x' := by rw [hθx, hθx', F₁.La_swap_neg_one]
  exact alphaOf_spin_twin_pair_sq hodd h5 hQ hrange hV (hperf R hpair.mem) (hperf R' hpair.mem')
    (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne hpair.hx hpair.hx2 hpair.hx1
    hpair.hx' hpair.hx'2 hpair.hx'1 hord hpair.ker
    (CFSG.ClassicalInvolution.G2D4Models.Twin.LiftSim.liftSimFr (hlift H ψ hpair.ker)) hk hkk v hvR
    hvR' hvv

end Transport

section Families

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

variable {p e : ℕ} [Fact p.Prime]

theorem twinSqAlpha_plus_ge5 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn5 : 5 ≤ n) :
    TwinSqAlpha p e .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have : Group.IsPerfect (spinGroup (quadPlus n (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := n) trivial hadm
    (by simp)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, R ≤ ⁅R, R⁆) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
        TwinSqAlphaOn .POmegaPlus M := by
    intro M hM hperf hnc
    subst hM
    refine twinSqAlphaOn_of_spin hodd (five_le_card_galoisField hq)
      (nondegenerate_polarBilin_quadPlus n _) (range_spinAction_quadPlus hn3)
      (centerScalar_quadPlus hn3) (by omega) (fun F₁ F₂ h => ?_)
      (fun H _ _ ψ hψ => liftSim_quadPlus hp2 hn5 he ψ hψ) _
      (fundCorr_plus hp2 hq hn4).1 hperf hnc
    have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hperf hnc

theorem twinSqAlpha_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) : TwinSqAlpha p e .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := n) trivial
    hadm (by simp)
  show TwinSqAlphaOn .POmegaMinus ⟨spinGroup (quadMinus n (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum n (minusCoeffs_irr p e)⟩
  exact twinSqAlphaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fun H _ _ ψ hψ => liftSim_quadMinus hp2 hn4 he ψ hψ) _ (fundCorr_minus hp2 hq hadm).1
    hperf hnc

end Families

end CFSG.ClassicalInvolution.Asc77
