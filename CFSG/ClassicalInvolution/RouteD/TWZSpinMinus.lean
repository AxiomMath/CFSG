module

public import CFSG.ClassicalInvolution.RouteD.TWZSpinCount
public import CFSG.ClassicalInvolution.RouteD.TWZSpinModel
public import CFSG.ClassicalInvolution.RouteD.TwinYR3Classify
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthStd
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.TwinY
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups

section Statement

@[expose] def SqCountOn (t : StatedLieTag) (M : LieUniversal) (B : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (θ : M.K →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center M.K →
    ∀ (R R' : Subgroup M.K), R ∈ GFund t M.D → R' ∈ GFund t M.D → R ≠ R' →
      ∀ (x x' : M.K), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' →
        ∀ α : MulAut X, α * α * (α * α) = 1 → (∀ r ∈ R, α (θ r) = θ r) →
          (∀ r ∈ R', α (θ r) = θ r) →
          α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
            B < Nat.card {S : Subgroup M.K // S ∈ GFund t M.D ∧
              ∀ r ∈ S, (α * α) (θ r) = θ r}

end Statement

section Arith

theorem arith_framesPlus {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 4 - 1) * q ^ 3) * framesPlus q 0 < 2 * framesPlus q 1 := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold framesPlus
  norm_num
  zify [h1, h2, h3, h4]
  have hx : (1 : ℤ) < q := by exact_mod_cast hq
  have a1 : (0 : ℤ) < (q : ℤ) ^ 4 - 1 := by
    have := one_lt_pow₀ hx (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  have a2 : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by
    have := one_lt_pow₀ hx (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have a3 : (0 : ℤ) < (q : ℤ) ^ 5 := pow_pos (by linarith) 5
  have a4 : (0 : ℤ) < (q : ℤ) ^ 3 + q + 1 := by positivity
  have hP := mul_pos (mul_pos (mul_pos (mul_pos (two_pos : (0 : ℤ) < 2) a3) a1) a2) a4
  nlinarith [hP]

theorem arith_framesMinus {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 4 - 1) * q ^ 3) * framesPlus q 0 < 2 * framesMinus q 0 := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold framesPlus framesMinus
  norm_num
  zify [h1, h2, h3, h4]
  have hx : (1 : ℤ) < q := by exact_mod_cast hq
  have a1 : (0 : ℤ) < (q : ℤ) ^ 4 - 1 := by
    have := one_lt_pow₀ hx (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  have a2 : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by
    have := one_lt_pow₀ hx (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have a3 : (0 : ℤ) < (q : ℤ) ^ 5 := pow_pos (by linarith) 5
  have a4 : (0 : ℤ) < (q : ℤ) * ((q : ℤ) - 1) ^ 2 + 1 := by positivity
  have hP := mul_pos (mul_pos (mul_pos (mul_pos (two_pos : (0 : ℤ) < 2) a3) a1) a2) a4
  nlinarith [hP]

end Arith

section Transport

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem sqCountOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : Module.finrank F (ι → F) = 8)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ GFund t D, R.map (spinAction Q) ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ GFund t D, R.map (spinAction Q) = L)
    (hperf : ∀ R ∈ GFund t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ GFund t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) {B : ℕ}
    (hcount : ∀ X' : Submodule F (ι → F), PolarNondegOn Q X' →
      Module.finrank F X' + 2 = Module.finrank F (ι → F) → ∀ N : ℕ,
        N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
          2 * Nat.card (OFrame (Q.restrict X')) → B < N) :
    SqCountOn t ⟨spinGroup Q, D⟩ B := by
  intro X _ θ hθs hθk R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR'
  have hinj : ∀ {S : Subgroup (spinGroup Q)}, S ∈ GFund t D →
      ∀ r ∈ S, spinAction Q r = 1 → r = 1 := fun {S} hS =>
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center (ker_spinAction_le_center Q)
      fun r hr hcen => hnc S hS r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  rcases spin_sq_count hodd h5 hQ hrange hZ (by omega) hV.le hproj hθs hθk (hlift X θ hθk)
    (hperf R hR) (hperf R' hR') (hcorr R hR) (hcorr R' hR') (hinj hR) (hinj hR') hne hx hx2 hx1
    hx' hx'2 hx'1 hxx' α hα4 hαR hαR' D hperf hcorr hsurj with h | h | ⟨X', hnd, hdim, hN⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hcount X' hnd hdim _ hN))

end Transport

section Minus

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Models.Transfer

set_option linter.unusedSectionVars false

variable {p e : ℕ} [Fact p.Prime]


theorem sqCount_minus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    SqCountOn .POmegaMinus
      (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaMinus 4 p e Fact.out)
      (((p ^ e) ^ 4 - 1) * (p ^ e) ^ 3) := by
  have hn4 : 4 ≤ 4 := le_rfl
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := 4) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := 4) trivial
    hadm (by simp)
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hq2 : 2 ≤ p ^ e := by omega
  show SqCountOn .POmegaMinus ⟨spinGroup (quadMinus 4 (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum 4 (minusCoeffs_irr p e)⟩ _
  refine sqCountOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) hdim
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fun H _ ψ hψ => liftSim_quadMinus hp2 hn4 he ψ hψ) _ (fundCorr_minus hp2 hq hadm).1
    (fundCorr_minus hp2 hq hadm).2 hperf hnc ?_
  intro X' hnd hdimX N hN
  set Q₈ := quadMinus 4 (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2 with hQ₈
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (detQ (K := GaloisField p e))) = framesPlus (p ^ e) 0 := by
    rw [NonClassical.card_o4, hcard]
    rfl
  rw [hO] at hN
  have hnd' := nondegenerate_polarBilin_restrict hnd
  have hX6 : Module.finrank (GaloisField p e) X' = 6 := by omega
  by_contra hle
  push Not at hle
  have hmul : N * framesPlus (p ^ e) 0 ≤ ((p ^ e) ^ 4 - 1) * (p ^ e) ^ 3 * framesPlus (p ^ e) 0 :=
    Nat.mul_le_mul_right _ hle
  by_cases hP : IsPlusType (Q₈.restrict X')
  · have hf := card_frame_regular_plus hnd' (j := 1) (by omega) hP
    rw [hf, hcard] at hN
    have := arith_framesPlus hq2
    omega
  · have hf := card_frame_regular_minus hodd hnd' (j := 0) (by omega) hP
    rw [hf, hcard] at hN
    have := arith_framesMinus hq2
    omega

end Minus

end CFSG.ClassicalInvolution.RouteD.TWZ
