module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPMinSq
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd
public import CFSG.ClassicalInvolution.RouteD.TWZSpinMinus
public import CFSG.ClassicalInvolution.RouteD.TWT4Rank

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.Q3 (CompData)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups

@[expose] def SqCountC (c : CompData) (B : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (θ : c.G →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center c.G →
    ∀ (R R' : Subgroup c.G), R ∈ c.fund → R' ∈ c.fund → R ≠ R' →
      ∀ (x x' : c.G), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' →
        ∀ α : MulAut X, α * α * (α * α) = 1 → (∀ r ∈ R, α (θ r) = θ r) →
          (∀ r ∈ R', α (θ r) = θ r) →
          α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
            B < Nat.card {S : Subgroup c.G // S ∈ c.fund ∧ ∀ r ∈ S, (α * α) (θ r) = θ r}


theorem sqCountC_minus4 : SqCountC (CompData.model .POmegaMinus 4) 2160 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  have he : 1 ≤ 1 := le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr 3 1)
  have hZ3 : ∀ c ∈ Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf c :=
    (Q3W.powCop3_model (t := .POmegaMinus) (n := 4) trivial hadm (by decide) (by decide)).cop
  have hcard : Nat.card (GaloisField 3 1) = 3 := Q3W.card_gf3
  show SqCountC ⟨spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2), GFund .POmegaMinus
      (Twisted.minusDatum 4 (minusCoeffs_irr 3 1))⟩ 2160
  intro X _ θ hθs hθk R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR'
  rcases spin_sq_count3 Q3W.odd_gf3 hcard
      (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr 3 1))
      (range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1))
      (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) hZ3 (by omega) (by omega)
      (fun F₁ F₂ h => TG3.false_of_orth_quadMinus_four3 h2 (minusCoeffs_irr 3 1)
        (by rw [hcard]; norm_num) F₁ F₂ (span_le_perp_of_proj h2 F₁ F₂ h))
      hθs hθk (liftSim_quadMinus hp2 hn4 he θ hθk) (Q3TY.centralQuot3_minus hadm) hR hR' hne
      hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR' with h | h | ⟨X', hnd, hdimX, hN⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ?_)
  set Q₈ := quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2 with hQ₈
  set N := Nat.card {S : Subgroup (spinGroup Q₈) //
    S ∈ GFund .POmegaMinus (Twisted.minusDatum 4 (minusCoeffs_irr 3 1)) ∧
      ∀ r ∈ S, (α * α) (θ r) = θ r} with hNdef
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      framesPlus 3 0 := by
    rw [NonClassical.card_o4, hcard]
    rfl
  rw [hO] at hN
  have hnd' := nondegenerate_polarBilin_restrict hnd
  have hX6 : Module.finrank (GaloisField 3 1) X' = 6 := by omega
  by_contra hle
  push Not at hle
  have hmul : N * framesPlus 3 0 ≤ 2160 * framesPlus 3 0 := Nat.mul_le_mul_right _ hle
  by_cases hP : IsPlusType (Q₈.restrict X')
  · have hf := card_frame_regular_plus hnd' (j := 1) (by omega) hP
    rw [hf, hcard] at hN
    have := arith_framesPlus (q := 3) (by norm_num)
    norm_num at this
    omega
  · have hf := card_frame_regular_minus Q3W.odd_gf3 hnd' (j := 0) (by omega) hP
    rw [hf, hcard] at hN
    have := arith_framesMinus (q := 3) (by norm_num)
    norm_num at this
    omega

end CFSG.ClassicalInvolution.Q3.Q3TIY
