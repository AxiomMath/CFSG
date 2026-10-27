module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinMinus
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.ModelFacts.CF3Spin
public import CFSG.ClassicalInvolution.Asc77.AscR10E5

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three)
open scoped MatrixGroups


section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K}

open CFSG.LieType.CurtisTits in
theorem commutingGeneration_minus3 [Finite K] (hodd : Odd (Nat.card K))
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) (k₀ : Fin (n - 1)) (hk₀ : k₀.val = 0)
    (hsingle : Generic.FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hlong : Generic.IsLongestRoot (minusDatum n hirr) (Pi.single k₀ 1))
    (hG3 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaMinus (minusDatum n hirr), Gen3 R)
    (hk3 : ∀ x ∈ (spinAction (quadMinus n K b c)).ker, x ^ 3 = 1 → x = 1) :
    CommutingGeneration (Generic.fundamentalSubgroups .POmegaMinus (minusDatum n hirr)) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ : (quadMinus n K b c).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hk : k₀.val + 1 < n - 1 := by omega
  have hij : k₀ ≠ (⟨k₀.val + 1, hk⟩ : Fin (n - 1)) := succ_ne_of_lt n hk
  have hdim : Module.finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  let fr₀ : Frame (quadMinus n K b c) := (minusFrame n b c).toHypFrame.toFrame hij true false
  have hR₀mem : rankOne (minusDatum n hirr).rootGroup k₀ ∈
      Generic.fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    ⟨1, Pi.single k₀ 1, Or.inl hlong, by ext y; simp [rankOne]⟩
  have hperp : 2 ≤ Module.finrank K fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  obtain ⟨hframe, hlift⟩ := frames_of_single_class hodd hQ
    (Generic.fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (rankOne (minusDatum n hirr).rootGroup k₀) fr₀
    (map_rankOne_minus hirr hk) hperp
    (fun y => ⟨y, Pi.single k₀ 1, Or.inl hlong, rfl⟩) (fun R hR => hsingle _ hR₀mem R hR)
  refine commutingGeneration_spin3 hodd hQ (minusFrame n b c).toHypFrame (by omega) ?_
    (isPerfect_spinGroup_quadMinus hn hirr) (range_spinAction_quadMinus hn hirr).le _ hframe hlift
    hG3 hk3
  intro v hv hQv
  have hv' : ∀ k r, polar (quadMinus n K b c) v (minusVec n k r) = 0 := hv
  rw [eq_planeVec_of_polar_minusVec n b c hv'] at hQv ⊢
  rw [quadMinus_planeVec'] at hQv
  by_contra h0
  refine planeNorm_ne_zero hirr (fun hw => h0 ?_) hQv
  rw [hw, planeVec_zero]

end Minus

section Main

variable {p e : ℕ} [Fact p.Prime]

theorem commutingFundamentalGeneration3_pOmegaMinus (h3 : p ^ e = 3) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    CommutingFundamentalGeneration p .POmegaMinus n e := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have hM : Generic.modelUniv .POmegaMinus n p e Fact.out =
      ⟨spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2),
        minusDatum n (minusCoeffs_irr p e)⟩ := rfl
  have hsingle : Generic.FundamentalSingleClass .POmegaMinus
      (Generic.modelUniv .POmegaMinus n p e Fact.out).D :=
    fundamentalSingleClass .POmegaMinus n p e Fact.out trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus n p e Fact.out).D, Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaMinus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hk3 : ∀ x ∈ (spinAction (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)).ker, x ^ 3 = 1 → x = 1 :=
    fun x hx hx3 =>
      eq_one_of_sq_eq_one_of_pow_three (OrthAut.minus_hker2 (minusCoeffs_irr p e) x hx) hx3
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaMinus n p e Fact.out).D.rank,
      k.val + 2 < n →
      Generic.IsLongestRoot (Generic.modelUniv .POmegaMinus n p e Fact.out).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaMinus n p e Fact.out trivial hadm k hk
  show CommutingGeneration (Generic.fundamentalSubgroups .POmegaMinus
    (Generic.modelUniv .POmegaMinus n p e Fact.out).D)
  generalize Generic.modelUniv .POmegaMinus n p e Fact.out = M at hM hsingle hG3 hlong ⊢
  subst hM
  have hn0 : 0 < n - 1 := by omega
  exact commutingGeneration_minus3 hodd (minusCoeffs_irr p e) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hk3

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
