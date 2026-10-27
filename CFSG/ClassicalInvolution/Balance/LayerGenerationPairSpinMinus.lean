module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinGen
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K}

open CFSG.LieType.CurtisTits in
theorem map_rankOne_minus (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Fin (n - 1)}
    (hk : k.val + 1 < n - 1) :
    (rankOne (minusDatum n hirr).rootGroup k).map (spinAction (quadMinus n K b c)) =
      ((minusFrame n b c).toHypFrame.toFrame (succ_ne_of_lt n hk) true false).La.range := by
  have h1 : rankOne (minusDatum n hirr).rootGroup k =
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false).range :=
    rankOne_minusRootGroup_of_lt n hirr hk
  rw [h1]
  exact map_longSL2_range (minusFrame n b c).toHypFrame (succ_ne_of_lt n hk) true false

open CFSG.LieType.CurtisTits in
theorem commutingGeneration_minus [Finite K] (hodd : Odd (Nat.card K))
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) (k₀ : Fin (n - 1)) (hk₀ : k₀.val = 0)
    (hsingle : Generic.FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hlong : Generic.IsLongestRoot (minusDatum n hirr) (Pi.single k₀ 1))
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ⁅R, R⁆ = R) :
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
  refine commutingGeneration_spin hodd hQ (minusFrame n b c).toHypFrame (by omega) ?_
    (isPerfect_spinGroup_quadMinus hn hirr) (range_spinAction_quadMinus hn hirr).le _ hframe hlift
    hperf
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

theorem commutingFundamentalGeneration_pOmegaMinus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    CommutingFundamentalGeneration p .POmegaMinus n e := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaMinus n p e Fact.out =
      ⟨spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2),
        minusDatum n (minusCoeffs_irr p e)⟩ := rfl
  have hsingle : Generic.FundamentalSingleClass .POmegaMinus
      (Generic.modelUniv .POmegaMinus n p e Fact.out).D :=
    fundamentalSingleClass .POmegaMinus n p e Fact.out trivial hadm (by decide) (by decide)
  have hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus n p e Fact.out).D, ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
      (fundPerfect_core .POmegaMinus n p e hp2 trivial hadm (by omega) R hR)
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaMinus n p e Fact.out).D.rank,
      k.val + 2 < n →
      Generic.IsLongestRoot (Generic.modelUniv .POmegaMinus n p e Fact.out).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaMinus n p e Fact.out trivial hadm k hk
  show CommutingGeneration (Generic.fundamentalSubgroups .POmegaMinus
    (Generic.modelUniv .POmegaMinus n p e Fact.out).D)
  generalize Generic.modelUniv .POmegaMinus n p e Fact.out = M at hM hsingle hperf hlong ⊢
  subst hM
  have hn0 : 0 < n - 1 := by omega
  exact commutingGeneration_minus hodd (minusCoeffs_irr p e) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hperf

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
