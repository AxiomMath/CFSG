module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinGen
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Odd

variable {n : ℕ} {K : Type} [Field K]

open CFSG.LieType.CurtisTits in
theorem map_rankOne_odd (k : Fin n) (hk : k.val + 1 < n) {j : Fin n} (hj : j.val = k.val + 1)
    (hkj : k ≠ j) :
    (rankOne (oddDatum n K).rootGroup k).map (spinAction (quadOdd n K)) =
      ((oddFrame n K).toHypFrame.toFrame hkj true false).La.range := by
  have h1 : rankOne (oddDatum n K).rootGroup k = (rankOneB K k).range :=
    le_antisymm (OddCT.rankOne_le_range _) (by
      rintro _ ⟨M, rfl⟩
      exact OddCT.rankOneB_mem_rankOne _ M)
  rw [h1, rankOneB_of_lt K hk hj hkj]
  exact map_longSL2_range (oddFrame n K).toHypFrame hkj true false

open CFSG.LieType.CurtisTits in
theorem commutingGeneration_odd [Finite K] (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    (k₀ : Fin n) (hk₀ : k₀.val = 0)
    (hsingle : Generic.FundamentalSingleClass .POmegaOdd (oddDatum n K))
    (hlong : Generic.IsLongestRoot (oddDatum n K) (Pi.single k₀ 1))
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaOdd (oddDatum n K), ⁅R, R⁆ = R) :
    CommutingGeneration (Generic.fundamentalSubgroups .POmegaOdd (oddDatum n K)) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ : (quadOdd n K).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n K h2)
  have : Nonempty (Fin n ⊕ Fin n ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
  have hk : k₀.val + 1 < n := by omega
  let j₀ : Fin n := ⟨k₀.val + 1, hk⟩
  have hij : k₀ ≠ j₀ := fun h => by simpa [j₀] using congrArg Fin.val h
  have hdim : Module.finrank K (Fin n ⊕ Fin n ⊕ Unit → K) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  let fr₀ : Frame (quadOdd n K) := (oddFrame n K).toHypFrame.toFrame hij true false
  have hR₀mem : rankOne (oddDatum n K).rootGroup k₀ ∈
      Generic.fundamentalSubgroups .POmegaOdd (oddDatum n K) :=
    ⟨1, Pi.single k₀ 1, Or.inl hlong, by ext y; simp [rankOne]⟩
  have hperp : 2 ≤ Module.finrank K fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  obtain ⟨hframe, hlift⟩ := frames_of_single_class hodd hQ
    (Generic.fundamentalSubgroups .POmegaOdd (oddDatum n K))
    (rankOne (oddDatum n K).rootGroup k₀) fr₀
    (map_rankOne_odd k₀ hk (j := j₀) rfl hij) hperp
    (fun y => ⟨y, Pi.single k₀ 1, Or.inl hlong, rfl⟩) (fun R hR => hsingle _ hR₀mem R hR)
  refine commutingGeneration_spin hodd hQ (oddFrame n K).toHypFrame hn3 ?_
    (isPerfect_spinGroup_quadOdd h2 hn3) (range_spinAction_quadOdd h2 hn3).le _ hframe hlift hperf
  · intro v hv hQv
    have hvz := eq_smul_oddZ_of_polar_oddFrame_vec hv
    set c := v (.inr (.inr ())) with hc
    have hz : quadOdd n K (oddFrame n K).z = 1 := (oddFrame n K).map_z
    rw [hvz, QuadraticMap.map_smul, hz, smul_eq_mul, mul_one, mul_self_eq_zero] at hQv
    rw [hvz, hQv, zero_smul]

end Odd

section Main

variable {p e : ℕ} [Fact p.Prime]

theorem commutingFundamentalGeneration_pOmegaOdd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    CommutingFundamentalGeneration p .POmegaOdd n e := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaOdd n p e Fact.out =
      ⟨spinGroup (quadOdd n (GaloisField p e)), oddDatum n (GaloisField p e)⟩ := rfl
  have hsingle : Generic.FundamentalSingleClass .POmegaOdd
      (Generic.modelUniv .POmegaOdd n p e Fact.out).D :=
    fundamentalSingleClass .POmegaOdd n p e Fact.out trivial hadm (by decide) (by decide)
  have hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaOdd
      (Generic.modelUniv .POmegaOdd n p e Fact.out).D, ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
      (fundPerfect_core .POmegaOdd n p e hp2 trivial hadm (by omega) R hR)
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaOdd n p e Fact.out).D.rank, k.val + 1 < n →
      Generic.IsLongestRoot (Generic.modelUniv .POmegaOdd n p e Fact.out).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaOdd n p e Fact.out trivial hadm k hk
  show CommutingGeneration (Generic.fundamentalSubgroups .POmegaOdd
    (Generic.modelUniv .POmegaOdd n p e Fact.out).D)
  generalize Generic.modelUniv .POmegaOdd n p e Fact.out = M at hM hsingle hperf hlong ⊢
  subst hM
  have hn0 : 0 < n := by omega
  exact commutingGeneration_odd hodd hn3 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega)) hperf

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
