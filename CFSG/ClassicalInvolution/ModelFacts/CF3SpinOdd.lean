module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinOdd
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.ModelFacts.CF3Spin
public import CFSG.ClassicalInvolution.Asc77.AscR10E5

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three)
open scoped MatrixGroups


section Odd

variable {n : ℕ} {K : Type} [Field K]

open CFSG.LieType.CurtisTits in
theorem commutingGeneration_odd3 [Finite K] (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    (k₀ : Fin n) (hk₀ : k₀.val = 0)
    (hsingle : Generic.FundamentalSingleClass .POmegaOdd (oddDatum n K))
    (hlong : Generic.IsLongestRoot (oddDatum n K) (Pi.single k₀ 1))
    (hG3 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaOdd (oddDatum n K), Gen3 R)
    (hk3 : ∀ x ∈ (spinAction (quadOdd n K)).ker, x ^ 3 = 1 → x = 1) :
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
  refine commutingGeneration_spin3 hodd hQ (oddFrame n K).toHypFrame hn3 ?_
    (isPerfect_spinGroup_quadOdd h2 hn3) (range_spinAction_quadOdd h2 hn3).le _ hframe hlift hG3 hk3
  · intro v hv hQv
    have hvz := eq_smul_oddZ_of_polar_oddFrame_vec hv
    set c := v (.inr (.inr ())) with hc
    have hz : quadOdd n K (oddFrame n K).z = 1 := (oddFrame n K).map_z
    rw [hvz, QuadraticMap.map_smul, hz, smul_eq_mul, mul_one, mul_self_eq_zero] at hQv
    rw [hvz, hQv, zero_smul]

end Odd

section Main

variable {p e : ℕ} [Fact p.Prime]

theorem commutingFundamentalGeneration3_pOmegaOdd (h3 : p ^ e = 3) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    CommutingFundamentalGeneration p .POmegaOdd n e := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e (ne_two_of_pow_eq_three h3)
  have hM : Generic.modelUniv .POmegaOdd n p e Fact.out =
      ⟨spinGroup (quadOdd n (GaloisField p e)), oddDatum n (GaloisField p e)⟩ := rfl
  have hsingle : Generic.FundamentalSingleClass .POmegaOdd
      (Generic.modelUniv .POmegaOdd n p e Fact.out).D :=
    fundamentalSingleClass .POmegaOdd n p e Fact.out trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaOdd
      (Generic.modelUniv .POmegaOdd n p e Fact.out).D, Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaOdd) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hk3 : ∀ x ∈ (spinAction (quadOdd n (GaloisField p e))).ker, x ^ 3 = 1 → x = 1 :=
    fun x hx hx3 => eq_one_of_sq_eq_one_of_pow_three (OrthAut.odd_hker2 h2 n x hx) hx3
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaOdd n p e Fact.out).D.rank, k.val + 1 < n →
      Generic.IsLongestRoot (Generic.modelUniv .POmegaOdd n p e Fact.out).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaOdd n p e Fact.out trivial hadm k hk
  show CommutingGeneration (Generic.fundamentalSubgroups .POmegaOdd
    (Generic.modelUniv .POmegaOdd n p e Fact.out).D)
  generalize Generic.modelUniv .POmegaOdd n p e Fact.out = M at hM hsingle hG3 hlong ⊢
  subst hM
  have hn0 : 0 < n := by omega
  exact commutingGeneration_odd3 hodd hn3 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega)) hG3 hk3

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
