module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LInner3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LField2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LGF
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.GH74.Exceptional.LinearFourTwo
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank

@[expose] def GraphWitInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K], (2 : K) = 0 → 3 ≤ n → (n = 3 → 8 ≤ Nat.card K) →
    (n = 4 → 4 ≤ Nat.card K) → ∀ A : GL (Fin n) K, (conjAut n K A * dualAut n K) ^ 2 = 1 →
      HasWit (conjAut n K A * dualAut n K)

@[expose] def GraphField3WitInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) = 0 → 8 ≤ Nat.card K → ∀ (A : GL (Fin 3) K)
    (σ : K ≃+* K), σ ≠ 1 → (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1 →
      HasWit (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K)

variable {n : ℕ} {K : Type} [Field K]

theorem hasWit_psl [Finite K] (h2 : (2 : K) = 0) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (h3 : n = 3 → 8 ≤ Nat.card K)
    (h4 : n = 4 → 4 ≤ Nat.card K) (hG : GraphWitInput) (hGF : GraphField3WitInput)
    {v : MulAut (projectiveSL n K)} (hv : orderOf v = 2) : HasWit v := by
  have hsq : v ^ 2 = 1 := by rw [← hv, pow_orderOf_eq_one]
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 v
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    · rw [hσ, map_one, mul_one] at hα
      subst hα
      exact hasWit_conjAut h2 hn h3 hv
    · rw [hα] at hsq ⊢
      exact hasWit_field h2 hn hσ hsq
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · rw [hσ, map_one, mul_one] at hα
      rw [hα] at hsq ⊢
      exact hG n K h2 hn h3 h4 A hsq
    · rw [hα] at hsq ⊢
      rcases Nat.lt_or_ge n 4 with hn4 | hn4
      · obtain rfl : n = 3 := by omega
        exact hGF K h2 (h3 rfl) A σ hσ hsq
      · exact hasWit_graphField h2 hn4 hf hK hσ hsq

theorem twoNilpFor_psl_of_inputs
    (hA : TwoNilpFor fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hG : GraphWitInput) (hGF : GraphField3WitInput) :
    TwoNilpFor fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .PSL n 2 f := by
  intro Y _ _ hY hs hnab a ha hP
  obtain ⟨n, f, hYm⟩ := hY
  have hL : Blueprint.LieModel Y .PSL n 2 f := Or.inl ⟨by decide, hYm⟩
  obtain ⟨-, hf, hn2, -⟩ := hYm.1
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exact Or.inl ⟨2, f, hL⟩
  by_cases h31 : n = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h31
    exact Or.inl ⟨7, 1, LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism Y hL⟩
  by_cases h32 : n = 3 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := h32
    exact Or.inr (Or.inr (Or.inl hL))
  by_cases h41 : n = 4 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h41
    exact hA Y ⟨8, by norm_num, GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hL⟩
      hs hnab a ha hP
  obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hf3 : n = 3 → 8 ≤ Nat.card K := fun h => by
    rw [hKc]
    have : 3 ≤ f := by omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  have hf4 : n = 4 → 4 ≤ Nat.card K := fun h => by
    rw [hKc]
    have : 2 ≤ f := by omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  have hw := hasWit_psl h2 hf hKc hn3 hf3 hf4 hG hGF (v := MulAut.congr θ a)
    (by rw [MulEquiv.orderOf_eq]; exact ha)
  have hw' := hw.congr θ.symm
  have e : MulAut.congr θ.symm (MulAut.congr θ a) = a := by
    ext y
    simp [MulAut.congr_apply]
  rw [e] at hw'
  exact absurd hP (not_isPGroup_of_hasWit hw')

end CFSG.ComponentClassification.HarrisLit.L33.C2
