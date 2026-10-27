module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamBSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisArith
import CFSG.GroupTheory.WeirSylow.Symplectic
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.GroupTheory.WeirSylow
open CFSG.Blueprint
open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp StatedScalars)

noncomputable def heisBProjEquiv (r : ℕ) (K : Type) [Field K] [CharP K 2] :
    StatedProj (StatedSp r K) ≃* StatedSp r K :=
  (QuotientGroup.quotientMulEquivOfEq
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot).trans QuotientGroup.quotientBot

theorem heisB_out_data {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {r f : ℕ} (hcl : StatedClassicalModel X .PSp r 2 f) :
    OutPCyc p X ∧ ((∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) → ∃ f₀ : ℕ, f = p * f₀) := by
  have hadm : StatedLieAdmissible .PSp r 2 f := hcl.1
  have hr : 2 ≤ r := hadm.2.2.1
  refine ⟨?_, ?_⟩
  · rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact outPCyc_of_outPNice (CFSG.RankThree.PartOne.OutStructure.outPNice_PSp_two hp hcl)
    · exact outPCyc_of_outPNice
        (CFSG.RankThree.PartOne.OutStructure.outPNice_PSp_ge_three hp hr3 hcl)
  · rintro ⟨α, hαin, hαp⟩
    have hmodel : LieModel X .PSp r 2 f := Or.inl ⟨by simp [classicalTags], hcl⟩
    have hdiv : ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSp r (2 ^ f) := by
      intro h
      change p ∣ Nat.gcd 2 (2 ^ f - 1) at h
      have h1 : p ≤ Nat.gcd 2 (2 ^ f - 1) := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ two_pos) h
      have h2 : Nat.gcd 2 (2 ^ f - 1) ≤ 2 := Nat.gcd_le_left _ two_pos
      omega
    rcases CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp X r 2 f hadm
        hmodel (by decide) p hp (by omega) hdiv (fun h => absurd h.1 (by decide)) α hαp hαin with
      ⟨f₀, hf₀, -⟩ | ⟨h, -⟩
    · exact ⟨f₀, hf₀⟩
    · exact absurd h (by decide)

theorem heisB_noHeisAut_of_model {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hrk : ∀ A : Subgroup X, IsMulCommutative A → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ 3)
    {r f : ℕ} (hcl : StatedClassicalModel X .PSp r 2 f) : NoHeisAut p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hCyc, hfield⟩ := heisB_out_data hp hp5 hcl
  obtain ⟨⟨-, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hcl
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hKc : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hp2 : p ≠ 2 := by omega
  have hpow : ∀ m : ℕ, ¬ p ∣ 2 ^ m := fun m h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hpK : ¬ p ∣ Fintype.card K := by rw [hKc]; exact hpow f
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hW := heisB_sylowShape_of_mulEquiv (e.trans (heisBProjEquiv r K))
    (fun P => sylow_Sp hodd K hpK r P)
  have ha1 : 1 ≤ padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1) :=
    heisB_one_le_padicValNat (by rw [hKc]; exact Nat.one_lt_two_pow (by omega)) hpK
  have hlt := heisB_lt_of_sigmaModel hp hp5 ha1 hW hrk
  have hH := sylow_equiv_homC_of_sigmaModel hp hlt hW
  refine noHeisAut_of_homC_sylow hp hp5 hZ hCyc hrk fun S => ⟨_, _, hH S, Or.inr fun hout => ?_⟩
  obtain ⟨f₀, rfl⟩ := hfield hout
  have hf₀ : f₀ ≠ 0 := by
    rintro rfl
    omega
  have hq : Fintype.card K = (2 ^ f₀) ^ p := by rw [hKc, ← pow_mul, mul_comm]
  rw [hq]
  exact heis_two_le_padicValNat hp (hpow f₀) (Nat.le_self_pow hf₀ 2)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
