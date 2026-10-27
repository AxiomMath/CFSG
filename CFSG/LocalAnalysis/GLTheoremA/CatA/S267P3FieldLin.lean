module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldSL
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Projective

variable {K : Type} [Field K] [Finite K] {N : ℕ}

theorem exists_modelB_projectiveSL (hN : N = 4 ∨ N = 5)
    (hfield : ∀ σ : K ≃+* K, orderOf σ = 3 → ModelB (projectiveSL N K) (fieldAut N K σ))
    (β : MulAut (projectiveSL N K)) (hβ3 : β ^ 3 = 1)
    (hβ : β ∉ (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range) :
    ∃ (g : projectiveSL N K) (ψ : MulAut (projectiveSL N K)), β = MulAut.conj g * ψ ∧
      ModelB (projectiveSL N K) ψ := by
  have hD : β ∉ linearAutGroup N K := fun hD =>
    hβ (mem_range_conj_of_mem_linearAutGroup_of_coprime hD
      (by rcases hN with rfl | rfl <;> norm_num) hβ3)
  obtain ⟨σ, hσ, A, rfl⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (by omega) β hβ3 hD
  refine ⟨1, MulAut.congr (conjAut N K A) (fieldAut N K σ), ?_,
    ModelB.congr (conjAut N K A) (hfield σ hσ)⟩
  rw [map_one, one_mul]
  exact MulEquiv.ext fun _ => rfl

theorem card_le_nine_projectiveSL (hN : N = 4 ∨ N = 5) (h3 : 3 ∣ Nat.card K + 1)
    (F : Subgroup (projectiveSL N K)) (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL N K)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      ((LinearCover.projectiveSpecialLinearEquivProjectiveSL N K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj N K))]
    refine (CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSL_le_div_two ⟨1, rfl⟩
      (by omega) h3).trans ?_
    omega
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hF.isPGroup
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num)
    ((CFSG.SectionRank.le_pRank (by norm_num) le_top hF hj).trans hr)

end Projective

theorem p3At_A_of_field
    (hfield : ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ringChar K ≠ 3 →
      ∀ (n : ℕ), (n = 4 ∨ n = 5) → ∀ σ : K ≃+* K, orderOf σ = 3 →
        ModelB (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ))
    {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n Q).Valid) (h3 : 3 ∣ Q.card + 1) : P3At ⟨_, hv⟩ := by
  rintro q Ω _ _ S B H hchar ⟨e⟩
  have hQq : Q.p = q := by
    change (TauCeti.LieTypeIndex.A n Q).characteristic = q at hchar
    rwa [TauCeti.LieTypeIndex.characteristic_A] at hchar
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set K := GaloisField Q.p Q.exponent with hKdef
  have hKcard : Nat.card K = Q.card := by
    rw [hKdef, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hchK : ringChar K = q := by rw [ringChar.eq K Q.p, hQq]
  have hN : n + 1 = 4 ∨ n + 1 = 5 := by omega
  set e₁ : PSimple 3 S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n + 1)) K :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n Q hv)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    haveI := Fintype.ofFinite K
    have hK5 : 5 ≤ Fintype.card K := by
      rw [Fintype.card_eq_nat_card, hKcard, TauCeti.PrimePower.card_def]
      exact (Q.prime_p.five_le_of_ne_two_of_ne_three (hQq ▸ H.two) (hQq ▸ H.three)).trans
        (Nat.le_self_pow Q.exponent_pos.ne' _)
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier
      (k := K) (n := n + 1) (by omega) hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro hd
    have := hd.trans (Nat.gcd_dvd_left _ _)
    omega
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) K).symm.trans e₁.symm)
  exact Or.inl (concA_of_outer H hZ φ hφ hφS
    (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by omega))
    (card_le_nine_projectiveSL hN (by rwa [hKcard]))
    (exists_modelB_projectiveSL hN (hfield K (by rw [hchK]; exact H.two)
      (by rw [hchK]; exact H.three) (n + 1) hN)))

theorem p3At_A_of_dvd_add_one {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n Q).Valid) (h3 : 3 ∣ Q.card + 1) : P3At ⟨_, hv⟩ :=
  p3At_A_of_field (fun K _ _ hK2 hK3 n hn σ hσ => Field.modelB_projectiveSL hn hK2 hK3 hσ) hn3 hn4
    hv h3

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
