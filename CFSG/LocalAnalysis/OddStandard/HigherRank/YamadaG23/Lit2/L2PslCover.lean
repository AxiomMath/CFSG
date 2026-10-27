module

public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem l2_psl_cover (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable)
    {S : Type} [Group S] [Finite S] {n p f : ℕ} (hn : 5 ≤ n)
    (hX : CFSG.Blueprint.LieModel S .PSL n p f) {H : Type} [Group H] [Finite H]
    (hq : CFSG.IsQuasisimple H) (ρ : H →* S) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = center H) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : Matrix.SpecialLinearGroup (Fin n) K →* S)
      (α : Matrix.SpecialLinearGroup (Fin n) K →* H),
      Nat.card K = p ^ f ∧ Function.Surjective π ∧
      π.ker = center (Matrix.SpecialLinearGroup (Fin n) K) ∧ Function.Surjective α ∧
      ρ.comp α = π := by
  classical
  obtain ⟨-, K, hKf, hKfin, hK, ⟨eS⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by omega : n ≠ 0)
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* S :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).trans eS.symm
  let π₀ : Matrix.SpecialLinearGroup (Fin n) K →*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
  let π : Matrix.SpecialLinearGroup (Fin n) K →* S := e.toMonoidHom.comp π₀
  have hπs : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [MonoidHom.ker_comp_of_injective π₀ e.toMonoidHom e.injective, QuotientGroup.ker_mk']
  have hSLperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  obtain ⟨hcomm, ⟨eM⟩⟩ := hG S .PSL n p f hX
  have hSperf : Group.IsPerfect S := ⟨hcomm⟩
  have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) =
      Nat.gcd n (p ^ f - 1) := by
    rw [Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).symm.toEquiv,
      Nat.card_congr eM.toEquiv]
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL n p f =
        (Nat.gcd n (p ^ f - 1), 1) := rfl
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [hgen, hexc]
    simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = Nat.card π.ker := by
    rw [hcardM, hπk, ← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.RankThree.PartOne.card_scalars (by omega), hK]
  obtain ⟨α, hρα, hαs⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_hom_of_card_multiplier_eq hSperf hSLperf π hπs
      hπk.le hcard ρ hρs hρk.le
  exact ⟨K, hKf, hKfin, π, α, hK, hπs, hπk, hαs hq.1, hρα⟩

end CFSG.OddStandard.HigherRank.YamadaG23
