module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAHyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAInv3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CASwap5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAZ4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAD2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_struct (hI31 : CFSG.ASVolI.I_3_1) (hN24 : Nar24)
    (hSM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2)
    (c : K7Abs ρ t J Q P M6 M7) :
    (∃ Y : Subgroup Γ, Nonempty (↥Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∧
        IsInternalDirect (Subgroup.normalClosure (J : Set Γ)) Y (conjSub t Y) ∧
        IsSylowIn 2 (Subgroup.normalClosure (J : Set Γ)) P) ∨
    (∃ (r : ℕ) (z : Γ), r.Prime ∧ r ≠ 2 ∧ z ∈ Subgroup.normalClosure (J : Set Γ) ∧
        (∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) ∧
        IsPGroup r ↥(Subgroup.zpowers z) ∧ ∀ m : M, ρ z m = m → m = 1) := by
  obtain ⟨K, hK, hJK⟩ := y7c_component_cover hI31 c
  by_cases hKt : conjSub t K = K
  · by_cases hnorm : ∀ g : Γ, conjSub g K = K
    · have hNK := y7c_N_eq_K_of_normal c hK hJK hnorm
      have hq : CFSG.IsQuasisimple ↥(Subgroup.normalClosure (J : Set Γ)) := by
        rw [hNK]
        exact hK.1
      have hker : ∀ n m : Γ, ρ n = 1 → m ∈ Subgroup.normalClosure (J : Set Γ) →
          n * m = m * n := fun n m hn hm => y7c_ker_cent_N c hK hJK hn hm
      by_cases hZ : ∀ z ∈ Subgroup.normalClosure (J : Set Γ),
          (∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) → ρ z = 1
      · exact (y7c_D2_false hN24 c rfl hq hker hZ).elim
      · push_neg at hZ
        obtain ⟨z, hz, hzc, hρz⟩ := hZ
        exact Or.inr (y7c_odd_central c hq hz hzc hρz)
    · push_neg at hnorm
      obtain ⟨g, hg⟩ := hnorm
      exact (y7c_two_fixed_false c hK hJK hKt hg).elim
  · exact Or.inl (y7c_swap_conclusion c hK hJK hKt hSM)

end CFSG.OddStandard.HigherRank.YamadaG23
