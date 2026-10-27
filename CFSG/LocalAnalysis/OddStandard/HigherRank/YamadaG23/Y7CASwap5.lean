module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CASwap4

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

theorem y7c_swap_conclusion (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K)
    (hSM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) :
    ∃ Y : Subgroup Γ, Nonempty (↥Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∧
      IsInternalDirect (Subgroup.normalClosure (J : Set Γ)) Y (conjSub t Y) ∧
      IsSylowIn 2 (Subgroup.normalClosure (J : Set Γ)) P := by
  have hne' : K ≠ conjSub t K := fun h => hne h.symm
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a :=
    y7c_comm_of_components hK (y7c_isComponent_conjSub hK t) hne'
  have hN : Subgroup.normalClosure (J : Set Γ) = K ⊔ conjSub t K :=
    y7c_swap_N_eq c hK hJK hne
  have hcenterN : Subgroup.center ↥(Subgroup.normalClosure (J : Set Γ)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), (z : Γ) * n = n * (z : Γ) := by
      intro n hn
      have hzn := Subgroup.mem_center_iff.mp hz ⟨n, hn⟩
      exact (congrArg Subtype.val hzn).symm
    exact Subtype.ext (by
      simpa using y7c_swap_center_N_trivial c hK hJK hne hSM z.2 hzc)
  have hcardN : Nat.card ↥(Subgroup.normalClosure (J : Set Γ)) = 168 ^ 2 := by
    have hbot : Nat.card ↥(⊥ : Subgroup ↥(Subgroup.normalClosure (J : Set Γ))) = 1 :=
      Nat.card_unique
    rw [y7c_swap_card_N c hK hJK hne, hcenterN, hbot, mul_one]
  have hcenterK : Subgroup.center ↥K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzcN : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), (z : Γ) * n = n * (z : Γ) := by
      intro n hn
      have hle : K ⊔ conjSub t K ≤ Subgroup.centralizer ({(z : Γ)} : Set Γ) := by
        refine sup_le ?_ ?_
        · intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)).symm
        · intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hcomm z z.2 k hk
      rw [← hN] at hle
      exact (Subgroup.mem_centralizer_iff.mp (hle hn)) (z : Γ) (by simp)
    exact Subtype.ext (by
      have hzN : (z : Γ) ∈ Subgroup.normalClosure (J : Set Γ) := by
        rw [hN]
        exact Subgroup.mem_sup_left z.2
      simpa using y7c_swap_center_N_trivial c hK hJK hne hSM hzN hzcN)
  have hKGL : Nonempty (↥K ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
    obtain ⟨e⟩ := y7c_swap_quot_equiv c hK hJK hne
    refine ⟨((QuotientGroup.quotientMulEquivOfEq hcenterK).trans
      QuotientGroup.quotientBot).symm.trans e⟩
  refine ⟨K, hKGL, ?_, ?_⟩
  · unfold IsInternalDirect
    refine ⟨hN.symm, ?_, hcomm⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxN : x ∈ Subgroup.normalClosure (J : Set Γ) := by
      rw [hN]
      exact Subgroup.mem_sup_left hx.1
    have hxc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), x * n = n * x := by
      intro n hn
      have hle : K ⊔ conjSub t K ≤ Subgroup.centralizer ({x} : Set Γ) := by
        refine sup_le ?_ ?_
        · intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (hcomm k hk x hx.2).symm
        · intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hcomm x hx.1 k hk
      rw [← hN] at hle
      exact (Subgroup.mem_centralizer_iff.mp (hle hn)) x (by simp)
    exact y7c_swap_center_N_trivial c hK hJK hne hSM hxN hxc
  · refine ⟨y7c_P_le_N c, c.P_two, ?_⟩
    have hcardPN : Nat.card ↥(P.subgroupOf (Subgroup.normalClosure (J : Set Γ))) =
        Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y7c_P_le_N c)).toEquiv
    have hmul : P.relIndex (Subgroup.normalClosure (J : Set Γ)) * 2 ^ 6 = 168 ^ 2 := by
      have h := Subgroup.index_mul_card (P.subgroupOf (Subgroup.normalClosure (J : Set Γ)))
      rw [hcardPN, c.P_card, hcardN] at h
      simpa only [Subgroup.relIndex] using h
    have hrel : P.relIndex (Subgroup.normalClosure (J : Set Γ)) = 441 := by
      have h' := hmul
      norm_num at h'
      omega
    rw [hrel]
    norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
