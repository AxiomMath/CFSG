module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CASwap3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAP
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralTwoCoverTransfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

theorem y7c_swap_center_N_trivial (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K)
    (hSM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) {z : Γ}
    (hz : z ∈ Subgroup.normalClosure (J : Set Γ))
    (hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) : z = 1 := by
  let N : Subgroup Γ := Subgroup.normalClosure (J : Set Γ)
  let Zc : Subgroup ↥N := Subgroup.center ↥N
  haveI : Zc.Normal := Subgroup.instNormalCenter
  let P' : Subgroup ↥N := P.subgroupOf N
  let S : Subgroup ↥N := Zc ⊔ P'
  have hzN : z ∈ N := hz
  have hN : N = K ⊔ conjSub t K := y7c_swap_N_eq c hK hJK hne
  have hKt : CFSG.IsComponent (conjSub t K) := y7c_isComponent_conjSub hK t
  have hKN : K ≤ N := by rw [hN]; exact le_sup_left
  have hKtN : conjSub t K ≤ N := by rw [hN]; exact le_sup_right
  have hsup_le : K ⊔ conjSub t K ≤ ⁅N, N⁆ :=
    sup_le (Subgroup.isPerfect_iff.mp hK.1.1 ▸ Subgroup.commutator_mono hKN hKN)
      (Subgroup.isPerfect_iff.mp hKt.1.1 ▸ Subgroup.commutator_mono hKtN hKtN)
  have hcomm_eq : ⁅N, N⁆ = N :=
    le_antisymm (Subgroup.commutator_le_self N) (hN.le.trans hsup_le)
  have hperf : commutator ↥N = ⊤ := (Subgroup.isPerfect_iff.mpr hcomm_eq).commutator_eq_top
  have hZc2 : IsPGroup 2 ↥Zc := by
    rw [_root_.isPGroup_iff_orderOf_dvd_pow]
    intro g
    refine ⟨1, ?_⟩
    have hsqN : (g : ↥N) * (g : ↥N) = 1 := by
      apply Subtype.ext
      have hc : ∀ n ∈ N, ((g : ↥N) : Γ) * n = n * ((g : ↥N) : Γ) :=
        fun n hn => (congrArg Subtype.val (Subgroup.mem_center_iff.mp g.2 ⟨n, hn⟩)).symm
      exact y7c_swap_center_sq c hK hJK hne hSM (g : ↥N).2 hc
    rw [pow_one, orderOf_dvd_iff_pow_eq_one, pow_two]
    exact Subtype.ext hsqN
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Zc)).mp hZc2
  have hcardN : Nat.card ↥N = 168 ^ 2 * Nat.card ↥Zc := y7c_swap_card_N c hK hJK hne
  have hcardP' : Nat.card ↥P' = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y7c_P_le_N c)).toEquiv, c.P_card]
  have hcommZP : ∀ x ∈ Zc, ∀ y ∈ P', x * y = y * x :=
    fun x hx y _ => (Subgroup.mem_center_iff.mp hx y).symm
  have hinf : Zc ⊓ P' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (y7c_P_inf_center c (Subgroup.mem_subgroupOf.mp hx.2) x.2
      fun n hn => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx.1 ⟨n, hn⟩)).symm)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Zc P' hcommZP).1
  rw [hinf, Subgroup.card_bot, mul_one, hcardP', hm] at hprod
  have hcardS : Nat.card ↥S = 2 ^ (m + 6) := by
    change Nat.card ↥(Zc ⊔ P') = 2 ^ (m + 6)
    rw [hprod]
    exact (pow_add 2 m 6).symm
  have hfacN : (Nat.card ↥N).factorization 2 = m + 6 := by
    have h168 : (168 : ℕ) ^ 2 = 2 ^ 6 * 441 := by norm_num
    have h441 : (441 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 441)
    have hNfac : Nat.card ↥N = 2 ^ (6 + m) * 441 := by
      rw [hcardN, hm, h168, mul_assoc (2 ^ 6) 441 (2 ^ m), mul_comm 441 (2 ^ m),
        ← mul_assoc, ← pow_add]
    rw [hNfac, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, h441, add_zero]
    omega
  have hcard : Nat.card ↥S = 2 ^ (Nat.card ↥N).factorization 2 := by
    rw [hfacN, hcardS]
  have hZP : Zc ≤ (Sylow.ofCard S hcard : Subgroup ↥N) := by
    rw [Sylow.coe_ofCard]
    exact le_sup_left
  have hdec : ∀ x ∈ (Sylow.ofCard S hcard : Subgroup ↥N),
      ∃ z ∈ Zc, ∃ y ∈ P', x = z * y := by
    intro x hx
    change x ∈ Zc ⊔ P' at hx
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨z, hz, y, hy, hzy⟩ := hx
    exact ⟨z, hz, y, hy, hzy.symm⟩
  have hbot : Zc = ⊥ :=
    CFSG.ProperTwoGeneratedCore.CentralTwoCover.eq_bot_of_complement_of_perfect
      (G := ↥N) (p := 2) hperf (Sylow.ofCard S hcard) le_rfl hZP hdec hinf
  have hzmem : (⟨z, hzN⟩ : ↥N) ∈ Zc := by
    rw [Subgroup.mem_center_iff]
    intro n
    exact Subtype.ext (hzc n n.2).symm
  have hz1 : (⟨z, hzN⟩ : ↥N) = 1 := by
    have hmem : (⟨z, hzN⟩ : ↥N) ∈ (⊥ : Subgroup ↥N) := hbot ▸ hzmem
    simpa using hmem
  exact Subtype.ext_iff.mp hz1

end CFSG.OddStandard.HigherRank.YamadaG23
