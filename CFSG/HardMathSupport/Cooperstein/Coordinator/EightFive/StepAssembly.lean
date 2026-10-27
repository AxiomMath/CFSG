module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepPairEven
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepPairOdd
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepLarge
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepTransitive
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.Open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

theorem tperm_step {n : ℕ} (hn : 9 ≤ n) (ih : ∀ m, 7 ≤ m → m < n → TPerm m)
    (h9 : ExitNineFix) (h10e : ExitTenEven) (h10o : ExitTenOdd) (hLN : ExitLargeNat)
    (hLE : ExitLargeExotic) (h16 : ExitSixteenTransitive) : TPerm n := by
  intro V _ _ hV H ψ hψ hAlt ⟨A, hA⟩
  left
  have hE : IsExp2 ((A.subgroupOf H).map ψ) := isExp2_map_subgroupOf hA.2.2.1
  by_cases hfix : ∃ ω, ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a ω = ω
  · obtain ⟨ω, hω⟩ := hfix
    exact step_fix hV hψ hAlt hA hn (ih (n - 1) (by omega) (by omega)) ω hω h9
  push Not at hfix
  have hmin : ∀ i : Fin n, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i := hfix
  have h1 : ∀ i : Fin n, Nat.card (orbit ((A.subgroupOf H).map ψ) i) ≠ 1 := fun i h => by
    obtain ⟨a, ha, hai⟩ := hmin i
    exact hai (fixed_of_card_orbit_eq_one h (ψ a) ⟨a, ha, rfl⟩)
  by_cases h2 : ∃ i : Fin n, Nat.card (orbit ((A.subgroupOf H).map ψ) i) = 2
  · obtain ⟨p, hp⟩ := h2
    obtain ⟨q, hqp, hpq⟩ := exists_pair_of_card_orbit_eq_two hp
    have hn10 : 10 ≤ n := by
      have heven := even_of_card_orbit_ne_one hE h1
      rw [Nat.card_fin] at heven
      obtain ⟨k, hk⟩ := heven
      omega
    have horb : ∀ a : ↥H, (a : MulAut V) ∈ A →
        ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p := fun a ha => hpq (ψ a) ⟨a, ha, rfl⟩
    by_cases hAL : A ≤ altPre ψ
    · exact step_pair_le hV hψ hAlt hA hn10 (ih (n - 2) (by omega) (by omega)) p q
        (Ne.symm hqp) hAL horb hmin h10e
    · exact step_pair_not_le hV hψ hAlt hA hn10 (ih (n - 2) (by omega) (by omega))
        (ih (n - 1) (by omega) (by omega)) p q (Ne.symm hqp) hAL horb hmin h10o
  push Not at h2
  have h4 : ∀ i : Fin n, 4 ≤ Nat.card (orbit ((A.subgroupOf H).map ψ) i) := fun i =>
    four_le_card_orbit hE (h1 i) (h2 i)
  by_cases htr : IsPretransitive ((A.subgroupOf H).map ψ) (Fin n)
  · exact (step_transitive hV hψ hAlt hA hn (fun m hm hmn => ih m (by omega) hmn) htr h16).elim
  · exact step_large hV hψ hAlt hA hn (fun m hm hmn => ih m (by omega) hmn) h4 htr hLN hLE

theorem tperm_all (h7 : TPerm 7) (h8 : TPerm 8) (h9 : ExitNineFix) (h10e : ExitTenEven)
    (h10o : ExitTenOdd) (hLN : ExitLargeNat) (hLE : ExitLargeExotic)
    (h16 : ExitSixteenTransitive) : ∀ n, 7 ≤ n → TPerm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 7 ∨ n = 8 ∨ 9 ≤ n by omega) with rfl | rfl | hn9
    · exact h7
    · exact h8
    · exact tperm_step hn9 (fun m hm7 hmn => ih m hmn hm7) h9 h10e h10o hLN hLE h16

theorem gf2EightFive_of_exits (h8 : TPerm 8)
    (h9 : ExitNineFix) (h10e : ExitTenEven) (h10o : ExitTenOdd) (hLN : ExitLargeNat)
    (hLE : ExitLargeExotic) (h16 : ExitSixteenTransitive) : GF2EightFive :=
  gf2EightFive_of_tperm fun n hn =>
    tperm_all tperm_seven h8 h9 h10e h10o hLN hLE h16 n (by omega)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
