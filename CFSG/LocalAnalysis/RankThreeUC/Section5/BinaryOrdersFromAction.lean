module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful
public import CFSG.LocalAnalysis.RankThreeUC.Section5.FixedKernel
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeCommutatorNontrivial
public import CFSG.LinearAlgebra.CoprimeActions.BinaryMersenneOrderPowerTwo
public import CFSG.LocalAnalysis.RankThreeUC.NotIsMulCommutativeAndBinaryOrderPowerTwoOfFixedPointFreeAction
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryOrdersFromAction

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction

variable {G : Type} [Group G] [Finite G]

theorem binary_orders {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hpi : p ∉ piOf B) :
    ∀ r ∈ piOf B, ∃ k : ℕ, binaryMultiplicativeOrder r = 2 ^ k := by
  intro r hr
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨h.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨h.oddPrimeClassTwoAction.setting.exponent⟩
  obtain ⟨A, hAB, hAcard, hAnorm, hAne, hA2⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeCommutatorNontrivial.exists_prime_subgroup h hr
  have hrp : r.Prime := hr.1
  have hrB : r ∣ Nat.card B := hr.2
  have hr_odd : r ≠ 2 := by
    rintro rfl
    exact absurd (Odd.of_dvd_nat h.oddPrimeClassTwoAction.setting.oddOrder hrB) (by decide)
  have hrp' : r ≠ p := by rintro rfl; exact hpi hr
  have hp2 : 2 ≠ p := by
    rintro rfl; exact absurd h.oddPrimeClassTwoAction.setting.odd (by decide)
  obtain ⟨hcop, hinj⟩ := CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful.faithful h hpi
  haveI := CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful.solvable h
  have hS : CFSG.LocalAnalysis.RankThreeUC.FaithfulPrimeFieldKGroupModule (joint P T B) p (Additive (Quotient.Pbar P))
      (rep p (joint P T B)) :=
    ⟨CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful.kGroup h, hp, hinj⟩
  set D : Subgroup (joint P T B) := (A.subgroupOf B).map (bToJoint h.oddPrimeClassTwoAction) with hD
  set S : Subgroup (joint P T B) := (Sstar P T B).subgroupOf (joint P T B) with hSdef
  have hDcard : Nat.card D = r := by
    rw [hD, Subgroup.card_map_of_injective (bToJoint_injective h.oddPrimeClassTwoAction h.faithfulBinaryIrreducibleAction),
      ← hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have hCV : (⨅ d ∈ D, LinearMap.ker (rep p (joint P T B) d - LinearMap.id)) =
      (⊥ : Submodule (ZMod p) (Additive (Quotient.Pbar P))) := by
    have hne : D ≠ ⊥ := by
      intro hbot
      have : Nat.card D = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hDcard] at this
      exact hrp.one_lt.ne' this
    obtain ⟨⟨d, hd⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hd1 : d ≠ 1 := fun h1 => hd1' (Subtype.ext h1)
    have hd' := hd
    rw [hD, Subgroup.mem_map] at hd'
    obtain ⟨a, -, rfl⟩ := hd'
    have ha : a ≠ 1 := by rintro rfl; exact hd1 (by simp)
    rw [eq_bot_iff, ← CFSG.LocalAnalysis.RankThreeUC.Section5.FixedKernel.kernel_eq_bot h hpi a ha]
    exact iInf₂_le _ hd
  have hQD : ⁅D, ⁅D, S⁆⁆ = ⁅D, S⁆ := by
    have hS2 : IsPGroup 2 S :=
      (CFSG.LocalAnalysis.RankThreeUC.Section5.SstarQuotientFaithful.isPGroup h).comap_subtype
        (K := joint P T B)
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    have hc : Nat.Coprime (Nat.card D) (Nat.card S) := by
      rw [hDcard, hn]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hrp Nat.prime_two).2 hr_odd)
    have := CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S D hc hAnorm
    rw [Subgroup.commutator_comm D S, Subgroup.commutator_comm D ⁅S, D⁆]
    exact this
  have := CFSG.LocalAnalysis.RankThreeUC.not_isMulCommutative_and_binary_order_power_two_of_fixedPointFree_action hS Nat.prime_two hrp hp2 hrp' (Ne.symm hr_odd) D hDcard hCV
    ⁅D, S⁆ hQD hAne hA2
  exact this.2.2

theorem exponent_is_two_power {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hpi : p ∉ piOf B) :
    ∃ k : ℕ, e = 2 ^ k := by
  refine CFSG.LinearAlgebra.CoprimeActions.BinaryMersenneOrderPowerTwo.exponent_is_two_power e
    (by have := h.oddPrimeClassTwoAction.two_lt; omega) fun r hr hrd => ?_
  exact binary_orders h hpi r (by rw [h.oddPrimeClassTwoAction.pi_eq]; exact ⟨hr, hrd⟩)

end CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryOrdersFromAction
