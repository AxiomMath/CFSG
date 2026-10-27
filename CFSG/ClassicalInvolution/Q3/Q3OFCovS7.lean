module

public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.ClassicalInvolution.Q3.Q3OFCovPull
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3NTAlpha
public import CFSG.ClassicalInvolution.Q3.Q3OFStmt
public import CFSG.ClassicalInvolution.Q3.Q3TY1
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

set_option linter.unusedSectionVars false

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort shortElt_eq)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed (single_add_single_apply_of_ne'
  negPair_swap single_add_single_add_not two_mul_boolSign not_isLong_single_two swapPair_swap
  not_isLong_add_disjoint)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

variable {n : ℕ} {K : Type} [Field K]

theorem spinSeven_ker_eq_bot_of_comm [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    [Group.IsPerfect E] {π : E →* spinGroup (quadOdd 3 K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {γ δ : Fin 3 → ℤ} (h : IsOrthPair γ δ)
    (hcomm : ∀ a b : E, π a = SpinOdd.x 3 K γ 1 → π b = SpinOdd.x 3 K δ 1 → a * b = b * a) :
    π.ker = ⊥ := by
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanB 3) ∅, IsRootLift π γ (X π γ) :=
    fun γ hγ => isRootLift_X_three hK le_rfl hπ hcen hγ
  obtain ⟨hγr, hδr⟩ := mem_roots_of_isOrthPair h
  have hker : ∀ γ δ, IsOrthPair γ δ → ∀ a b, ⁅X π γ a, X π δ b⁆ ∈ π.ker := fun γ δ h a b => by
    obtain ⟨hγ, hδ⟩ := mem_roots_of_isOrthPair h
    rw [MonoidHom.mem_ker, map_commutatorElement, (hspec γ hγ).2.1, (hspec δ hδ).2.1,
      commutatorElement_eq_one_iff_mul_comm]
    exact commute_x_of_isOrthPair h a b
  have hc : ∀ s t, ⁅X π γ s, X π δ t⁆ ∈ Subgroup.center E := fun s t => hcen (hker γ δ h s t)
  have hc1 : ⁅X π γ 1, X π δ 1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hcomm _ _ ((hspec γ hγr).2.1 1) ((hspec δ hδr).2.1 1))
  obtain ⟨-, hzp⟩ := commutator_mem_zpowers_of_add hK (hspec γ hγr).1 (hspec δ hδr).1 hc
  have hQ : ∀ s t, ⁅X π γ s, X π δ t⁆ = 1 := fun s t => by
    have := hzp s t
    rwa [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
  have hrr : ∀ (k : Fin 3) (v : Fin 3 → ℤ),
      reflection (cartanB 3) k (reflection (cartanB 3) k v) = v := by
    intro k v
    have h2 : (cartanB 3) k k = 2 := by simp [cartanB]
    simpa [Module.End.mul_apply] using LinearMap.congr_fun (reflection_mul_self h2) v
  have hmem : ∀ (k : Fin 3) {v : Fin 3 → ℤ}, v ∈ roots (isFiniteType_cartanB 3) ∅ →
      reflection (cartanB 3) k v ∈ roots (isFiniteType_cartanB 3) ∅ :=
    fun k v hv => (SpinOdd.Φ 3 K).refl_mem k v hv
  have hrefl : ∀ (k : Fin 3) {γ δ : Fin 3 → ℤ}, γ ∈ roots (isFiniteType_cartanB 3) ∅ →
      δ ∈ roots (isFiniteType_cartanB 3) ∅ →
      ((∀ a b, ⁅X π γ a, X π δ b⁆ = 1) ↔
        ∀ a b, ⁅X π (reflection (cartanB 3) k γ) a, X π (reflection (cartanB 3) k δ) b⁆ = 1) := by
    intro k γ δ hγ hδ
    constructor
    · intro hQ' a b
      have := commutator_mem_of_reflection hπ hcen (fun γ hγ => (hspec γ hγ).2.1)
        (bot_le : (⊥ : Subgroup E) ≤ Subgroup.center E) k hγ hδ
        (fun a b => Subgroup.mem_bot.mpr (hQ' a b)) a b
      exact Subgroup.mem_bot.mp this
    · intro hQ' a b
      have := commutator_mem_of_reflection hπ hcen (fun γ hγ => (hspec γ hγ).2.1)
        (bot_le : (⊥ : Subgroup E) ≤ Subgroup.center E) k (hmem k hγ) (hmem k hδ)
        (fun a b => Subgroup.mem_bot.mpr (hQ' a b)) a b
      rw [hrr, hrr] at this
      exact Subgroup.mem_bot.mp this
  set γ₀ := ofStdB 3 (Pi.single 0 1 + Pi.single 1 1) with hγ₀
  set δ₀ := ofStdB 3 (Pi.single 2 1) with hδ₀
  have h₀ : IsOrthPair γ₀ δ₀ :=
    ⟨0, 1, 2, true, true, true, by decide, by decide, by decide,
      by rw [hγ₀, toStdB_ofStdB]; rfl, by rw [hδ₀, toStdB_ofStdB]; rfl⟩
  obtain ⟨hγ₀r, hδ₀r⟩ := mem_roots_of_isOrthPair h₀
  have hiff : ∀ γ δ, IsOrthPair γ δ → ((∀ a b, ⁅X π γ a, X π δ b⁆ = 1) ↔
      ∀ a b, ⁅X π γ₀ a, X π δ₀ b⁆ = 1) := fun γ δ h' =>
    (isOrthPair_induction (P := fun γ δ => γ ∈ roots (isFiniteType_cartanB 3) ∅ ∧
        δ ∈ roots (isFiniteType_cartanB 3) ∅ ∧ ((∀ a b, ⁅X π γ a, X π δ b⁆ = 1) ↔
          ∀ a b, ⁅X π γ₀ a, X π δ₀ b⁆ = 1))
      ⟨hγ₀r, hδ₀r, Iff.rfl⟩
      (fun k γ δ ⟨hγ, hδ, hi⟩ => ⟨hmem k hγ, hmem k hδ, (hrefl k hγ hδ).symm.trans hi⟩) h').2.2
  have hQ₀ : ∀ a b, ⁅X π γ₀ a, X π δ₀ b⁆ = 1 := (hiff γ δ h).mp hQ
  have horth : ∀ γ δ, IsOrthPair γ δ → ∀ a b, X π γ a * X π δ b = X π δ b * X π γ a :=
    fun γ δ h' a b => commutatorElement_eq_one_iff_mul_comm.mp (((hiff γ δ h').mpr hQ₀) a b)
  obtain ⟨σ, hσ⟩ := exists_section_of_orth hK le_rfl hπ hcen hspec horth
  exact SL2Closed.ker_eq_bot_of_section π hcen σ hσ

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

end CFSG.ClassicalInvolution.ModelFacts.TG3
