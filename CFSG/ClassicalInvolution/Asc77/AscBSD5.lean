module

public import CFSG.ClassicalInvolution.Asc77.AscBSD4

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (ModelFund)

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

theorem exists_two_ne_of_three_lt {m : ℕ} (hm : 3 < m) (a b : Fin m) (hab : a ≠ b) :
    ∃ c d : Fin m, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  classical
  have hcard : 1 < (((Finset.univ : Finset (Fin m)).erase a).erase b).card := by
    have h1 : (((Finset.univ : Finset (Fin m)).erase a).erase b).card =
        (Finset.univ : Finset (Fin m)).card - 2 := by
      rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ a)]
      · omega
      · simp [Ne.symm hab]
    rw [h1, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hc hd
  exact ⟨c, d, hcd, hc.2, hc.1, hd.2, hd.1⟩

variable {p f : ℕ} [Fact p.Prime]


@[expose] def FundTwoBound (p : ℕ) [Fact p.Prime] (t : LTag) (n : ℕ) : Prop :=
  ∀ e : ℕ, p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t n p e →
    ∀ {R₁ R₂ R₃ : Subgroup (modelUniv t n p e Fact.out).K}, R₁ ∈ ModelFund p t n e →
      R₂ ∈ ModelFund p t n e → R₃ ∈ ModelFund p t n e →
      ∀ {r₁ r₂ r₃ : (modelUniv t n p e Fact.out).K}, IsInvIn R₁ r₁ → IsInvIn R₂ r₂ →
        IsInvIn R₃ r₃ → r₁ * r₂⁻¹ ∈ Subgroup.center (modelUniv t n p e Fact.out).K →
        r₂ * r₃⁻¹ ∈ Subgroup.center (modelUniv t n p e Fact.out).K →
        R₁ = R₂ ∨ R₂ = R₃ ∨ R₁ = R₃

theorem fundTwoBound_psl_four : FundTwoBound p .PSL 4 := by
  intro e hp2 _ _ R₁ R₂ R₃ h₁ h₂ h₃ r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23
  exact fund_two_bound_psl_four hp2 h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23

theorem fundTwoBound_psu_four : FundTwoBound p .PSU 4 := by
  intro e hp2 hq hadm R₁ R₂ R₃ h₁ h₂ h₃ r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23
  exact fund_two_bound_psu_four hp2 hq hadm h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23

section Twins

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
variable {C : XCtx p f (𝒞 K) z}

theorem twin_ne_twin {e₁ e₂ : Fin C.D.card} (hne : e₁ ≠ e₂)
    (he₁ : C.D.tag e₁ = .PSL ∧ C.D.rank e₁ = 2) (he₂ : C.D.tag e₂ = .PSL ∧ C.D.rank e₂ = 2)
    (m₁ : CompMem C e₁) (hm₁ : m₁.nbar = zbar z) (m₂ : CompMem C e₂) (hm₂ : m₂.nbar = zbar z) :
    m₁.N ≠ m₂.N := by
  intro h
  obtain ⟨hcl₁, hmod₁⟩ := classical_of_nbar_eq C he₁ m₁ hm₁
  obtain ⟨hcl₂, hmod₂⟩ := classical_of_nbar_eq C he₂ m₂ hm₂
  have hrange : (C.psi e₁).range = (C.psi e₂).range := by rw [← hmod₁, ← hmod₂, h]
  have hz : zbar z ∈ (C.psi e₁).range := by
    rw [← hmod₁]
    exact oddQuotMk_mem_modOdd hcl₁.mem (XCtx.hzC z)
  refine C.range_not_comm_of_A1 e₁ he₁ hz ?_
  intro a ha b hb
  rw [hrange] at hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact C.psi_commute hne a' b'

end Twins

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
