module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4FStar
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem fitting_le_centralizer' {p : ℕ} [Fact p.Prime] (hO : pCore p Γ = ⊥) {a : Γ}
    (h2 : pCore 2 Γ ≤ centralizer ({a} : Set Γ))
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Γ, Q.Normal → IsPGroup r ↥Q →
      Q ≤ centralizer ({a} : Set Γ)) :
    fittingSubgroup Γ ≤ centralizer ({a} : Set Γ) := by
  have hcent : ∀ q : ℕ, q.Prime → pCore q Γ ≤ centralizer ({a} : Set Γ) := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    by_cases hqp : q = p
    · rw [hqp, hO]
      exact bot_le
    · by_cases hq2 : q = 2
      · rw [hq2]
        exact h2
      · exact hodd q hq hq2 hqp _ pCore_normal pCore_isPGroup
  have hmain : zpowers a ≤ centralizer (fittingSubgroup Γ : Set Γ) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    have hqp : (q.1.1).Prime := Nat.prime_of_mem_primeFactors q.1.2
    rw [zpowers_le, Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent _ hqp hs)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (zpowers_le.mp hmain)) x hx

theorem exists_component_not_le_centralizer' {p : ℕ} [Fact p.Prime] (hO : pCore p Γ = ⊥)
    {a : Γ} (hap : ∃ k : ℕ, a ^ p ^ k = 1) (ha1 : a ≠ 1)
    (h2 : pCore 2 Γ ≤ centralizer ({a} : Set Γ))
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Γ, Q.Normal → IsPGroup r ↥Q →
      Q ≤ centralizer ({a} : Set Γ)) :
    ∃ K : Subgroup Γ, IsComponent K ∧ ¬ K ≤ centralizer ({a} : Set Γ) := by
  have hF := fitting_le_centralizer' hO h2 hodd
  by_contra hcon
  push Not at hcon
  have hlayer : layer Γ ≤ centralizer ({a} : Set Γ) :=
    sSup_le fun K hK => hcon K hK
  exact not_layer_le_centralizer_of_fstar hO ha1 hap
    (fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp (hF hx)).symm) hlayer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
