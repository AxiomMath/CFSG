module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CentExt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4FStar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem pCore_two_le_centralizer (T : Sylow 2 Γ) {p : ℕ} [Fact p.Prime] {P : Subgroup Γ}
    (hP : IsPGroup p ↥P) (hp2 : p ≠ 2) (hTP : (T : Subgroup Γ) ≤ normalizer (P : Set Γ)) {a : Γ}
    (ha : a ∈ P) : pCore 2 Γ ≤ centralizer ({a} : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxT : x ∈ (T : Subgroup Γ) := fitting_pCore_le_sylow T hx
  have hxP : x * a * x⁻¹ ∈ P := (mem_normalizer_iff.mp (hTP hxT) a).mp ha
  have hc1 : x * a * x⁻¹ * a⁻¹ ∈ P := P.mul_mem hxP (P.inv_mem ha)
  have hc2 : x * a * x⁻¹ * a⁻¹ ∈ pCore 2 Γ := by
    have : x * (a * x⁻¹ * a⁻¹) = x * a * x⁻¹ * a⁻¹ := by group
    rw [← this]
    exact (pCore 2 Γ).mul_mem hx (pCore_normal.conj_mem _ ((pCore 2 Γ).inv_mem hx) a)
  obtain ⟨k, hk⟩ := hP ⟨_, hc1⟩
  obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := Γ)) ⟨_, hc2⟩
  have hk' : (x * a * x⁻¹ * a⁻¹) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm' : (x * a * x⁻¹ * a⁻¹) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
      (Ne.symm hp2))
  have h1 := eq_one_of_pow_pow_of_pow hcop hm' hk'
  have h2 : x * a = a * x := by
    have : x * a * x⁻¹ * a⁻¹ = 1 := h1
    calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
      _ = a * x := by rw [this, one_mul]
  exact h2

theorem fitting_le_centralizer (T : Sylow 2 Γ) {p : ℕ} [Fact p.Prime] {P : Subgroup Γ}
    (hP : IsPGroup p ↥P) (hp2 : p ≠ 2) (hO : pCore p Γ = ⊥)
    (hTP : (T : Subgroup Γ) ≤ normalizer (P : Set Γ)) {a : Γ} (ha : a ∈ P)
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
        exact pCore_two_le_centralizer T hP hp2 hTP ha
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

theorem exists_component_not_le_centralizer (T : Sylow 2 Γ) {p : ℕ} [Fact p.Prime]
    {P : Subgroup Γ} (hP : IsPGroup p ↥P) (hp2 : p ≠ 2) (hO : pCore p Γ = ⊥)
    (hTP : (T : Subgroup Γ) ≤ normalizer (P : Set Γ)) {a : Γ} (ha : a ∈ P) (ha1 : a ≠ 1)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Γ, Q.Normal → IsPGroup r ↥Q →
      Q ≤ centralizer ({a} : Set Γ)) :
    ∃ K : Subgroup Γ, IsComponent K ∧ ¬ K ≤ centralizer ({a} : Set Γ) := by
  have hF := fitting_le_centralizer T hP hp2 hO hTP ha hodd
  have hap : ∃ k : ℕ, a ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  by_contra hcon
  push Not at hcon
  have hlayer : layer Γ ≤ centralizer ({a} : Set Γ) :=
    sSup_le fun K hK => hcon K hK
  exact not_layer_le_centralizer_of_fstar hO ha1 hap
    (fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp (hF hx)).symm) hlayer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
