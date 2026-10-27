module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpComp
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A]

theorem pCore_le_centralizer_comp {J : Subgroup A} (hJ : IsComponent J) (q : ℕ) [Fact q.Prime] :
    pCore q A ≤ centralizer (J : Set A) := by
  have hnil := pCore_isNilpotent (p := q) (G := A)
  have hsolv : Group.IsSolvable ↥(pCore q A) := inferInstance
  have h := (CFSG.LocalCores.component_solvable_centralizer (G := A) hsolv
    (pCore_normal (p := q) (G := A)).isSubnormal).1 J hJ
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem exists_involution_comp {J : Subgroup A} (hJ : IsComponent J) : ∃ c ∈ J, orderOf c = 2 := by
  obtain ⟨u, hu⟩ := exists_orderOf_eq_two_of_isQuasisimple (J := ↥J) hJ.1
  exact ⟨(u : A), u.2, by rw [Subgroup.orderOf_coe]; exact hu⟩

theorem comp_eq_of_no_invol {J : Subgroup A} (hJ : IsComponent J)
    (hf : ∀ c : A, orderOf c = 2 → c ∈ centralizer (J : Set A) → False) {J' : Subgroup A}
    (hJ' : IsComponent J') : J' = J := by
  by_contra hne
  obtain ⟨c, hcJ', hc⟩ := exists_involution_comp hJ'
  refine hf c hc ?_
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (comp_comm_of_ne hJ' hJ hne)) hcJ'

theorem pCore_two_eq_bot_of_no_invol {J : Subgroup A} (hJ : IsComponent J)
    (hf : ∀ c : A, orderOf c = 2 → c ∈ centralizer (J : Set A) → False) : pCore 2 A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hpg : IsPGroup 2 ↥(pCore 2 A) := pCore_isPGroup (p := 2) (G := A)
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    have h1 : Nat.card ↥(pCore 2 A) = 1 := by simpa using hn
    exact (Subgroup.eq_bot_of_card_eq _ h1)
  have h2 : 2 ∣ Nat.card ↥(pCore 2 A) := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine hf (u : A) (by rw [Subgroup.orderOf_coe]; exact hu) ?_
  exact pCore_le_centralizer_comp hJ 2 u.2

omit [Finite A] in
theorem layer_eq_of_unique {J : Subgroup A} (hJ : IsComponent J)
    (h : ∀ J' : Subgroup A, IsComponent J' → J' = J) : layer A = J :=
  le_antisymm (sSup_le fun J' hJ' => (h J' hJ').le) (le_sSup hJ)

omit [Finite A] in
theorem normal_of_unique {J : Subgroup A} (hJ : IsComponent J)
    (h : ∀ J' : Subgroup A, IsComponent J' → J' = J) : J.Normal := by
  have := layer_eq_of_unique hJ h
  have hc := CFSG.LocalCores.layer_characteristic (G := A)
  rw [← this]
  infer_instance

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
