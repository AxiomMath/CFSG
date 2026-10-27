module

public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineFi22

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

theorem isSolvable_of_card_eq_two {G : Type*} [Group G] (h : Nat.card G = 2) :
    Group.IsSolvable G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic G := isCyclic_of_prime_card h
  let _ := IsCyclic.commGroup (α := G)
  exact Group.isSolvable_of_comm (fun a b => mul_comm a b)

theorem two_mul_card_quotient_center_of_isComponent_perm {n : ℕ} (hn : 5 ≤ n)
    {B : Subgroup (Equiv.Perm (Fin n))} (hB : IsComponent B) :
    2 * Nat.card (B ⧸ center B) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hA : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have hq : Nat.card (Equiv.Perm (Fin n) ⧸ alternatingGroup (Fin n)) = 2 := by
    rw [← Subgroup.index, alternatingGroup.index_eq_two]
  have hnp : ¬ (Nat.card (alternatingGroup (Fin n))).Prime := by
    intro hp
    have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [← hA] at h3
    have h3' : 3 ∣ Nat.card (alternatingGroup (Fin n)) :=
      (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 2)).mp h3
    have h120 : 120 ≤ n.factorial := by
      calc 120 = Nat.factorial 5 := by decide
        _ ≤ n.factorial := Nat.factorial_le hn
    rcases hp.eq_one_or_self_of_dvd 3 h3' with h | h
    · omega
    · omega
  have hnc := Sporadic.FischerOddCore.exists_noncomm_of_isSimpleGroup hs hnp
  rw [Sporadic.FischerOddCore.card_quotient_center_of_component_of_normal_simple
    (isSolvable_of_card_eq_two hq) hs hnc hB]
  exact hA

theorem two_mul_card_quotient_center_of_isComponent_of_mulEquiv_perm {n : ℕ} (hn : 5 ≤ n)
    {G : Type*} [Group G] (e : G ≃* Equiv.Perm (Fin n)) {B : Subgroup G} (hB : IsComponent B) :
    2 * Nat.card (B ⧸ center B) = n.factorial := by
  obtain ⟨hB', hc⟩ := Sporadic.FischerOddCore.component_quotient_mulEquiv e hB
  rw [hc]
  exact two_mul_card_quotient_center_of_isComponent_perm hn hB'

theorem card_quotient_center_of_isComponent_of_mulEquiv_perm_ten {G : Type*} [Group G]
    (e : G ≃* Equiv.Perm (Fin 10)) {B : Subgroup G} (hB : IsComponent B) :
    Nat.card (B ⧸ center B) = 1814400 := by
  have h := two_mul_card_quotient_center_of_isComponent_of_mulEquiv_perm (by norm_num) e hB
  rw [show Nat.factorial 10 = 3628800 by decide] at h
  omega

section HN


theorem hn_outer_card_quotient_center {S : Type} [Group S] (e : S ≃* NativeSporadic.HN)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 1814400 := by
  obtain ⟨φ⟩ := ComponentClassification.RestrictedStd.Spor.hnOuterFixInput S e σ hσ hout
  exact card_quotient_center_of_isComponent_of_mulEquiv_perm_ten
    ((MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub σ)).trans φ) hD

end HN

end CFSG.SeitzReduction.SporadicRefine
