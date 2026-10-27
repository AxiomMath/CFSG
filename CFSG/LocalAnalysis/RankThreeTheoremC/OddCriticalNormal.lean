module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

private theorem critical_exists_prime_pCore_not_commuting {X : Type} [Group X] [Finite X]
    {L O : Subgroup X} (hOL : O ≤ L) (hOs : Group.IsSolvable O) (h : ⁅L, O⁆ ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ ⁅L, inSubgroup (pCore q) O⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply h
  have hF : (fittingSubgroup O).map O.subtype ≤ Subgroup.centralizer (L : Set X) := by
    rw [fitting_eq_sup_pCore O, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    have h1 := hcon p.1.1 (Nat.prime_of_mem_primeFactors p.1.2)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    exact h1
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  have hxO : (⟨x, hx⟩ : O) ∈ Subgroup.centralizer (fittingSubgroup O : Set O) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfL := hF (Subgroup.mem_map_of_mem O.subtype hf)
    have := Subgroup.mem_centralizer_iff.mp hfL x (hOL hx)
    exact Subtype.ext this.symm
  have hxF := CFSG.RankThree.PGroups.solvable_fitting_self_centralizing O hxO
  exact hF (Subgroup.mem_map_of_mem O.subtype hxF)

private theorem critical_eq_one_of_fixing_pGroup_of_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) {P : Type*} [Group P] {D : Set P}
    (hfix : IsPGroup q (fixingSubgroup (MulAut P) D))
    {σ : MulAut P} (hσD : ∀ d ∈ D, σ d = d) {k : ℕ} (hσ : σ ^ (p ^ k) = 1) : σ = 1 := by
  have hmem : σ ∈ fixingSubgroup (MulAut P) D := by
    rw [mem_fixingSubgroup_iff (MulAut P)]
    exact hσD
  obtain ⟨j, hj⟩ := hfix ⟨σ, hmem⟩
  have hj' : σ ^ (q ^ j) = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (q ^ j) (p ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).mpr hqp)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hσ)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

private theorem critical_le_centralizer_of_centralizes_critical_subgroup {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≠ p) {X : Type*} [Group X] {Q T : Subgroup X} [Q.Normal]
    (hT : IsPGroup p T) (D₀ : Subgroup Q)
    (hfix : IsPGroup q (fixingSubgroup (MulAut Q) (D₀ : Set Q)))
    (hTD : T ≤ Subgroup.centralizer ((D₀.map Q.subtype : Subgroup X) : Set X)) :
    T ≤ Subgroup.centralizer (Q : Set X) := by
  intro t ht
  let σ : MulAut Q := MulAut.conjNormal t
  have hσD : ∀ d ∈ (D₀ : Set Q), σ d = d := by
    intro d hd
    apply Subtype.ext
    show t * (d : X) * t⁻¹ = d
    have h := Subgroup.mem_centralizer_iff.mp (hTD ht) (d : X)
      (Subgroup.mem_map_of_mem Q.subtype hd)
    calc t * d * t⁻¹ = d * t * t⁻¹ := by rw [← h]
      _ = d := by group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have ht1 : t ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hσk : σ ^ (p ^ k) = 1 := by
    rw [← map_pow, ht1, map_one]
  have hσ1 := critical_eq_one_of_fixing_pGroup_of_pow hp hq hqp hfix hσD hσk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg (fun φ : MulAut Q => ((φ ⟨x, hx⟩ : Q) : X)) hσ1
  change t * x * t⁻¹ = x at h
  calc x * t = t * x * t⁻¹ * t := by rw [h]
    _ = t * x := by group

theorem exists_critical_normal {J : Type} [Group J] [Finite J] {O : Subgroup J} [O.Normal]
    (hOs : Group.IsSolvable O) (hOodd : Odd (Nat.card O))
    (hO : ⁅(⊤ : Subgroup J), O⁆ ≠ ⊥) {p : ℕ} [Fact p.Prime] (hpO : ¬ p ∣ Nat.card O)
    {U : Subgroup J} (hU : IsPGroup p U)
    (hJ : Subgroup.normalClosure (U : Set J) ⊔ O = ⊤) (hperf : commutator J = ⊤) :
    ∃ (q : ℕ) (D : Subgroup J), q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ D.Normal ∧ D ≠ ⊥ ∧ D ≤ O ∧
      (∀ x ∈ D, x ^ q = 1) ∧ ⁅⁅D, D⁆, D⁆ = ⊥ ∧ ⁅U, D⁆ ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq, hQ⟩ := critical_exists_prime_pCore_not_commuting (le_top : O ≤ ⊤) hOs hO
  have : Fact q.Prime := ⟨hq⟩
  set Q : Subgroup J := inSubgroup (pCore q) O with hQdef
  have hQO : Q ≤ O := Subgroup.map_subtype_le _
  have hQnormal : Q.Normal := by
    rw [hQdef, inSubgroup]
    infer_instance
  have hQq : IsPGroup q Q := (pCore_isPGroup (p := q) (G := O)).map O.subtype
  have hQ1 : Q ≠ ⊥ := fun h => hQ (by rw [h, Subgroup.commutator_bot_right])
  have hqO : q ∣ Nat.card O := by
    rcases hQq.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQ1
    · exact h.trans (Subgroup.card_dvd_of_le hQO)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hqO)
  have hqp : q ≠ p := fun h => hpO (h ▸ hqO)
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  obtain ⟨D₀, hD₀char, hD₀1, hD₀cl, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQq
  refine ⟨q, D₀.map Q.subtype, hq, hq2, hqp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hQnormal
    have := hD₀char
    infer_instance
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective]
    exact hD₀1
  · exact (Subgroup.map_subtype_le D₀).trans hQO
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hD₀exp y hy, Subgroup.coe_one]
  · have h1 : ⁅D₀, D₀⁆ ≤ Subgroup.centralizer (D₀ : Set Q) :=
      (Subgroup.commutator_mono le_rfl le_top).trans (hD₀cl.trans inf_le_right)
    have h2 : ⁅⁅D₀, D₀⁆, D₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, h2, Subgroup.map_bot]
  · intro h0
    have := hQnormal
    have hUD : U ≤ Subgroup.centralizer ((D₀.map Q.subtype : Subgroup J) : Set J) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hUC := critical_le_centralizer_of_centralizes_critical_subgroup hp hq hqp hU D₀
      hD₀fix hUD
    have hcl : Subgroup.normalClosure (U : Set J) ≤ Subgroup.centralizer (Q : Set J) :=
      Subgroup.normalClosure_le_normal hUC
    set C : Subgroup J := Subgroup.centralizer (Q : Set J) with hCdef
    have hCN : C.Normal := inferInstance
    have hCO : C ⊔ O = ⊤ := by
      refine top_unique ?_
      rw [← hJ]
      exact sup_le_sup_right hcl O
    have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp O.subtype) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hg : g ∈ C ⊔ O := hCO ▸ mem_top g
      obtain ⟨c, hc, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      refine ⟨⟨o, ho⟩, ?_⟩
      change (o : J ⧸ C) = ((c * o : J) : J ⧸ C)
      rw [QuotientGroup.eq, ← mul_assoc]
      exact hCN.conj_mem' c hc o
    have : Group.IsSolvable O := hOs
    have : Group.IsSolvable (J ⧸ C) := Group.isSolvable_of_surjective hsurj
    have : Group.IsPerfect J := ⟨hperf⟩
    have hsub : Subsingleton (J ⧸ C) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (J ⧸ C) inferInstance
    have hCtop : ∀ g : J, g ∈ C := fun g =>
      (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    exact hQ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun g _ => hCtop g)

end CFSG.LocalAnalysis.RankThreeTheoremC
