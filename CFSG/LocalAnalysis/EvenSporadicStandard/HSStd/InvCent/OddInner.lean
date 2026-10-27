module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Out
import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

@[expose] def OddInner (A : Type*) [Group A] : Prop :=
  ∀ σ : MulAut A, Odd (orderOf σ) → σ ∈ (MulAut.conj : A →* MulAut A).range

theorem prime_dvd_multiset_lcm {r : ℕ} (hr : r.Prime) (M : Multiset ℕ) (h : r ∣ M.lcm) :
    ∃ c ∈ M, r ∣ c := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    exact absurd (Nat.le_of_dvd one_pos h) (by have := hr.two_le; omega)
  | cons a s ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm] at h
    rcases (Nat.Prime.dvd_lcm hr).1 h with h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨c, hc, hrc⟩ := ih h
      exact ⟨c, Multiset.mem_cons_of_mem hc, hrc⟩

theorem perm_fin_six_orderOf_ne_fifteen (σ : Equiv.Perm (Fin 6)) : orderOf σ ≠ 15 := by
  intro h
  have h3 : 3 ∣ orderOf σ := by rw [h]; norm_num
  have h5 : 5 ∣ orderOf σ := by rw [h]; norm_num
  rw [← Equiv.Perm.lcm_cycleType] at h3 h5
  obtain ⟨c, hc, h3c⟩ := prime_dvd_multiset_lcm (by decide) _ h3
  obtain ⟨c', hc', h5c'⟩ := prime_dvd_multiset_lcm (by decide) _ h5
  have hsum : σ.cycleType.sum ≤ 6 := by simpa using Equiv.Perm.sum_cycleType_le σ
  have hle : ∀ x ∈ σ.cycleType, x ≤ σ.cycleType.sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _)
  by_cases hcc : c = c'
  · subst hcc
    have hdvd : 3 * 5 ∣ c :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h3c h5c'
    have hpos : 0 < c := by have := Equiv.Perm.two_le_of_mem_cycleType hc; omega
    have h1 := Nat.le_of_dvd hpos hdvd
    have h2 := hle c hc
    omega
  · have hc'e : c' ∈ σ.cycleType.erase c := (Multiset.mem_erase_of_ne (Ne.symm hcc)).2 hc'
    have e1 : σ.cycleType.sum = c + (σ.cycleType.erase c).sum := by
      conv_lhs => rw [← Multiset.cons_erase hc]
      rw [Multiset.sum_cons]
    have e2 : c' ≤ (σ.cycleType.erase c).sum :=
      Multiset.single_le_sum (fun _ _ => Nat.zero_le _) c' hc'e
    have hcr : 3 ≤ c := Nat.le_of_dvd (by have := Equiv.Perm.two_le_of_mem_cycleType hc; omega) h3c
    have hcs : 5 ≤ c' :=
      Nat.le_of_dvd (by have := Equiv.Perm.two_le_of_mem_cycleType hc'; omega) h5c'
    omega

theorem OddInner.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : OddInner A) :
    OddInner B := by
  intro σ hodd
  let τ : MulAut A := MulAut.congr e.symm σ
  have hoddτ : Odd (orderOf τ) := by
    have h1 : orderOf τ = orderOf σ := MulEquiv.orderOf_eq (MulAut.congr e.symm) σ
    rwa [h1]
  obtain ⟨a, ha⟩ := h τ hoddτ
  refine ⟨e a, ?_⟩
  ext y
  have ha' := congrArg (fun φ : MulAut A => φ (e.symm y)) ha
  simp only [MulAut.conj_apply] at ha'
  have h2 : τ (e.symm y) = e.symm (σ y) := by
    show e.symm (σ ((e.symm).symm (e.symm y))) = e.symm (σ y)
    simp
  rw [h2] at ha'
  have h3 := congrArg e ha'
  simpa [MulAut.conj_apply] using h3

theorem oddInner_of_outSq {A : Type*} [Group A] (h : CFSG.EvenSporadicStandard.SolomonRed.OutSq A) :
    OddInner A := by
  intro σ hodd
  have hsq : σ * σ ∈ (MulAut.conj : A →* MulAut A).range := by
    obtain ⟨a, ha⟩ := h σ
    refine ⟨a, ?_⟩
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply]
    exact (ha x).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one σ) hodd 1
  have hσ : σ = (σ * σ) ^ m := by
    calc σ = σ ^ 1 := (pow_one σ).symm
      _ = σ ^ (2 * m) := hm
      _ = (σ ^ 2) ^ m := pow_mul σ 2 m
      _ = (σ * σ) ^ m := by rw [pow_two]
  rw [hσ]
  exact ((MulAut.conj : A →* MulAut A).range).pow_mem hsq m

theorem oddInner_alternatingGroup_six : OddInner (alternatingGroup (Fin 6)) :=
  oddInner_of_outSq CFSG.EvenSporadicStandard.SolomonRed.outSq_alternatingGroup_six

theorem no_order_fifteen_alternatingGroup_six :
    ∀ a : alternatingGroup (Fin 6), orderOf a ≠ 15 := by
  intro a ha
  have hcoe : orderOf ((a : Equiv.Perm (Fin 6))) = 15 := by
    rw [Subgroup.orderOf_coe]; exact ha
  exact perm_fin_six_orderOf_ne_fifteen (a : Equiv.Perm (Fin 6)) hcoe

end CFSG.EvenSporadicStandard.HSStd.InvCent
