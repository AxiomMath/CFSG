module

public import CFSG.GH74.Generic.BProg.B3.S3SD7DichP0
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Generic.BProg.B3

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.Generic.BProg.B3.S3SD7DichP0
open scoped commutatorElement

namespace S3Sec29I

theorem perfect_sylow_two_not_cyclic {J : Type} [Group J] [Finite J] (hperf : Group.IsPerfect J)
    (heven : 2 ∣ Nat.card J) (T : Sylow 2 J) : ¬ IsCyclic ↥T := by
  intro hcyclic
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card J).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  let transfer := MonoidHom.transferSylow T (hcyclic.normalizer_le_centralizer hmin)
  have hcomplement : transfer.ker.IsComplement' (T : Subgroup J) :=
    hcyclic.isComplement' hmin
  have hker : transfer.ker = ⊤ := by
    rw [eq_top_iff]
    have hle : commutator J ≤ transfer.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (IsMulCommutative.is_comm.comm _ _)
    rw [Group.isPerfect_def.mp hperf] at hle
    exact hle
  rw [hker] at hcomplement
  exact T.ne_bot_of_dvd_card heven (Subgroup.isComplement'_top_left.mp hcomplement)

theorem even_card_of_perfect {J : Type} [Group J] [Finite J] [Nontrivial J]
    (hperf : Group.IsPerfect J) : 2 ∣ Nat.card J := by
  by_contra h
  have hodd : Odd (Nat.card J) := by
    rcases Nat.even_or_odd (Nat.card J) with he | ho
    · exact absurd (even_iff_two_dvd.mp he) h
    · exact ho
  have hsolv : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.IsPerfect.not_isSolvable J hsolv

theorem exp4_check : P0l.all (fun a => pe (a * a * a * a) 1) = true := by decide +kernel

theorem key_check : P0l.all (fun a => P0l.all fun b =>
    pe (a * a) 1 || pe b 1 || pe b a || pe b (a * a) || pe b (a * a * a) ||
      (pe (b * b) 1 && !pe b (a * a)) ||
      (pe ((a * b) * (a * b)) 1 && !pe (a * b) (a * a) && !pe (a * b) 1)) = true := by
  decide +kernel

theorem isCyclic_of_le_P0 {T : Subgroup (Perm (Fin 7))} (hTP : T ≤ P0)
    (huniq : ∀ s ∈ T, ∀ t ∈ T, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s = t) :
    IsCyclic ↥T := by
  classical
  by_cases hex : ∃ a ∈ T, a * a ≠ 1
  · obtain ⟨a, haT, ha2⟩ := hex
    have haP : a ∈ P0l := mem_P0.1 (hTP haT)
    have h4 : a * a * a * a = 1 :=
      pe_iff.1 (List.all_eq_true.1 exp4_check a haP)
    have hmem : ∀ b ∈ T, b ∈ Subgroup.zpowers a := by
      intro b hbT
      have hbP : b ∈ P0l := mem_P0.1 (hTP hbT)
      have hk := List.all_eq_true.1 (List.all_eq_true.1 key_check a haP) b hbP
      by_cases hb1 : b = 1
      · rw [hb1]; exact Subgroup.one_mem _
      by_cases hba : b = a
      · rw [hba]; exact Subgroup.mem_zpowers a
      by_cases hba2 : b = a * a
      · rw [hba2, ← pow_two]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2
      by_cases hba3 : b = a * a * a
      · rw [hba3, show a * a * a = a ^ 3 by rw [pow_succ, pow_two]]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 3
      exfalso
      have hs : a * a ∈ T := T.mul_mem haT haT
      have hs2 : (a * a) * (a * a) = 1 := by
        have : (a * a) * (a * a) = a * a * a * a := by group
        rw [this, h4]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', pe_iff, pe_eq_false_iff] at hk
      rcases hk with ((((((hk | hk) | hk) | hk) | hk) | hk) | hk)
      · exact ha2 hk
      · exact hb1 hk
      · exact hba hk
      · exact hba2 hk
      · exact hba3 hk
      · exact hk.2 (huniq b hbT (a * a) hs hk.1 hs2 hb1 ha2)
      · have habT : a * b ∈ T := T.mul_mem haT hbT
        have := huniq (a * a) hs (a * b) habT hs2 hk.1.1 ha2 hk.2
        exact hk.1.2 this.symm
    refine ⟨⟨⟨a, haT⟩, fun ⟨t, ht⟩ => ?_⟩⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hmem t ht)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · push Not at hex
    by_cases hne : ∃ s ∈ T, s ≠ 1
    · obtain ⟨s, hsT, hs1⟩ := hne
      refine ⟨⟨⟨s, hsT⟩, fun ⟨t, ht⟩ => ?_⟩⟩
      by_cases ht1 : t = 1
      · exact ⟨0, Subtype.ext (by simp [ht1])⟩
      · have := huniq s hsT t ht (hex s hsT) (hex t ht) hs1 ht1
        exact ⟨1, Subtype.ext (by simp [this])⟩
    · push Not at hne
      refine ⟨⟨1, fun ⟨t, ht⟩ => ⟨0, Subtype.ext (by simp [hne t ht])⟩⟩⟩

theorem factQ (T : Subgroup (Perm (Fin 7))) (hT : IsPGroup 2 ↥T) (hnc : ¬ IsCyclic ↥T) :
    ∃ s ∈ T, ∃ t ∈ T, s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧ s * s = 1 ∧ t * t = 1 := by
  obtain ⟨σ, hσ⟩ := exists_conj_le_P0 T hT
  by_contra hno
  apply hnc
  have hinj : Function.Injective (MulAut.conj σ).toMonoidHom := (MulAut.conj σ).injective
  have hcyc : IsCyclic ↥(T.map (MulAut.conj σ).toMonoidHom) := by
    refine isCyclic_of_le_P0 hσ ?_
    rintro _ ⟨s0, hs0, rfl⟩ _ ⟨t0, ht0, rfl⟩ hs ht hs1 ht1
    rw [← map_mul, map_eq_one_iff _ hinj] at hs ht
    rw [Ne, map_eq_one_iff _ hinj] at hs1 ht1
    by_contra hne
    exact hno ⟨s0, hs0, t0, ht0, hs1, ht1, fun h => hne (by rw [h]), hs, ht⟩
  have := hcyc
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective T (MulAut.conj σ).toMonoidHom hinj).symm.toMonoidHom
    (Subgroup.equivMapOfInjective T (MulAut.conj σ).toMonoidHom hinj).symm.surjective

theorem eq_bot_of_perfect_of_solvable {G : Type*} [Group G] {H : Subgroup G} (hperf : ⁅H, H⁆ = H)
    (hsolv : Group.IsSolvable ↥H) : H = ⊥ := by
  by_contra hne
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isSolvable ↥H hsolv

theorem perfect_le_centralizer_even_invol (H : Subgroup (Perm (Fin 7))) (hperf : ⁅H, H⁆ = H)
    (t : Perm (Fin 7)) (hcard : t.support.card = 4) (hH : H ≤ centralizer {t}) : H = ⊥ := by
  classical
  have hsupp : ∀ h ∈ H, ∀ i, h i ∈ t.support ↔ i ∈ t.support := by
    intro h hh i
    have hc : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.1 (hH hh)
    have hc' : ∀ j, t (h j) = h (t j) := fun j => by
      have := congrArg (fun f : Perm (Fin 7) => f j) hc
      simpa using this.symm
    simp only [Equiv.Perm.mem_support]
    rw [hc' i]
    exact not_congr ⟨fun h1 => h.injective (by rw [h1]), fun h1 => by rw [h1]⟩
  let φ : ↥H →* Perm {i // i ∈ t.support} × Perm {i // i ∉ t.support} :=
    { toFun := fun h => (h.1.subtypePerm (hsupp h.1 h.2),
        h.1.subtypePerm (fun i => not_congr (hsupp h.1 h.2 i)))
      map_one' := Prod.ext (Equiv.ext fun i => Subtype.ext rfl) (Equiv.ext fun i => Subtype.ext rfl)
      map_mul' := fun a b => Prod.ext (Equiv.ext fun i => Subtype.ext rfl)
        (Equiv.ext fun i => Subtype.ext rfl) }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ t.support
    · have := congrArg (fun p => ((p.1 ⟨i, hi⟩ : {i // i ∈ t.support}) : Fin 7)) hab
      simpa [φ] using this
    · have := congrArg (fun p => ((p.2 ⟨i, hi⟩ : {i // i ∉ t.support}) : Fin 7)) hab
      simpa [φ] using this
  have h1 : Group.IsSolvable (Perm {i // i ∈ t.support}) := by
    refine Equiv.Perm.isSolvable ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
  have h2 : Group.IsSolvable (Perm {i // i ∉ t.support}) := by
    refine Equiv.Perm.isSolvable ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe, hcard]
    simp
  have := h1
  have := h2
  exact eq_bot_of_perfect_of_solvable hperf (Group.isSolvable_of_isSolvable_injective hφ)

end S3Sec29I

end CFSG.GH74.Generic.BProg.B3
