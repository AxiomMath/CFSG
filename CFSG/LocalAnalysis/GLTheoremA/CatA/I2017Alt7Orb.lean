module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017

open Equiv Equiv.Perm Finset

theorem cycleType_eq_five {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} (h5 : orderOf σ = 5)
    (hsupp : #σ.support < 10) : σ.cycleType = {5} := by
  have hne : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h5
    norm_num at h5
  have hpos : σ.cycleType ≠ 0 := fun h => hne (cycleType_eq_zero.1 h)
  have hall : ∀ a ∈ σ.cycleType, a = 5 := by
    intro a ha
    have h2 := two_le_of_mem_cycleType ha
    have hd := dvd_of_mem_cycleType ha
    rw [h5] at hd
    exact (Nat.prime_five.eq_one_or_self_of_dvd a hd).resolve_left (by omega)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 5 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  have hsum5 : σ.cycleType.sum = Multiset.card σ.cycleType * 5 := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul]
  have hsum := sum_cycleType σ
  have hcpos : 0 < Multiset.card σ.cycleType := Multiset.card_pos.2 hpos
  have hc1 : Multiset.card σ.cycleType = 1 := by omega
  rw [hrep, hc1, Multiset.replicate_one]

theorem orderOf_eq_five_of_cycleType {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : σ.cycleType = {5}) : orderOf σ = 5 := by
  rw [← lcm_cycleType, h]
  simp

theorem card_fixed_of_cycleType_five {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    {s : Finset α} (hs : σ.support ⊆ s) (h5 : σ.cycleType = {5}) (hcard : #s = 8) :
    #(s.filter (fun j => σ j = j)) = 3 := by
  have hsum := sum_cycleType σ
  rw [h5, Multiset.sum_singleton] at hsum
  have hfilt : s.filter (fun j => σ j = j) = s \ σ.support := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_support, not_not]
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [hfilt]
  omega

theorem transitive_of_no_fixed {n : ℕ} {s : Finset (Fin n)} (hs : #s = 8)
    {H : Subgroup ↥(alternatingGroup (Fin n))}
    (hHs : ∀ h ∈ H, ∀ i ∉ s, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) i = i)
    (hH : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7))))
    (hno : ∀ i ∈ s, ∃ h ∈ H, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) i ≠ i)
    (ω : Fin n) (hω : ω ∈ s) (j : Fin n) (hj : j ∈ s) :
    ∃ h ∈ H, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ω = j := by
  classical
  have hpres : ∀ h ∈ H, ∀ i ∈ s, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) i ∈ s := by
    intro h hh i hi
    by_contra hni
    have key := hHs h hh _ hni
    have h2 := (((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n))).injective key
    exact hni (by rw [h2]; exact hi)
  set O : Finset (Fin n) := s.filter
    (fun x => ∃ h ∈ H, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ω = x) with hOdef
  have hωO : ω ∈ O := by
    refine Finset.mem_filter.2 ⟨hω, 1, H.one_mem, ?_⟩
    simp
  have hOs : O ⊆ s := Finset.filter_subset _ _
  have hOmem : ∀ x ∈ O, ∃ h ∈ H, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ω = x :=
    fun x hx => (Finset.mem_filter.1 hx).2
  have hOinv : ∀ h ∈ H, ∀ x ∈ O,
      ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x ∈ O := by
    intro h hh x hx
    obtain ⟨g, hg, hgx⟩ := hOmem x hx
    refine Finset.mem_filter.2 ⟨hpres h hh x (hOs hx), h * g, H.mul_mem hh hg, ?_⟩
    rw [← hgx]
    simp
  have hOiff : ∀ h ∈ H, ∀ x : Fin n, x ∈ O ↔ ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x ∈ O := by
    intro h hh x
    constructor
    · exact hOinv h hh x
    · intro hx
      have hinv := hOinv h⁻¹ (H.inv_mem hh) _ hx
      simpa using hinv
  let K : Subgroup ↥H :=
    { carrier := {h | ∀ x ∈ O, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x = x}
      mul_mem' := fun {a b} ha hb x hx => by
        show ((a : ↥(alternatingGroup (Fin n))) : Perm (Fin n))
          (((b : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x) = x
        rw [hb x hx, ha x hx]
      one_mem' := fun x _ => rfl
      inv_mem' := fun {a} ha x hx => by
        show (((((a⁻¹ : ↥H)) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) x = x
        simp only [Subgroup.coe_inv]
        exact Equiv.Perm.inv_eq_iff_eq.2 (ha x hx).symm }
  have hKnorm : K.Normal := by
    refine ⟨fun h hh g => ?_⟩
    have hh' : ∀ x ∈ O, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x = x := hh
    show ∀ x ∈ O, (((g * h * g⁻¹ : ↥H) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x = x
    intro x hx
    have hgx := hOinv _ (H.inv_mem g.2) x hx
    have hfix := hh' _ hgx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply] at hfix ⊢
    rw [hfix]
    simp
  have hK : K = ⊥ := by
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup ↥H := hH.elim fun e => e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      obtain ⟨h0, hh0, hne⟩ := hno ω hω
      have hmem : (⟨h0, hh0⟩ : ↥H) ∈ K := by
        rw [h]
        exact Subgroup.mem_top _
      exact hne (hmem ω hωO)
  let f : ↥H → Perm {x // x ∈ O} := fun h =>
    Equiv.Perm.subtypePerm ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n))
      (fun x => (hOiff h.1 h.2 x).symm)
  have hinj : Function.Injective f := by
    intro h1 h2 heq
    have hagree : ∀ x ∈ O, ((h1 : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x =
        ((h2 : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x := by
      intro x hx
      have := congrArg (fun φ : Perm {x // x ∈ O} => ((φ ⟨x, hx⟩ : {x // x ∈ O}) : Fin n)) heq
      simpa [f, Equiv.Perm.subtypePerm_apply] using this
    have hg : h1⁻¹ * h2 ∈ K := by
      show ∀ x ∈ O, (((h1⁻¹ * h2 : ↥H) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) x = x
      intro x hx
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      rw [← hagree x hx]
      simp
    rw [hK, Subgroup.mem_bot, inv_mul_eq_one] at hg
    exact hg
  have hcardH : Nat.card ↥H = 2520 := by
    obtain ⟨e⟩ := hH
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hcardO : 2520 ≤ (#O).factorial := by
    have hle := Nat.card_le_card_of_injective f hinj
    rw [hcardH, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe] at hle
    exact hle
  have hO7 : 7 ≤ #O := by
    by_contra hlt
    have h6 : (#O).factorial ≤ (6 : ℕ).factorial := Nat.factorial_le (by omega)
    have h720 : (6 : ℕ).factorial = 720 := rfl
    omega
  have hOle : #O ≤ 8 := hs ▸ Finset.card_le_card hOs
  have hOs8 : #O = 8 := by
    by_contra hne
    have h7 : #O = 7 := by omega
    have hsdiff : #(s \ O) = 1 := by
      have := Finset.card_sdiff_add_card_eq_card hOs
      omega
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.1 hsdiff
    have hj₀mem : j₀ ∈ s \ O := by rw [hj₀]; exact Finset.mem_singleton_self _
    obtain ⟨h0, hh0, hne0⟩ := hno j₀ (Finset.mem_sdiff.1 hj₀mem).1
    apply hne0
    have hmem : ((h0 : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j₀ ∈ s \ O := by
      refine Finset.mem_sdiff.2 ⟨hpres h0 hh0 j₀ (Finset.mem_sdiff.1 hj₀mem).1, ?_⟩
      intro hO
      have := (hOiff h0 hh0 j₀).2 hO
      exact (Finset.mem_sdiff.1 hj₀mem).2 this
    rw [hj₀, Finset.mem_singleton] at hmem
    exact hmem
  have hOeq : O = s := Finset.eq_of_subset_of_card_le hOs (by omega)
  rw [← hOeq] at hj
  obtain ⟨h, hh, hhj⟩ := hOmem j hj
  exact ⟨h, hh, hhj⟩

end CFSG.LocalAnalysis.GLTheoremA.I2017
