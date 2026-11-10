
module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model

@[expose] public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.Sporadic.SmallOddCore

theorem card_P : Nat.card P = 3265920 := by
  rw [← Nat.card_congr psiEquiv.toEquiv, card_X₀]

def InvCoset (k : ℕ) : Set (Equiv.Perm (Fin 820)) :=
  {β | ∃ g ∈ P, β = g * tP k ∧ β * β = 1}

theorem finite_InvCoset (k : ℕ) : (InvCoset k).Finite := Set.toFinite _

theorem subset_union_of_ncard {α : Type*} {S A B : Set α} (hS : S.Finite) (hA : A ⊆ S)
    (hB : B ⊆ S) (hd : Disjoint A B) (h : A.ncard + B.ncard = S.ncard) : S ⊆ A ∪ B := by
  have hAB : A ∪ B ⊆ S := Set.union_subset hA hB
  have hfA : A.Finite := hS.subset hA
  have hfB : B.Finite := hS.subset hB
  have h2 : (A ∪ B).ncard = S.ncard := by rw [Set.ncard_union_eq hd hfA hfB, h]
  exact (Set.eq_of_subset_of_ncard_le hAB h2.ge hS).ge

theorem subset_of_ncard {α : Type*} {S A : Set α} (hS : S.Finite) (hA : A ⊆ S)
    (h : A.ncard = S.ncard) : S ⊆ A :=
  (Set.eq_of_subset_of_ncard_le hA h.ge hS).ge

section Cover

theorem tP_normalizes {k : ℕ} {p : Equiv.Perm (Fin 820)} (hp : p ∈ P) :
    tP k * p * (tP k)⁻¹ ∈ P :=
  (mem_normalizer_iff.1 (tP_mem_normalizer k) p).1 hp

theorem repCoset_lt {j : ℕ} (hj : j < 9) : repCoset[j]! < 8 := by
  interval_cases j <;> decide

theorem rP_mem_InvCoset {j : ℕ} (hj : j < 9) : rP j ∈ InvCoset repCoset[j]! := by
  have h := checks.2.2.2.2.2
  simp only [repCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h j hj
  have hk := repCoset_lt hj
  have hrep := rep_rP hj
  have hsq : rP j * rP j = 1 :=
    (eqA_iff (rep_compA hrep hrep) rep_idA).1 h1
  have hmem : rP j * (tP repCoset[j]!)⁻¹ ∈ P :=
    (inP_iff (rep_compA hrep (rep_tArr_inv hk))).1 h2
  refine ⟨rP j * (tP repCoset[j]!)⁻¹, hmem, by group, hsq⟩

theorem rP_mul_self {j : ℕ} (hj : j < 9) : rP j * rP j = 1 := (rP_mem_InvCoset hj).choose_spec.2.2

theorem conjClass_subset_InvCoset {j : ℕ} (hj : j < 9) :
    conjClass P (rP j) ⊆ InvCoset repCoset[j]! := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨g, hg, hr, hr2⟩ := rP_mem_InvCoset hj
  set k := repCoset[j]!
  refine ⟨c * g * (tP k * c⁻¹ * (tP k)⁻¹), P.mul_mem (P.mul_mem hc hg) ?_, ?_, ?_⟩
  · have := tP_normalizes (k := k) (P.inv_mem hc)
    exact this
  · rw [hr]
    group
  · have h2 := rP_mul_self hj
    calc c * rP j * c⁻¹ * (c * rP j * c⁻¹) = c * (rP j * rP j) * c⁻¹ := by group
      _ = 1 := by rw [h2]; group

theorem conjClass_eq_of_mem {a b x : Equiv.Perm (Fin 820)} (ha : x ∈ conjClass P a)
    (hb : x ∈ conjClass P b) : conjClass P a = conjClass P b := by
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨h, hh, hgh⟩ := hb
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c * g⁻¹ * h, ?_, ?_⟩
    · exact P.mul_mem (P.mul_mem hc (P.inv_mem hg)) hh
    · have : a = g⁻¹ * h * b * (g⁻¹ * h)⁻¹ := by
        have h1 : g * a * g⁻¹ = h * b * h⁻¹ := hgh
        calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
          _ = g⁻¹ * (h * b * h⁻¹) * g := by rw [h1]
          _ = g⁻¹ * h * b * (g⁻¹ * h)⁻¹ := by group
      rw [this]
      group
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c * h⁻¹ * g, ?_, ?_⟩
    · exact P.mul_mem (P.mul_mem hc (P.inv_mem hh)) hg
    · have : b = h⁻¹ * g * a * (h⁻¹ * g)⁻¹ := by
        have h1 : g * a * g⁻¹ = h * b * h⁻¹ := hgh
        calc b = h⁻¹ * (h * b * h⁻¹) * h := by group
          _ = h⁻¹ * (g * a * g⁻¹) * h := by rw [h1]
          _ = h⁻¹ * g * a * (h⁻¹ * g)⁻¹ := by group
      rw [this]
      group

theorem disjoint_conjClass_of_ne {a b : Equiv.Perm (Fin 820)}
    (h : (conjClass P a).ncard ≠ (conjClass P b).ncard) :
    Disjoint (conjClass P a) (conjClass P b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact h (by rw [conjClass_eq_of_mem hxa hxb])

theorem ncard_conjClass_one : (conjClass P (1 : Equiv.Perm (Fin 820))).ncard = 1 := by
  have : conjClass P (1 : Equiv.Perm (Fin 820)) = {1} := by
    ext x
    simp only [mem_conjClass, mul_one, mul_inv_cancel, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, -, rfl⟩
      rfl
    · rintro rfl
      exact ⟨1, P.one_mem, rfl⟩
  rw [this, Set.ncard_singleton]

theorem conjClass_one_subset : conjClass P (1 : Equiv.Perm (Fin 820)) ⊆ InvCoset 0 := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c * 1 * c⁻¹, by simp, by simp [tP_zero], by simp⟩

theorem dP_pow_four : dP ^ 4 = 1 := by
  have h := checks.2.2.1
  simp only [relCheck, Bool.and_eq_true] at h
  exact (eqA_iff (rep_powA rep_dP 4) rep_idA).1 h.1.1

theorem tP_two_not_mem : tP 2 ∉ P := by
  have := tP_mul_inv_not_mem (k := 2) (k' := 0) (by norm_num) (by norm_num) (by norm_num)
  rwa [tP_zero, inv_one, mul_one] at this

theorem sq_mem_of_involution {g t : Equiv.Perm (Fin 820)} (hg : g ∈ P)
    (ht : t ∈ normalizer (P : Set (Equiv.Perm (Fin 820)))) (h : g * t * (g * t) = 1) :
    t * t ∈ P := by
  have h1 := (mem_normalizer_iff.1 ht g).1 hg
  have h2 : t * t = (g * (t * g * t⁻¹))⁻¹ := by
    have h3 : g * (t * g * t⁻¹) * (t * t) = 1 := by
      calc g * (t * g * t⁻¹) * (t * t) = g * t * (g * t) := by group
        _ = 1 := h
    exact eq_inv_of_mul_eq_one_right h3
  rw [h2]
  exact P.inv_mem (P.mul_mem hg h1)

theorem no_involution_odd {k : ℕ} (hk : k = 1 ∨ k = 3) {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) :
    g * tP k * (g * tP k) ≠ 1 := by
  intro h
  have hsq := sq_mem_of_involution hg (tP_mem_normalizer k) h
  apply tP_two_not_mem
  rcases hk with rfl | rfl
  · have : tP 1 * tP 1 = tP 2 := by simp [tP, pow_two]
    rwa [this] at hsq
  · have h6 : tP 3 * tP 3 = tP 2 := by
      have : dP ^ 3 * dP ^ 3 = dP ^ 2 := by
        calc dP ^ 3 * dP ^ 3 = dP ^ 4 * dP ^ 2 := by group
          _ = dP ^ 2 := by rw [dP_pow_four, one_mul]
      simpa [tP] using this
    rwa [h6] at hsq

theorem card_inf_centralizer_conj {c : Equiv.Perm (Fin 820)} (hc : c ∈ P)
    (r : Equiv.Perm (Fin 820)) :
    Nat.card ↥(P ⊓ centralizer ({c * r * c⁻¹} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(P ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 820)))) := by
  rw [inf_centralizer_conj P hc r]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem coset_index_of_mem {j : ℕ} (hj : j < 9) (h : repCoset[j]! = 0) : j = 2 := by
  interval_cases j <;> simp_all [repCoset]

theorem tP_mem_P_iff {k : ℕ} (hk : k < 8) : tP k ∈ P ↔ k = 0 := by
  constructor
  · intro h
    by_contra hne
    have := tP_mul_inv_not_mem hk (by norm_num : 0 < 8) hne
    rw [tP_zero, inv_one, mul_one] at this
    exact this h
  · rintro rfl
    rw [tP_zero]
    exact P.one_mem

theorem repCoset_eq_zero_of_mem
    {β : Equiv.Perm (Fin 820)} (hβP : β ∈ P) {j : ℕ} (hj : j < 9)
    {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) (hβg : β = g * tP repCoset[j]!) :
    repCoset[j]! = 0 := by
  have hk := repCoset_lt hj
  have : tP repCoset[j]! ∈ P := by
    have h1 : tP repCoset[j]! = g⁻¹ * β := by rw [hβg]; group
    rw [h1]
    exact P.mul_mem (P.inv_mem hg) hβP
  exact (tP_mem_P_iff hk).1 this

theorem rep_unique : ∀ j, j < 9 → ∀ j', j' < 9 → repCoset[j']! = repCoset[j]! →
    repCent[j]! = 720 → repCent[j']! = 720 → j' = j := by decide

end Cover

end CFSG.EvenSporadicStandard.M24Std.CU43
