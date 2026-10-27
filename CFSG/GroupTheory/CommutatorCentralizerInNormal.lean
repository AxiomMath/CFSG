module

public import CFSG.GroupTheory.CommutatorCentralizerIn
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutatorCentralizerIn_le (M C T : Subgroup G)
    (hMC : M ≤ normalizer (C : Set G)) : commutatorCentralizerIn M C T hMC ≤ M :=
  fun _ hx => ((mem_commutatorCentralizerIn hMC).1 hx).1

theorem le_normalizer_commutatorCentralizerIn {M C T : Subgroup G}
    (hMC : M ≤ normalizer (C : Set G)) (hTC : T ≤ normalizer (C : Set G))
    (hMTC : M ≤ normalizer ((T ⊔ C : Subgroup G) : Set G)) :
    M ≤ normalizer (commutatorCentralizerIn M C T hMC : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ commutatorCentralizerIn M C T hMC,
      m * x * m⁻¹ ∈ commutatorCentralizerIn M C T hMC := by
    intro m hm x hx
    obtain ⟨hxM, hx⟩ := (mem_commutatorCentralizerIn hMC).1 hx
    refine (mem_commutatorCentralizerIn hMC).2
      ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun t ht => ?_⟩
    have h1 : m⁻¹ * t * m⁻¹⁻¹ ∈ ((T ⊔ C : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.1 (hMTC (M.inv_mem hm)) t).1 (Subgroup.mem_sup_left ht)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T C hTC] at h1
    obtain ⟨t', ht', c, hc, htc⟩ := h1
    have hxc : ⁅x, c⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem ((Subgroup.mem_normalizer_iff.1 (hMC hxM) c).1 hc) (C.inv_mem hc)
    have hk : ⁅x, t' * c⁆ ∈ C := by
      have e : ⁅x, t' * c⁆ = ⁅x, t'⁆ * (t' * ⁅x, c⁆ * t'⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact C.mul_mem (hx t' ht') ((Subgroup.mem_normalizer_iff.1 (hTC ht') _).1 hxc)
    have ht_eq : t = m * (t' * c) * m⁻¹ := by
      have h2 : t' * c = m⁻¹ * t * m⁻¹⁻¹ := htc
      rw [h2]; group
    have e2 : ⁅m * x * m⁻¹, t⁆ = m * ⁅x, t' * c⁆ * m⁻¹ := by
      rw [ht_eq]; simp only [commutatorElement_def]; group
    rw [e2]
    exact (Subgroup.mem_normalizer_iff.1 (hMC hm) _).1 hk
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key m hm x hx, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_commutatorCentralizerIn_of_le {M C T : Subgroup G}
    (hMC : M ≤ normalizer (C : Set G)) (hCM : C ≤ M) (hTC : T ≤ normalizer (C : Set G)) :
    T ≤ normalizer (commutatorCentralizerIn M C T hMC : Set G) := by
  have key : ∀ s ∈ T, ∀ x ∈ commutatorCentralizerIn M C T hMC,
      s * x * s⁻¹ ∈ commutatorCentralizerIn M C T hMC := by
    intro s hs x hx
    obtain ⟨hxM, hx⟩ := (mem_commutatorCentralizerIn hMC).1 hx
    refine (mem_commutatorCentralizerIn hMC).2 ⟨?_, fun t ht => ?_⟩
    · have e : s * x * s⁻¹ = ⁅x, s⁆⁻¹ * x := by simp only [commutatorElement_def]; group
      rw [e]
      exact M.mul_mem (M.inv_mem (hCM (hx s hs))) hxM
    · have e : ⁅s * x * s⁻¹, t⁆ = s * ⁅x, s⁻¹ * t * s⁆ * s⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hTC hs) _).1
        (hx _ (T.mul_mem (T.mul_mem (T.inv_mem hs) ht) hs))
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key s hs x hx, fun hx => ?_⟩
  have := key s⁻¹ (T.inv_mem hs) _ hx
  simpa [mul_assoc] using this

theorem mul_inv_mem_commutatorCentralizerIn {M C T : Subgroup G}
    (hMC : M ≤ normalizer (C : Set G)) {v w : G} (hv : v ∈ M) (hw : w ∈ M)
    (hv2 : v ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (h : ∀ t ∈ T, (v * t * v⁻¹) * (w * t * w⁻¹)⁻¹ ∈ C) :
    v * w⁻¹ ∈ commutatorCentralizerIn M C T hMC := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hv2])
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hw2])
  have hk : w⁻¹ * v ∈ commutatorCentralizerIn M C T hMC := by
    refine (mem_commutatorCentralizerIn hMC).2 ⟨M.mul_mem (M.inv_mem hw) hv, fun t ht => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hMC (M.inv_mem hw)) _).1 (h t ht)
    rw [commutatorElement_def]
    convert h1 using 1
    group
  have := (commutatorCentralizerIn M C T hMC).inv_mem hk
  rwa [mul_inv_rev, inv_inv, hvi, ← hwi] at this

theorem sup_inf_eq_inf_sup_of_permutes {E T L : Subgroup G} (hEL : E ≤ L)
    (hcoe : ((E ⊔ T : Subgroup G) : Set G) = (E : Set G) * (T : Set G)) :
    E ⊔ (T ⊓ L) = (E ⊔ T) ⊓ L := by
  refine le_antisymm (sup_le (le_inf le_sup_left hEL) (inf_le_inf_right L le_sup_right)) ?_
  rintro x ⟨hxET, hxL⟩
  have hx : x ∈ ((E ⊔ T : Subgroup G) : Set G) := hxET
  rw [hcoe] at hx
  obtain ⟨e, he, t, ht, rfl⟩ := hx
  have htL : t ∈ L := by
    have := L.mul_mem (L.inv_mem (hEL he)) hxL
    simpa using this
  exact Subgroup.mul_mem_sup he ⟨ht, htL⟩

theorem le_normalizer_sup_inf_of_permutes {E T L : Subgroup G} (hEL : E ≤ L)
    (hTL : T ≤ normalizer (L : Set G))
    (hcoe : ((E ⊔ T : Subgroup G) : Set G) = (E : Set G) * (T : Set G)) :
    T ≤ normalizer ((E ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
  rw [sup_inf_eq_inf_sup_of_permutes hEL hcoe]
  intro t ht
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right ht), hTL ht⟩

end CFSG.GroupTheory
