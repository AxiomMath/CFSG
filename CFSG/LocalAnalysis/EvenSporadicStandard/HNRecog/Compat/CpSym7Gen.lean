module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv
open scoped Finset

theorem cp_sym7_cent_gen {τ σ : Perm (Fin 7)} (hτ : τ.cycleType = {2})
    (hσ : σ.cycleType = {2, 2}) (hcomm : τ * σ = σ * τ) (hτσ : (τ * σ).cycleType = {2, 2, 2}) :
    Subgroup.closure ((Subgroup.centralizer {τ} : Set (Perm (Fin 7))) ∪
      (Subgroup.centralizer {σ} : Set (Perm (Fin 7)))) = ⊤ := by
  classical
  have hτcard : τ.support.card = 2 := by
    rw [← Equiv.Perm.sum_cycleType τ, hτ]
    decide
  have hσcard : σ.support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType σ, hσ]
    decide
  have hτσcard : (τ * σ).support.card = 6 := by
    rw [← Equiv.Perm.sum_cycleType (τ * σ), hτσ]
    decide
  have hinter : #(τ.support ∩ σ.support) = 0 := by
    have h := Finset.card_union_add_card_inter τ.support σ.support
    rw [hτcard, hσcard] at h
    have hle : 6 ≤ #(τ.support ∪ σ.support) := by
      rw [← hτσcard]
      exact Finset.card_le_card
        (by simpa [Finset.sup_eq_union] using Equiv.Perm.support_mul_le τ σ)
    omega
  have hdisj : Disjoint τ.support σ.support := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hinter
  set A : Finset (Fin 7) := τ.supportᶜ with hA
  set B : Finset (Fin 7) := σ.supportᶜ with hB
  have hmemA : ∀ x : Fin 7, x ∈ A ↔ τ x = x := by
    intro x
    simp only [hA, Finset.mem_compl, Equiv.Perm.notMem_support]
  have hmemB : ∀ x : Fin 7, x ∈ B ↔ σ x = x := by
    intro x
    simp only [hB, Finset.mem_compl, Equiv.Perm.notMem_support]
  have hAcard : A.card = 5 := by
    rw [hA, Finset.card_compl, hτcard, Fintype.card_fin]
  have hBcard : B.card = 3 := by
    rw [hB, Finset.card_compl, hσcard, Fintype.card_fin]
  have hABuniv : A ∪ B = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [Finset.mem_union]
    by_cases hx : x ∈ τ.support
    · right
      rw [hB, Finset.mem_compl]
      intro hxs
      exact (Finset.disjoint_left.mp hdisj hx) hxs
    · left
      rw [hA, Finset.mem_compl]
      exact hx
  have hAB : ∀ x : Fin 7, x ∈ A ∨ x ∈ B := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hABuniv]; exact Finset.mem_univ x
    exact Finset.mem_union.mp hx
  have hABcard : (A ∩ B).card = 1 := by
    have h := Finset.card_union_add_card_inter A B
    rw [hABuniv, Finset.card_univ, Fintype.card_fin, hAcard, hBcard] at h
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hABcard
  have hpAB : p ∈ A ∩ B := by rw [hp]; exact Finset.mem_singleton_self p
  have hpA : p ∈ A := (Finset.mem_inter.mp hpAB).1
  have hpB : p ∈ B := (Finset.mem_inter.mp hpAB).2
  have swapA : ∀ {x y : Fin 7}, x ∈ A → y ∈ A →
      swap x y ∈ Subgroup.centralizer {τ} := by
    intro x y hx hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdis : Equiv.Perm.Disjoint (swap x y) τ := by
      intro z
      by_cases hz : z = x ∨ z = y
      · right
        have hzA : z ∈ A := by
          rcases hz with rfl | rfl
          · exact hx
          · exact hy
        exact (hmemA z).mp hzA
      · left
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hz (Or.inl h))
          (fun h => hz (Or.inr h))
    exact hdis.commute
  have swapB : ∀ {x y : Fin 7}, x ∈ B → y ∈ B →
      swap x y ∈ Subgroup.centralizer {σ} := by
    intro x y hx hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdis : Equiv.Perm.Disjoint (swap x y) σ := by
      intro z
      by_cases hz : z = x ∨ z = y
      · right
        have hzB : z ∈ B := by
          rcases hz with rfl | rfl
          · exact hx
          · exact hy
        exact (hmemB z).mp hzB
      · left
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hz (Or.inl h))
          (fun h => hz (Or.inr h))
    exact hdis.commute
  have hsub : {s : Perm (Fin 7) | s.IsSwap} ⊆
      Subgroup.closure ((Subgroup.centralizer {τ} : Set (Perm (Fin 7))) ∪
        (Subgroup.centralizer {σ} : Set (Perm (Fin 7)))) := by
    intro s hs
    rw [Set.mem_setOf_eq, Equiv.Perm.IsSwap] at hs
    obtain ⟨u, v, huv, rfl⟩ := hs
    by_cases huA : u ∈ A
    · by_cases hvA : v ∈ A
      · exact Subgroup.subset_closure (Or.inl (swapA huA hvA))
      · have hvB : v ∈ B := by
          rcases hAB v with h | h
          · exact absurd h hvA
          · exact h
        by_cases huB : u ∈ B
        · exact Subgroup.subset_closure (Or.inr (swapB huB hvB))
        · have hvp : v ≠ p := fun h => (h ▸ hvA) hpA
          have hvu : v ≠ u := Ne.symm huv
          have hformula : swap u v = swap p u * swap v p * swap p u :=
            (Equiv.swap_mul_swap_mul_swap (x := v) (y := p) (z := u) hvp hvu).symm
          rw [hformula]
          exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl (swapA hpA huA)))
            (Subgroup.subset_closure (Or.inr (swapB hvB hpB))))
            (Subgroup.subset_closure (Or.inl (swapA hpA huA)))
    · have huB : u ∈ B := by
        rcases hAB u with h | h
        · exact absurd h huA
        · exact h
      by_cases hvB : v ∈ B
      · exact Subgroup.subset_closure (Or.inr (swapB huB hvB))
      · have hvA : v ∈ A := by
          rcases hAB v with h | h
          · exact h
          · exact absurd h hvB
        have hup : u ≠ p := fun h => (h ▸ huA) hpA
        have hformula : swap u v = swap p v * swap u p * swap p v := by
          rw [Equiv.swap_comm u v]
          exact (Equiv.swap_mul_swap_mul_swap (x := u) (y := p) (z := v) hup huv).symm
        rw [hformula]
        exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl (swapA hpA hvA)))
          (Subgroup.subset_closure (Or.inr (swapB huB hpB))))
          (Subgroup.subset_closure (Or.inl (swapA hpA hvA)))
  rw [eq_top_iff]
  calc (⊤ : Subgroup (Perm (Fin 7)))
      = Subgroup.closure {s : Perm (Fin 7) | s.IsSwap} := Equiv.Perm.closure_isSwap.symm
    _ ≤ Subgroup.closure ((Subgroup.centralizer {τ} : Set (Perm (Fin 7))) ∪
          (Subgroup.centralizer {σ} : Set (Perm (Fin 7)))) :=
        (Subgroup.closure_le _).mpr hsub

theorem cp_s7_cent_gen {G : Type} [Group G] {K : Subgroup G} (φ : K ≃* Perm (Fin 7)) {t t' : G}
    (ht : t ∈ K) (ht' : t' ∈ K) (hcomm : t * t' = t' * t)
    (h1 : (φ ⟨t, ht⟩).cycleType = {2}) (h2 : (φ ⟨t', ht'⟩).cycleType = {2, 2})
    (h3 : (φ ⟨t * t', K.mul_mem ht ht'⟩).cycleType = {2, 2, 2}) :
    K ≤ Subgroup.closure ((K ⊓ Subgroup.centralizer {t} : Subgroup G) ∪
      (K ⊓ Subgroup.centralizer {t'} : Subgroup G) : Set G) := by
  classical
  have hmul : φ ⟨t, ht⟩ * φ ⟨t', ht'⟩ = φ ⟨t * t', K.mul_mem ht ht'⟩ := by
    rw [← map_mul]
    exact congrArg φ (Subtype.ext rfl)
  have hcomm_ts : φ ⟨t, ht⟩ * φ ⟨t', ht'⟩ = φ ⟨t', ht'⟩ * φ ⟨t, ht⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hτσ : (φ ⟨t, ht⟩ * φ ⟨t', ht'⟩).cycleType = {2, 2, 2} := by
    rw [hmul]
    exact h3
  have hgen : Subgroup.closure ((Subgroup.centralizer {φ ⟨t, ht⟩} : Set (Perm (Fin 7))) ∪
      (Subgroup.centralizer {φ ⟨t', ht'⟩} : Set (Perm (Fin 7)))) = ⊤ :=
    cp_sym7_cent_gen (τ := φ ⟨t, ht⟩) (σ := φ ⟨t', ht'⟩) h1 h2 hcomm_ts hτσ
  set T : Set (Perm (Fin 7)) :=
    (Subgroup.centralizer {φ ⟨t, ht⟩} : Set (Perm (Fin 7))) ∪
      (Subgroup.centralizer {φ ⟨t', ht'⟩} : Set (Perm (Fin 7))) with hT
  have hgenT : Subgroup.closure T = ⊤ := by rw [hT]; exact hgen
  let f : Perm (Fin 7) →* G := K.subtype.comp φ.symm.toMonoidHom
  have hf_range : f.range = K := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ.symm y).2
    · intro hg
      exact ⟨φ ⟨g, hg⟩, by simp [f]⟩
  have hclosureT : Subgroup.closure (f '' T) = K := by
    rw [← MonoidHom.map_closure f T, hgenT, ← MonoidHom.range_eq_map f, hf_range]
  have hfT : f '' T ⊆ ((K ⊓ Subgroup.centralizer {t} : Subgroup G) ∪
      (K ⊓ Subgroup.centralizer {t'} : Subgroup G) : Set G) := by
    rintro g ⟨y, hy, rfl⟩
    rw [hT] at hy
    rw [Set.mem_union] at hy
    rw [Set.mem_union]
    rcases hy with hy | hy
    · left
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (φ.symm y).2
      · rw [Subgroup.mem_centralizer_singleton_iff]
        show ((φ.symm y : K) : G) * t = t * ((φ.symm y : K) : G)
        have hy' : y * φ ⟨t, ht⟩ = φ ⟨t, ht⟩ * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hy
        have hk : (φ.symm y : K) * ⟨t, ht⟩ = ⟨t, ht⟩ * (φ.symm y : K) := by
          simpa using congrArg (fun z => φ.symm z) hy'
        simpa using congrArg Subtype.val hk
    · right
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (φ.symm y).2
      · rw [Subgroup.mem_centralizer_singleton_iff]
        show ((φ.symm y : K) : G) * t' = t' * ((φ.symm y : K) : G)
        have hy' : y * φ ⟨t', ht'⟩ = φ ⟨t', ht'⟩ * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hy
        have hk : (φ.symm y : K) * ⟨t', ht'⟩ = ⟨t', ht'⟩ * (φ.symm y : K) := by
          simpa using congrArg (fun z => φ.symm z) hy'
        simpa using congrArg Subtype.val hk
  calc K = Subgroup.closure (f '' T) := hclosureT.symm
    _ ≤ Subgroup.closure ((K ⊓ Subgroup.centralizer {t} : Subgroup G) ∪
          (K ⊓ Subgroup.centralizer {t'} : Subgroup G) : Set G) :=
        Subgroup.closure_mono hfT

end CFSG.EvenSporadicStandard.HNRecog.Section4
