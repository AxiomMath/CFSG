module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondBasic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSporadicStandard.Wong77.Module

namespace GoodFrame

variable {X : Type*} [Group X] (F : GoodFrame X)

theorem exists_index_notMem (i j k : Fin 23) : ∃ m : Fin 23, m ≠ i ∧ m ≠ j ∧ m ≠ k := by
  have hcard : ({i, j, k} : Finset (Fin 23)).card < (Finset.univ : Finset (Fin 23)).card := by
    calc ({i, j, k} : Finset (Fin 23)).card ≤ 3 := Finset.card_le_three
      _ < 23 := by norm_num
      _ = (Finset.univ : Finset (Fin 23)).card := by simp
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2.1, hm.2.2⟩

theorem not_transitive : ∀ a ∈ Set.range F.pt, ∀ b ∈ Set.range F.pt, ∀ c ∈ Set.range F.pt,
    ¬ ∀ e ∈ Set.range F.pt, ∀ f ∈ Set.range F.pt,
      ∃ g ∈ Subgroup.normalizer (Set.range F.pt) ⊓ Subgroup.centralizer {a * b * c},
        g * e * g⁻¹ = f := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ htr
  have hfix : ∀ m : Fin 23, F.pt i * F.pt j * F.pt k = F.pt m → False := by
    intro m hm
    obtain ⟨m', hm'⟩ := exists_ne m
    obtain ⟨g, ⟨-, hgC⟩, hg⟩ := htr (F.pt m) ⟨m, rfl⟩ (F.pt m') ⟨m', rfl⟩
    have hgC' := Subgroup.mem_centralizer_singleton_iff.1 hgC
    rw [hm] at hgC'
    have h1 : g * F.pt m * g⁻¹ = F.pt m := by rw [hgC', mul_inv_cancel_right]
    exact hm' (F.pt_injective (hg.symm.trans h1))
  by_cases hij : i = j
  · subst hij
    exact hfix k (by rw [F.pt_mul_self, one_mul])
  by_cases hik : i = k
  · subst hik
    refine hfix j ?_
    rw [F.pt_comm i j, mul_assoc, F.pt_mul_self, mul_one]
  obtain ⟨m, hmi, hmj, hmk⟩ := exists_index_notMem i j k
  obtain ⟨g, ⟨hgN, hgC⟩, hg⟩ := htr (F.pt i) ⟨i, rfl⟩ (F.pt m) ⟨m, rfl⟩
  have hgN' : ∀ x ∈ Set.range F.pt, g * x * g⁻¹ ∈ Set.range F.pt := fun x hx =>
    (Subgroup.mem_set_normalizer_iff.1 hgN x).1 hx
  obtain ⟨p, hp⟩ := hgN' (F.pt j) ⟨j, rfl⟩
  obtain ⟨q, hq⟩ := hgN' (F.pt k) ⟨k, rfl⟩
  have hgC' := Subgroup.mem_centralizer_singleton_iff.1 hgC
  have hprod : F.pt m * F.pt p * F.pt q = F.pt i * F.pt j * F.pt k := by
    calc F.pt m * F.pt p * F.pt q
        = (g * F.pt i * g⁻¹) * (g * F.pt j * g⁻¹) * (g * F.pt k * g⁻¹) := by rw [hg, hp, hq]
      _ = g * (F.pt i * F.pt j * F.pt k) * g⁻¹ := by group
      _ = F.pt i * F.pt j * F.pt k := by rw [hgC', mul_inv_cancel_right]
  have hmp : m ≠ p := by
    intro h
    apply hij
    apply F.pt_injective
    have h1 : g * F.pt i * g⁻¹ = g * F.pt j * g⁻¹ := by rw [hg, ← hp, h]
    exact mul_left_cancel (mul_right_cancel h1)
  have hmq : m ≠ q := by
    intro h
    apply hik
    apply F.pt_injective
    have h1 : g * F.pt i * g⁻¹ = g * F.pt k * g⁻¹ := by rw [hg, ← hq, h]
    exact mul_left_cancel (mul_right_cancel h1)
  have hw : (Pi.single m 1 + Pi.single p 1 + Pi.single q 1 : Word) =
      Pi.single i 1 + Pi.single j 1 + Pi.single k 1 := by
    refine F.eq_of_wprod_eq ?_ ?_
    · simp only [wprod_add, wprod_single]
      exact hprod
    · have h1 := hammingNorm_add_single_le (Pi.single m 1 + Pi.single p 1) q
      have h2 := hammingNorm_add_single_le (Pi.single m 1) p
      have h3 := hammingNorm_add_single_le (Pi.single i 1 + Pi.single j 1) k
      have h4 := hammingNorm_add_single_le (Pi.single i 1) j
      rw [hammingNorm_single] at h2 h4
      omega
  have := congrFun hw m
  simp [hmp, hmq, hmi, hmj, hmk] at this

end GoodFrame

end CFSG.EvenSporadicStandard.TwoFi22
