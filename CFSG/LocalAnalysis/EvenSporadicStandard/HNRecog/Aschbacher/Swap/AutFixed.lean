module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Equiv Equiv.Perm

private def t₀ : A5 := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide)⟩

private theorem t₀_sq : t₀ ^ 2 = 1 := by decide +kernel

private theorem t₀_a₀_cube : (t₀ * a₀) ^ 3 = 1 := by decide +kernel

private theorem orderOf_t₀_a₀ : orderOf (t₀ * a₀) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨t₀_a₀_cube, by decide +kernel⟩

private theorem conj_pow_apply (i : ℕ) (x : A5) :
    (MulAut.conj (a₀ ^ i)).toMonoidHom x = a₀ ^ i * x * (a₀ ^ i)⁻¹ :=
  MulAut.conj_apply (a₀ ^ i) x

private theorem conj_pow_fixes_a₀ (i : ℕ) :
    (MulAut.conj (a₀ ^ i)).toMonoidHom a₀ = a₀ := by
  rw [conj_pow_apply]
  have hcomm : a₀ ^ i * a₀ = a₀ * a₀ ^ i := by rw [← pow_succ, pow_succ']
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem fifteen_le_card_closure :
    15 ≤ Nat.card (Subgroup.closure ({a₀, t₀} : Set A5)) := by
  set K := Subgroup.closure ({a₀, t₀} : Set A5)
  have ha : a₀ ∈ K := Subgroup.subset_closure (by simp)
  have ht : t₀ ∈ K := Subgroup.subset_closure (by simp)
  have hta : t₀ * a₀ ∈ K := K.mul_mem ht ha
  have h5 : 5 ∣ Nat.card K := by
    have h := K.orderOf_dvd_natCard ha
    rwa [orderOf_a₀] at h
  have h3 : 3 ∣ Nat.card K := by
    have h := K.orderOf_dvd_natCard hta
    rwa [orderOf_t₀_a₀] at h
  have h15 : 15 ∣ Nat.card K := by
    have hcop : (5 : ℕ).Coprime 3 := by decide
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h5 h3
    simpa using h
  haveI : Nonempty K := ⟨1⟩
  exact Nat.le_of_dvd Nat.card_pos h15

private theorem closure_a₀_t₀_eq_top : Subgroup.closure ({a₀, t₀} : Set A5) = ⊤ :=
  eq_top_of_fifteen_le_card fifteen_le_card_closure

theorem exists_pow_conj_of_apply_eq (φ : A5 →* A5) (h : φ a₀ = a₀) :
    ∃ i : ℕ, ∀ x : A5, φ x = a₀ ^ i * x * (a₀ ^ i)⁻¹ := by
  have key : ∀ u : A5, u ^ 2 = 1 → (u * a₀) ^ 3 = 1 →
      u = t₀ ∨ u = a₀ * t₀ * a₀⁻¹ ∨ u = a₀ ^ 2 * t₀ * (a₀ ^ 2)⁻¹ ∨
        u = a₀ ^ 3 * t₀ * (a₀ ^ 3)⁻¹ ∨ u = a₀ ^ 4 * t₀ * (a₀ ^ 4)⁻¹ := by
    decide +kernel
  have hφt2 : (φ t₀) ^ 2 = 1 := by rw [← map_pow, t₀_sq, map_one]
  have hφta3 : (φ t₀ * a₀) ^ 3 = 1 := by
    rw [← h, ← map_mul, ← map_pow, t₀_a₀_cube, map_one]
  have hgen : Subgroup.closure ({a₀, t₀} : Set A5) = ⊤ := closure_a₀_t₀_eq_top
  have finish : ∀ (j : ℕ), φ t₀ = a₀ ^ j * t₀ * (a₀ ^ j)⁻¹ →
      ∀ x : A5, φ x = a₀ ^ j * x * (a₀ ^ j)⁻¹ := by
    intro j hj x
    have hψa : (MulAut.conj (a₀ ^ j)).toMonoidHom a₀ = a₀ := conj_pow_fixes_a₀ j
    have hψt : (MulAut.conj (a₀ ^ j)).toMonoidHom t₀ = φ t₀ := by
      rw [conj_pow_apply, hj]
    have hφψ : φ = (MulAut.conj (a₀ ^ j)).toMonoidHom :=
      MonoidHom.eq_of_eqOn_dense (s := ({a₀, t₀} : Set A5)) hgen (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · rw [h, hψa]
        · rw [hψt])
    rw [hφψ]
    exact conj_pow_apply j x
  rcases key (φ t₀) hφt2 hφta3 with h0 | h1 | h2 | h3 | h4
  · exact ⟨0, finish 0 (by simpa using h0)⟩
  · exact ⟨1, finish 1 (by simpa using h1)⟩
  · exact ⟨2, finish 2 h2⟩
  · exact ⟨3, finish 3 h3⟩
  · exact ⟨4, finish 4 h4⟩

end CFSG.EvenSporadicStandard.HNRecog.Fpf
