module

public import CFSG.GH74.Uniqueness.SU.KI1r4LyFour

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.LyPerm

open Equiv Equiv.Perm Subgroup CFSG.GH74.Generic.S45.LAlt
open scoped commutatorElement

variable {n : ℕ}

theorem BadCent.conj {σ : Perm (Fin n)} (h : BadCent σ) (c : Perm (Fin n)) : BadCent (c * σ * c⁻¹) := by
  obtain ⟨⟨g, hg, hg4⟩, X, hXle, hXperf, g', hg'X, hg'⟩ := h
  have hmemC : ∀ a ∈ centAlt σ, c * a * c⁻¹ ∈ centAlt (c * σ * c⁻¹) := fun a ha => by
    obtain ⟨hA, hcomm⟩ := mem_centAlt.1 ha
    refine mem_centAlt.2 ⟨?_, ?_⟩
    · rw [Perm.mem_alternatingGroup] at hA ⊢
      rw [map_mul, map_mul, map_inv, hA]
      simp
    · calc c * a * c⁻¹ * (c * σ * c⁻¹) = c * (a * σ) * c⁻¹ := by group
        _ = c * (σ * a) * c⁻¹ := by rw [hcomm]
        _ = c * σ * c⁻¹ * (c * a * c⁻¹) := by group
  have hord : ∀ a : Perm (Fin n), orderOf (c * a * c⁻¹) = orderOf a := fun a => by
    have := (MulAut.conj c).orderOf_eq a
    simpa [MulAut.conj_apply] using this
  refine ⟨⟨c * g * c⁻¹, hmemC g hg, by rw [hord, hg4]⟩, X.map (MulAut.conj c).toMonoidHom, ?_, ?_,
    c * g' * c⁻¹, ⟨g', hg'X, rfl⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hmemC a (hXle ha)
  · rw [← Subgroup.map_commutator, hXperf]
  · rcases hg' with h4 | ⟨a, b, c', d, hab, hac, had, hbc, hbd, hcd, hgeq⟩
    · exact Or.inl (by rw [hord, h4])
    · refine Or.inr ⟨c a, c b, c c', c d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h => hab (c.injective h)
      · exact fun h => hac (c.injective h)
      · exact fun h => had (c.injective h)
      · exact fun h => hbc (c.injective h)
      · exact fun h => hbd (c.injective h)
      · exact fun h => hcd (c.injective h)
      · rw [hgeq, mul_assoc, swap_apply_apply c a b, swap_apply_apply c c' d]
        group

@[expose] def sigma5 : Perm (Fin 11) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9

@[expose] def diagA : Perm (Fin 11) := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)

@[expose] def diagB : Perm (Fin 11) :=
  (swap 0 2 * swap 2 4 * swap 4 6 * swap 6 8) * (swap 1 3 * swap 3 5 * swap 5 7 * swap 7 9)

@[expose] def diagD : Perm (Fin 11) := swap 0 1 * swap 2 3

@[expose] def diagX : Subgroup (Perm (Fin 11)) := Subgroup.closure {diagA, diagB, diagD}

@[expose] def order4El : Perm (Fin 11) := (swap 0 2 * swap 2 1 * swap 1 3) * (swap 4 6 * swap 6 5 * swap 5 7)

theorem diagA_mem : diagA ∈ diagX := Subgroup.subset_closure (by simp)

theorem diagB_mem : diagB ∈ diagX := Subgroup.subset_closure (by simp)

theorem diagD_mem : diagD ∈ diagX := Subgroup.subset_closure (by simp)

private theorem mem_centAlt_of {g : Perm (Fin 11)} (h1 : Perm.sign g = 1) (h2 : g * sigma5 = sigma5 * g) :
    g ∈ centAlt sigma5 := mem_centAlt.2 ⟨Perm.mem_alternatingGroup.2 h1, h2⟩

theorem diagX_le : diagX ≤ centAlt sigma5 := by
  rw [diagX, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact mem_centAlt_of (by decide +kernel) (by decide +kernel)
  · exact mem_centAlt_of (by decide +kernel) (by decide +kernel)
  · exact mem_centAlt_of (by decide +kernel) (by decide +kernel)

theorem diagX_perfect : ⁅diagX, diagX⁆ = diagX := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  rw [diagX, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have hA := diagA_mem
  have hB := diagB_mem
  have hD := diagD_mem
  rcases hg with rfl | rfl | rfl
  ·
    have h := Subgroup.commutator_mem_commutator (inv_mem hA)
      (show diagB * diagA * diagB⁻¹ * diagA⁻¹ * diagB ∈ diagX from
        mul_mem (mul_mem (mul_mem (mul_mem hB hA) (inv_mem hB)) (inv_mem hA)) hB)
    have e : diagA = ⁅diagA⁻¹, diagB * diagA * diagB⁻¹ * diagA⁻¹ * diagB⁆ := by
      simp only [diagA, diagB]
      decide +kernel
    rwa [← e] at h
  · have h := Subgroup.commutator_mem_commutator hA
      (show diagA * diagB * diagA * diagB ∈ diagX from mul_mem (mul_mem (mul_mem hA hB) hA) hB)
    have e : diagB = ⁅diagA, diagA * diagB * diagA * diagB⁆ := by
      simp only [diagA, diagB]
      decide +kernel
    rwa [← e] at h
  · have h := Subgroup.commutator_mem_commutator hA (show diagA * diagD ∈ diagX from mul_mem hA hD)
    have e : diagD = ⁅diagA, diagA * diagD⁆ := by
      simp only [diagA, diagD]
      decide +kernel
    rwa [← e] at h

theorem badCent_sigma5 : BadCent sigma5 := by
  refine ⟨⟨order4El, mem_centAlt_of (by decide +kernel) (by decide +kernel), ?_⟩, diagX, diagX_le,
    diagX_perfect, diagD, diagD_mem, Or.inr ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ¬ order4El ^ 2 ^ 1 = 1 := by decide +kernel
    have h2 : order4El ^ 2 ^ (1 + 1) = 1 := by decide +kernel
    simpa using orderOf_eq_prime_pow h1 h2
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

theorem fixAlt_perfect' {S : Finset (Fin 11)} (hS : S.card ≤ 6) :
    ⁅fixAlt S, fixAlt S⁆ = fixAlt S := by
  have h5 : 5 ≤ Nat.card {x : Fin 11 // x ∉ S} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    omega
  rw [fixAlt, ← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h5]

theorem fixAlt_support_commute {σ f : Perm (Fin 11)} (hf : f ∈ fixAlt σ.support) :
    f * σ = σ * f := by
  have hfix : ∀ x, σ x ≠ x → f x = x := fun x hx => fixAlt_fixes hf (Perm.mem_support.2 hx)
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : σ x = x
  · have hfx : σ (f x) = f x := by
      by_contra hne
      have h2 : f x = x := f.injective (hfix (f x) hne)
      rw [h2] at hne
      exact hne hx
    rw [hx, hfx]
  · have hsx : σ (σ x) ≠ σ x := fun h => hx (σ.injective h)
    rw [hfix x hx, hfix (σ x) hsx]

theorem badCent_of_few_moved {σ : Perm (Fin 11)} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hs : σ.support.card ≤ 6) : BadCent σ := by
  have hcard : 4 ≤ Fintype.card {x : Fin 11 // x ∉ σ.support} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    omega
  obtain ⟨e⟩ : Nonempty (Fin 4 ↪ {x : Fin 11 // x ∉ σ.support}) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  have hne : ∀ i j : Fin 4, i ≠ j → (e i : Fin 11) ≠ e j := fun i j h h' =>
    h (e.injective (Subtype.ext h'))
  have h01 : (e 0 : Fin 11) ≠ e 1 := hne _ _ (by decide)
  have h23 : (e 2 : Fin 11) ≠ e 3 := hne _ _ (by decide)
  have hmem : swap (e 0 : Fin 11) (e 1) * swap (e 2 : Fin 11) (e 3) ∈ fixAlt σ.support :=
    swap_mul_swap_mem_fixAlt h01 h23 (e 0).2 (e 1).2 (e 2).2 (e 3).2
  have hv1 : swap (e 0 : Fin 11) (e 1) * swap (e 2 : Fin 11) (e 3) ≠ 1 := by
    intro h
    have h' := congrArg (fun f : Perm (Fin 11) => f (e 0 : Fin 11)) h
    simp only [Perm.mul_apply, Perm.one_apply] at h'
    rw [swap_apply_of_ne_of_ne (hne 0 2 (by decide)) (hne 0 3 (by decide)), swap_apply_left] at h'
    exact h01 h'.symm
  have hLb : fixAlt σ.support ≤ centAlt σ := fun f hf =>
    mem_centAlt.2 ⟨fixAlt_le_alt _ hf, fixAlt_support_commute hf⟩
  exact badCent_of_fixes hσ hσ1 hLb (fixAlt_perfect' hs) hmem hv1
    (fun l hl x hx => fixAlt_fixes hl (Perm.mem_support.2 hx))

theorem badCent_of_odd {σ : Perm (Fin 11)} (hσ : σ * σ = 1) (hodd : σ ∉ alternatingGroup (Fin 11)) :
    BadCent σ := by
  obtain ⟨k, hk5, hct⟩ := invol_cycleType σ hσ
  have hsum : σ.support.card = 2 * k := by
    rw [← sum_cycleType, hct, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hσ1 : σ ≠ 1 := fun h => hodd (h ▸ one_mem _)
  have hk_odd : Odd k := by
    by_contra hk
    apply hodd
    rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, hct, Multiset.sum_replicate,
      Multiset.card_replicate, smul_eq_mul]
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hk
    rw [hm, show (m + m) * 2 + (m + m) = 2 * (m + m + m) by ring, pow_mul]
    simp
  have hk : k = 1 ∨ k = 3 ∨ k = 5 := by
    obtain ⟨m, hm⟩ := hk_odd
    omega
  rcases hk with rfl | rfl | rfl
  · exact badCent_of_few_moved hσ hσ1 (by omega)
  · exact badCent_of_few_moved hσ hσ1 (by omega)
  · have hconj : IsConj sigma5 σ :=
      isConj_iff_cycleType_eq.2 (by rw [hct]; exact cycleType_std (le_refl 5))
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [← hc]
    exact BadCent.conj badCent_sigma5 c

end CFSG.GH74.Uniqueness.SU.K.R4.LyPerm
