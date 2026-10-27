module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCA7Base

public section

namespace CFSG.ComponentClassification.FooteLit.FCC

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)
open CFSG.ComponentClassification.FooteLit.Aut5A7

@[expose] def v1p : Perm (Fin 7) := swap 0 2 * swap 1 3
@[expose] def v2p : Perm (Fin 7) := swap 0 2 * swap 4 5
@[expose] def c3p : Perm (Fin 7) := swap 0 1 * swap 1 4 * (swap 2 3 * swap 3 5)
@[expose] def t3p : Perm (Fin 7) := swap 0 2 * swap 1 3 * swap 4 5

@[expose] def a4Set : Finset (Perm (Fin 7)) :=
  {1, v1p, v2p, v1p * v2p, c3p, v1p * c3p, v2p * c3p, v1p * v2p * c3p, c3p * c3p,
    v1p * (c3p * c3p), v2p * (c3p * c3p), v1p * v2p * (c3p * c3p)}

theorem a4Set_mul : ∀ x ∈ a4Set, ∀ y ∈ a4Set, x * y ∈ a4Set := by
  simp only [a4Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) y
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem a4Set_inv : ∀ x ∈ a4Set, x⁻¹ ∈ a4Set := by
  simp only [a4Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem a4Set_sign : ∀ x ∈ a4Set, Perm.sign x = 1 := by
  simp only [a4Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem a4Set_commute : ∀ x ∈ a4Set, x * t3p = t3p * x := by
  simp only [a4Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem a4Set_comm_mem : ∀ x ∈ a4Set, x ≠ 1 → x ∈ ({v1p, v2p, v1p * v2p} : Finset _) ∨
    (x * v1p * x⁻¹ * v1p⁻¹ ∈ ({v1p, v2p, v1p * v2p} : Finset _)) := by
  simp only [a4Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem v_conj : ∀ u ∈ ({v1p, v2p, v1p * v2p} : Finset (Perm (Fin 7))),
    (v1p = u ∨ v1p = c3p * u * c3p⁻¹ ∨ v1p = c3p⁻¹ * u * c3p) ∧
      (v2p = u ∨ v2p = c3p * u * c3p⁻¹ ∨ v2p = c3p⁻¹ * u * c3p) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro u (rfl | rfl | rfl) <;> decide

@[expose] def a4 : Subgroup A7 where
  carrier := {g | (g : Perm (Fin 7)) ∈ a4Set}
  mul_mem' ha hb := a4Set_mul _ ha _ hb
  one_mem' := by decide
  inv_mem' hx := a4Set_inv _ hx

theorem mem_a4 (g : A7) : g ∈ a4 ↔ (g : Perm (Fin 7)) ∈ a4Set := Iff.rfl

theorem twelve_le_card_a4 : 12 ≤ Nat.card a4 := by
  let f : a4Set → a4 := fun x =>
    ⟨⟨x, Perm.mem_alternatingGroup.mpr (a4Set_sign x x.2)⟩, x.2⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (congrArg (fun g : a4 => ((g : A7) : Perm (Fin 7))) h)
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, show a4Set.card = 12 by decide] at h

@[expose] def v1a : A7 := ⟨v1p, by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def v2a : A7 := ⟨v2p, by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def c3a : A7 := ⟨c3p, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem v1a_mem : v1a ∈ a4 := (mem_a4 _).mpr (by decide)
theorem v2a_mem : v2a ∈ a4 := (mem_a4 _).mpr (by decide)
theorem c3a_mem : c3a ∈ a4 := (mem_a4 _).mpr (by decide)

theorem perm_ext_fin7 {π σ : Perm (Fin 7)} (h0 : π 0 = σ 0) (h1 : π 1 = σ 1) (h2 : π 2 = σ 2)
    (h3 : π 3 = σ 3) (h4 : π 4 = σ 4) (h5 : π 5 = σ 5) (h6 : π 6 = σ 6) : π = σ := by
  refine Equiv.ext fun x => ?_
  fin_cases x
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem eq_of_commute_a4 {π : Perm (Fin 7)} (h1 : π * v1p = v1p * π) (h2 : π * v2p = v2p * π)
    (h3 : π * c3p = c3p * π) : π = 1 ∨ π = t3p := by
  have key : ∀ x y : Fin 7, (v1p y = y ↔ v1p x = x) → (v2p y = y ↔ v2p x = x) →
      y = x ∨ y = t3p x := by decide
  have hπx : ∀ x, π x = x ∨ π x = t3p x := fun x =>
    key x (π x) (fixed_iff_of_commute h1 x) (fixed_iff_of_commute h2 x)
  have hc : ∀ x, π (c3p x) = c3p (π x) := fun x => by
    rw [← Perm.mul_apply, h3, Perm.mul_apply]
  have hinj : ∀ x y, π x = π y → x = y := fun x y h => π.injective h
  rcases hπx 0 with h0 | h0
  · left
    have e1 : π 1 = 1 := by
      have := hc 0
      rwa [h0, show c3p 0 = 1 by decide] at this
    have e4 : π 4 = 4 := by
      have := hc 1
      rwa [e1, show c3p 1 = 4 by decide] at this
    have e2 : π 2 = 2 := by
      rcases hπx 2 with h | h
      · exact h
      · have h' : π 2 = π 0 := by rw [h, h0]; decide
        exact absurd (hinj _ _ h') (by decide)
    have e3 : π 3 = 3 := by
      have := hc 2
      rwa [e2, show c3p 2 = 3 by decide] at this
    have e5 : π 5 = 5 := by
      have := hc 3
      rwa [e3, show c3p 3 = 5 by decide] at this
    have e6 : π 6 = 6 := by
      rcases hπx 6 with h | h
      · exact h
      · rwa [show t3p 6 = 6 by decide] at h
    exact perm_ext_fin7 h0 e1 e2 e3 e4 e5 e6
  · right
    have e1 : π 1 = t3p 1 := by
      have := hc 0
      rwa [h0, show c3p (t3p 0) = t3p 1 by decide, show c3p 0 = 1 by decide] at this
    have e4 : π 4 = t3p 4 := by
      have := hc 1
      rwa [e1, show c3p (t3p 1) = t3p 4 by decide, show c3p 1 = 4 by decide] at this
    have e2 : π 2 = t3p 2 := by
      rcases hπx 2 with h | h
      · have h' : π 2 = π 0 := by rw [h, h0]; decide
        exact absurd (hinj _ _ h') (by decide)
      · exact h
    have e3 : π 3 = t3p 3 := by
      have := hc 2
      rwa [e2, show c3p (t3p 2) = t3p 3 by decide, show c3p 2 = 3 by decide] at this
    have e5 : π 5 = t3p 5 := by
      have := hc 3
      rwa [e3, show c3p (t3p 3) = t3p 5 by decide, show c3p 3 = 5 by decide] at this
    have e6 : π 6 = t3p 6 := by
      rcases hπx 6 with h | h
      · rwa [show t3p 6 = 6 by decide]
      · exact h
    exact perm_ext_fin7 h0 e1 e2 e3 e4 e5 e6

theorem fcc_triple : FCConcl A7 (autPerm.symm (swap 0 2 * swap 1 3 * swap 4 5)) a4 := by
  refine ⟨fun g hg => ?_, ?_, fun N hNM hNn hN1 => ?_, fun α hα => ?_⟩
  ·
    show g ∈ MonoidHom.eqLocus (autPerm.symm t3p).toMonoidHom (MonoidHom.id A7)
    rw [mem_eqLocus_iff]
    exact a4Set_commute _ hg
  ·
    have h1 := two_mul_card_eqLocus_le (τ := swap (0 : Fin 7) 2 * swap 1 3 * swap 4 5)
      (by decide)
    rw [Perm.nat_card_centralizer, cycleType_triple] at h1
    have h2 := le_trans h1 (by decide : _ ≤ 48)
    have h3 := twelve_le_card_a4
    omega
  ·
    obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
      rcases N.bot_or_exists_ne_one with h | h
      · exact absurd h hN1
      · exact h
    have hxV : ∃ u ∈ N, (u : Perm (Fin 7)) ∈ ({v1p, v2p, v1p * v2p} : Finset _) := by
      rcases a4Set_comm_mem _ (hNM hxN) (fun h => hx1 (Subtype.ext h)) with h | h
      · exact ⟨x, hxN, h⟩
      · refine ⟨x * v1a * x⁻¹ * v1a⁻¹, ?_, h⟩
        rw [mul_assoc, mul_assoc]
        refine mul_mem hxN ?_
        rw [← mul_assoc]
        exact hNn v1a v1a_mem _ (inv_mem hxN)
    obtain ⟨u, huN, huV⟩ := hxV
    have hc1 : c3a * u * c3a⁻¹ ∈ N := hNn c3a c3a_mem u huN
    have hc2 : c3a⁻¹ * u * c3a ∈ N := by
      have := hNn c3a⁻¹ (inv_mem c3a_mem) u huN
      rwa [inv_inv] at this
    have hmem : ∀ t : A7, ((t : Perm (Fin 7)) = u ∨ (t : Perm (Fin 7)) = c3p * u * c3p⁻¹ ∨
        (t : Perm (Fin 7)) = c3p⁻¹ * u * c3p) → t ∈ N := by
      rintro t (h | h | h)
      · rwa [Subtype.ext h]
      · rwa [show t = c3a * u * c3a⁻¹ from Subtype.ext h]
      · rwa [show t = c3a⁻¹ * u * c3a from Subtype.ext h]
    obtain ⟨hv1, hv2⟩ := v_conj _ huV
    exact ⟨v1a, hmem v1a hv1, v2a, hmem v2a hv2, by decide, by decide, by decide, by decide,
      by decide, by decide⟩
  ·
    rcases eq_of_commute_a4 (commute_of_fix (hα v1a v1a_mem))
      (commute_of_fix (hα v2a v2a_mem)) (commute_of_fix (hα c3a c3a_mem)) with h | h
    · left
      apply autPerm.injective
      rw [h, map_one]
    · right
      apply autPerm.injective
      rw [h, MulEquiv.apply_symm_apply]
      rfl

end CFSG.ComponentClassification.FooteLit.FCC
