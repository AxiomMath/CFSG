module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm

theorem perm_six_eq_one_of_comm_alt {s : Perm (Fin 6)}
    (h : ∀ t ∈ alternatingGroup (Fin 6), t * s = s * t) : s = 1 := by
  have hmem : s ∈ centralizer (alternatingGroup (Fin 6) : Set (Perm (Fin 6))) :=
    mem_centralizer_iff.2 h
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by simp), Subgroup.mem_bot] at hmem
  exact hmem

theorem perm_six_eq_bot_or_alt_le {N : Subgroup (Perm (Fin 6))} (hN : N.Normal) :
    N = ⊥ ∨ alternatingGroup (Fin 6) ≤ N := by
  by_cases hne : N = ⊥
  · exact Or.inl hne
  right
  obtain ⟨⟨n, hnN⟩, hn1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hn1 : n ≠ 1 := fun h => hn1' (Subtype.ext h)
  have hm : ∃ m ∈ N, m ∈ alternatingGroup (Fin 6) ∧ m ≠ 1 := by
    by_cases hnA : n ∈ alternatingGroup (Fin 6)
    · exact ⟨n, hnN, hnA, hn1⟩
    · have hnc : ∃ g : Perm (Fin 6), g * n ≠ n * g := by
        by_contra hall
        have hcomm : ∀ g : Perm (Fin 6), g * n = n * g := fun g => by
          by_contra h
          exact hall ⟨g, h⟩
        exact hn1 (perm_six_eq_one_of_comm_alt fun h _ => hcomm h)
      obtain ⟨g, hg⟩ := hnc
      refine ⟨g * n * g⁻¹ * n⁻¹, mul_mem (hN.conj_mem n hnN g) (inv_mem hnN), ?_, ?_⟩
      · rw [mem_alternatingGroup]
        simp only [sign_mul, sign_inv]
        rcases Int.units_eq_one_or (sign n) with h | h <;>
          rcases Int.units_eq_one_or (sign g) with h' | h' <;> simp [h, h']
      · intro h
        apply hg
        have : g * n * g⁻¹ = n := mul_inv_eq_one.1 h
        calc g * n = g * n * g⁻¹ * g := by group
          _ = n * g := by rw [this]
  obtain ⟨m, hmN, hmA, hm1⟩ := hm
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnorm : (N.subgroupOf (alternatingGroup (Fin 6))).Normal := hN.subgroupOf _
  have := hnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 6))) with h | h
  · exfalso
    have : (⟨m, hmA⟩ : alternatingGroup (Fin 6)) ∈ N.subgroupOf (alternatingGroup (Fin 6)) :=
      hmN
    rw [h, Subgroup.mem_bot] at this
    exact hm1 (congrArg Subtype.val this)
  · intro x hx
    have : (⟨x, hx⟩ : alternatingGroup (Fin 6)) ∈ N.subgroupOf (alternatingGroup (Fin 6)) := by
      rw [h]
      trivial
    exact this

theorem perm_six_eq_bot_of_normal {N : Subgroup (Perm (Fin 6))} (hN : N.Normal)
    (hc : Nat.card N ≤ 30) : N = ⊥ := by
  rcases perm_six_eq_bot_or_alt_le hN with h | hle
  · exact h
  · exfalso
    have hdvd := Subgroup.card_dvd_of_le hle
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega

theorem mem_centralizer_swap {a b : Fin 8} (hab : a ≠ b) {π : Perm (Fin 8)}
    (hπ : π ∈ centralizer ({swap a b} : Set (Perm (Fin 8)))) :
    (π a = a ∧ π b = b) ∨ (π a = b ∧ π b = a) := by
  have h := mem_centralizer_singleton_iff.1 hπ
  have h1 : π b = swap a b (π a) := by
    have := congrArg (fun f : Perm (Fin 8) => f a) h
    simpa using this
  by_cases ha : π a = a
  · left
    refine ⟨ha, ?_⟩
    rw [h1, ha, swap_apply_left]
  · by_cases hb : π a = b
    · right
      refine ⟨hb, ?_⟩
      rw [h1, hb, swap_apply_right]
    · exfalso
      rw [swap_apply_of_ne_of_ne ha hb] at h1
      exact hab (π.injective h1.symm)

@[expose] noncomputable def swapChar {a b : Fin 8} (hab : a ≠ b) :
    centralizer ({swap a b} : Set (Perm (Fin 8))) →* ℤˣ where
  toFun π := if (π : Perm (Fin 8)) a = a then 1 else -1
  map_one' := by simp
  map_mul' π₁ π₂ := by
    rcases mem_centralizer_swap hab π₁.2 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
    rcases mem_centralizer_swap hab π₂.2 with ⟨h2a, -⟩ | ⟨h2a, -⟩
    · simp [h1a, h2a]
    · simp [h1a, h1b, h2a, hab.symm]
    · simp [h1a, h2a, hab.symm]
    · simp [h1a, h1b, h2a, hab.symm]

theorem fixes_of_swapChar_eq_one {a b : Fin 8} (hab : a ≠ b)
    {π : centralizer ({swap a b} : Set (Perm (Fin 8)))} (h : swapChar hab π = 1) :
    (π : Perm (Fin 8)) a = a ∧ (π : Perm (Fin 8)) b = b := by
  have ha : (π : Perm (Fin 8)) a = a := by
    by_contra hne
    simp [swapChar, hne] at h
  refine ⟨ha, ?_⟩
  rcases mem_centralizer_swap hab π.2 with ⟨-, h2⟩ | ⟨h2, -⟩
  · exact h2
  · exact absurd (ha.symm.trans h2) hab

end CFSG.EvenSporadicStandard.M22Std
