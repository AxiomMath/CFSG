module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Equiv.Perm Subgroup

theorem perm_six_cycleType_cases (σ : Perm (Fin 6)) (hs : sign σ = 1) (h : σ * σ ≠ 1) :
    σ.cycleType = {3} ∨ σ.cycleType = {5} ∨ σ.cycleType = {3, 3} ∨ σ.cycleType = {2, 4} := by
  have hord : ¬ orderOf σ ∣ 2 := fun hd =>
    h (by simpa [pow_two] using orderOf_dvd_iff_pow_eq_one.1 hd)
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => two_le_of_mem_cycleType hn
  have hsum : σ.cycleType.sum ≤ 6 := by simpa using sum_cycleType_le σ
  have hlcm := lcm_cycleType σ
  have heven : Even (σ.cycleType.sum + Multiset.card σ.cycleType) := by
    have := sign_of_cycleType σ
    rw [hs] at this
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 this.symm
  rw [← hlcm] at hord
  generalize σ.cycleType = m at *
  obtain ⟨l, rfl⟩ : ∃ l : List ℕ, (l : Multiset ℕ) = m := ⟨m.toList, Multiset.coe_toList m⟩
  simp only [Multiset.mem_coe, Multiset.sum_coe, Multiset.coe_card, Nat.even_iff] at h2 hsum heven
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · exact absurd (by decide) hord
  · simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at h2 hsum heven
    have : a = 3 ∨ a = 5 := by omega
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2 hsum heven
    have : (a = 3 ∧ b = 3) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨ (a = 2 ∧ b = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inr (by decide)))
    · exact absurd (by decide) hord
  · simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2 hsum heven
    omega
  · simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp] at h2 hsum
    omega

theorem a6_comm_sq (P : Subgroup (alternatingGroup (Fin 6))) (hP : Nat.card P = 8)
    (a : alternatingGroup (Fin 6)) (ha : ∀ x ∈ P, a * x = x * a) : a * a = 1 := by
  by_contra hne
  have hsign : sign (a : Perm (Fin 6)) = 1 := mem_alternatingGroup.1 a.2
  have hsq : (a : Perm (Fin 6)) * a ≠ 1 := fun h => hne (Subtype.ext h)
  set σ : Perm (Fin 6) := (a : Perm (Fin 6)) with hσ
  set Q : Subgroup (Perm (Fin 6)) := P.map (alternatingGroup (Fin 6)).subtype with hQ
  have hQcard : Nat.card Q = 8 := by
    rw [hQ, card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective, hP]
  have hQle : Q ≤ centralizer {σ} := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (ha x hx).symm)
  have hdvd : 8 ∣ Nat.card (centralizer {σ}) := hQcard ▸ card_dvd_of_le hQle
  rw [nat_card_centralizer] at hdvd
  rcases perm_six_cycleType_cases σ hsign hsq with h | h | h | h
  · rw [h] at hdvd
    revert hdvd
    decide
  · rw [h] at hdvd
    revert hdvd
    decide
  · rw [h] at hdvd
    revert hdvd
    decide
  · have hC : Nat.card (centralizer {σ}) = 8 := by
      rw [nat_card_centralizer, h]
      decide
    have hQeq : Q = centralizer {σ} := eq_of_le_of_card_ge hQle (by rw [hQcard, hC])
    obtain ⟨c, τ, hστ, hd, hc, hcs⟩ := mem_cycleType_iff.1 (show 2 ∈ σ.cycleType by rw [h]; simp)
    have hcmem : c ∈ centralizer {σ} := by
      rw [mem_centralizer_singleton_iff, hστ]
      calc c * (c * τ) = c * (τ * c) := by rw [hd.commute.eq]
        _ = c * τ * c := by rw [mul_assoc]
    rw [← hQeq] at hcmem
    obtain ⟨x, -, rfl⟩ := hcmem
    have h1 : sign ((alternatingGroup (Fin 6)).subtype x) = 1 := mem_alternatingGroup.1 x.2
    rw [hc.sign, hcs] at h1
    exact absurd h1 (by decide)

theorem sq_eq_one_of_comm_order_eight {N : Type*} [Group N] (e : N ≃* alternatingGroup (Fin 6))
    (P : Subgroup N) (hP : Nat.card P = 8) (a : N) (ha : ∀ x ∈ P, a * x = x * a) :
    a * a = 1 := by
  have h := a6_comm_sq (P.map e.toMonoidHom)
    (by rw [card_map_of_injective (f := e.toMonoidHom) e.injective, hP]) (e a) (by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, ha x hx])
  exact e.injective (by rw [map_mul, map_one]; exact h)

theorem sq_eq_one_of_comm_order_eight_of_le {Y : Type*} [Group Y] {N : Subgroup Y}
    (e : ↥N ≃* alternatingGroup (Fin 6)) :
    ∀ P : Subgroup Y, P ≤ N → Nat.card P = 8 → ∀ a ∈ N,
      (∀ x ∈ P, a * x = x * a) → a * a = 1 := by
  intro P hPN hP a haN ha
  have hcard : Nat.card (P.subgroupOf N) = 8 := by
    rw [← hP]
    exact Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv
  have h := sq_eq_one_of_comm_order_eight e (P.subgroupOf N) hcard ⟨a, haN⟩ (by
    intro x hx
    exact Subtype.ext (ha x (mem_subgroupOf.1 hx)))
  exact congrArg Subtype.val h

end CFSG.EvenSporadicStandard.Fin76b
