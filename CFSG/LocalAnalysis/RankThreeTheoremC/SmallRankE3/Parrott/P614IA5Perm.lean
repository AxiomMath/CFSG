module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open Equiv

@[expose] def cA : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def sA : Perm (Fin 5) := swap 3 4

@[expose] def dA : Perm (Fin 5) := swap 2 3 * swap 3 4

@[expose] def gA : Perm (Fin 5) := (cA * dA) * (cA * dA)

theorem sA_ne_one : sA ≠ 1 := by decide

theorem sign_sA : Perm.sign sA = -1 := by decide

theorem sign_swap01 : Perm.sign (swap (0 : Fin 5) 1) = -1 := by decide

theorem gA_conj : gA * cA * gA⁻¹ = dA := by decide

set_option maxRecDepth 100000 in
theorem exists_conj_cA : ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    ∃ g : Perm (Fin 5), g * c * g⁻¹ = cA := by
  decide

set_option maxRecDepth 100000 in
theorem eq_sA_of_odd : ∀ s : Perm (Fin 5), s ^ 8 = 1 → Perm.sign s = -1 →
    (s * (cA * s * cA⁻¹)) ^ 8 = 1 → s = sA := by
  decide

set_option maxRecDepth 100000 in
theorem eq_one_of_stab : ∀ s : Perm (Fin 5), s 0 = 0 → s 1 = 1 → s ^ 8 = 1 →
    (s * (dA * s * dA⁻¹)) ^ 8 = 1 → s = 1 := by
  decide

theorem isCycle_cAdA : (cA * dA).IsCycle := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : orderOf (cA * dA) = 5 := orderOf_eq_prime (by decide) (by decide)
  exact Equiv.Perm.isCycle_of_prime_order (by rw [h5]; exact Nat.prime_five) (by rw [h5]; decide)

theorem support_cAdA : (cA * dA).support = Finset.univ := by decide

theorem cAdA_three : (cA * dA) 3 = 4 := by decide

theorem eq_top_of_mem {L : Subgroup (Perm (Fin 5))} (hc : cA ∈ L) (hd : dA ∈ L) (hs : sA ∈ L) :
    L = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap isCycle_cAdA support_cAdA 3
  rw [cAdA_three] at h
  refine eq_top_iff.2 (h ▸ (Subgroup.closure_le L).2 ?_)
  intro g hg
  rcases hg with rfl | rfl
  · exact L.mul_mem hc hd
  · exact hs

theorem pow_eight_eq_one {g : Perm (Fin 5)} {k : ℕ} (h : g ^ 2 ^ k = 1) : g ^ 8 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  have hcard : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hdvd : 2 ^ j ∣ 120 := hcard ▸ hj ▸ orderOf_dvd_natCard g
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow 2 hj3)

abbrev Rest (x : Fin 5) : Prop := x ≠ 0 ∧ x ≠ 1

@[expose] noncomputable def stab01 : Subgroup (Perm (Fin 5)) :=
  (Equiv.Perm.ofSubtype : Perm (Subtype Rest) →* Perm (Fin 5)).range

theorem mem_stab01 {g : Perm (Fin 5)} : g ∈ stab01 ↔ g 0 = 0 ∧ g 1 = 1 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Equiv.Perm.ofSubtype_apply_of_not_mem f (by simp [Rest]),
      Equiv.Perm.ofSubtype_apply_of_not_mem f (by simp [Rest])⟩
  · rintro ⟨h0, h1⟩
    have hp : ∀ x, Rest (g x) ↔ Rest x := by
      intro x
      simp only [Rest]
      constructor
      · rintro ⟨hx0, hx1⟩
        exact ⟨fun h => hx0 (h ▸ h0), fun h => hx1 (h ▸ h1)⟩
      · rintro ⟨hx0, hx1⟩
        refine ⟨fun h => hx0 (g.injective (h.trans h0.symm)),
          fun h => hx1 (g.injective (h.trans h1.symm))⟩
    have hm : ∀ x, g x ≠ x → Rest x := by
      intro x hx
      refine ⟨fun h => hx (h ▸ h0), fun h => hx (h ▸ h1)⟩
    exact ⟨g.subtypePerm hp, Equiv.Perm.ofSubtype_subtypePerm hp hm⟩

theorem sA_mem_stab01 : sA ∈ stab01 := mem_stab01.2 (by decide)

theorem dA_mem_stab01 : dA ∈ stab01 := mem_stab01.2 (by decide)

theorem card_rest : Fintype.card (Subtype Rest) = 3 := by decide

noncomputable def stab01Equiv : ↥stab01 ≃* Perm (Fin 3) :=
  (MonoidHom.ofInjective (Equiv.Perm.ofSubtype_injective (p := Rest))).symm.trans
    (Fintype.equivOfCardEq (by rw [card_rest, Fintype.card_fin])).permCongrHom

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
