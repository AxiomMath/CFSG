module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm Subgroup

theorem lookup_cycleType_of_orderOf_four {σ : Perm (Fin 9)} (h4 : orderOf σ = 4)
    (hs : sign σ = 1) : σ.cycleType = {4, 2} ∨ σ.cycleType = {4, 4} := by
  have hmem : ∀ n ∈ σ.cycleType, n = 2 ∨ n = 4 := by
    intro n hn
    have h1 : n ∣ 4 := h4 ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h0 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have : n ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    interval_cases n <;> simp_all
  have hsum : σ.cycleType.sum ≤ 9 := by simpa using Equiv.Perm.sum_cycleType_le σ
  have h4mem : 4 ∈ σ.cycleType := by
    by_contra hn
    have h2 : σ.cycleType.lcm ∣ 2 := Multiset.lcm_dvd.mpr fun n hn' => by
      rcases hmem n hn' with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn' hn
    rw [Equiv.Perm.lcm_cycleType, h4] at h2
    norm_num at h2
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hs] at hsign
  obtain ⟨c, hc⟩ := Multiset.exists_cons_of_mem h4mem
  rw [hc] at hsign hsum hmem ⊢
  rcases Multiset.empty_or_exists_mem c with h0 | ⟨m, hm⟩
  · subst h0
    exfalso
    revert hsign
    decide
  · obtain ⟨d, hd⟩ := Multiset.exists_cons_of_mem hm
    subst hd
    have hm2 : m = 2 ∨ m = 4 := hmem m (by simp)
    rcases Multiset.empty_or_exists_mem d with h0 | ⟨k, hk⟩
    · subst h0
      rcases hm2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exfalso
      obtain ⟨e, he⟩ := Multiset.exists_cons_of_mem hk
      subst he
      have hk2 : k = 2 ∨ k = 4 := hmem k (by simp)
      have hlow : ∀ x ∈ e, 2 ≤ x := fun x hx => by
        rcases hmem x (by simp [hx]) with h | h <;> omega
      rcases Multiset.empty_or_exists_mem e with h0 | ⟨j, hj⟩
      · subst h0
        simp only [Multiset.sum_cons, Multiset.sum_zero] at hsum hsign
        rcases hm2 with rfl | rfl <;> rcases hk2 with rfl | rfl
        · revert hsign
          decide
        all_goals omega
      · have hj2 : 2 ≤ j := hlow j hj
        have hle : j ≤ e.sum := Multiset.le_sum_of_mem hj
        simp only [Multiset.sum_cons] at hsum
        rcases hm2 with rfl | rfl <;> rcases hk2 with rfl | rfl <;> omega


theorem lookup_exists_odd_commute_of_four_mem {σ : Perm (Fin 9)} (h : 4 ∈ σ.cycleType) :
    ∃ d : Perm (Fin 9), d * σ = σ * d ∧ sign d = -1 := by
  rw [Equiv.Perm.cycleType_def] at h
  obtain ⟨d, hd, hd2⟩ := Multiset.mem_map.mp h
  have hdc : d.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hd).1
  refine ⟨d, (Equiv.Perm.self_mem_cycle_factors_commute hd).eq, ?_⟩
  rw [hdc.sign]
  simp only [Function.comp_apply] at hd2
  rw [hd2]
  decide

theorem lookup_alt9_no_big_centralizer {q : Perm (Fin 9)} (hq4 : orderOf q = 4)
    (hqs : sign q = 1) {W : Subgroup (Perm (Fin 9))} (hWA : W ≤ alternatingGroup (Fin 9))
    (hWc : W ≤ centralizer ({q} : Set (Perm (Fin 9)))) (hW : Nat.card W = 32) : False := by
  have h32 : 32 ∣ Nat.card (centralizer ({q} : Set (Perm (Fin 9)))) :=
    hW ▸ Subgroup.card_dvd_of_le hWc
  rcases lookup_cycleType_of_orderOf_four hq4 hqs with h | h
  · rw [Equiv.Perm.nat_card_centralizer, h] at h32
    revert h32
    decide
  · have hcard : Nat.card (centralizer ({q} : Set (Perm (Fin 9)))) = 32 := by
      rw [Equiv.Perm.nat_card_centralizer, h]
      decide
    have heq : W = centralizer ({q} : Set (Perm (Fin 9))) :=
      Subgroup.eq_of_le_of_card_ge hWc (by rw [hcard, hW])
    obtain ⟨d, hdq, hds⟩ := lookup_exists_odd_commute_of_four_mem (σ := q)
      (by rw [h]; simp)
    have hd : d ∈ W := by
      rw [heq, mem_centralizer_singleton_iff]
      exact hdq
    have h1 := Perm.mem_alternatingGroup.1 (hWA hd)
    rw [hds] at h1
    exact absurd h1 (by decide)


theorem lookup_false_of_alt9_order_four {H : Type} [Group H]
    (ψ : H ≃* alternatingGroup (Fin 9)) {q : H} (hq : orderOf q = 4) {W : Subgroup H}
    (hW : Nat.card W = 32) (hc : ∀ w ∈ W, w * q = q * w) : False := by
  have hq' : orderOf ((ψ q : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hq]
  have hqs : sign ((ψ q : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 1 :=
    Perm.mem_alternatingGroup.1 (ψ q).2
  refine lookup_alt9_no_big_centralizer (W := (W.map ψ.toMonoidHom).map
      (alternatingGroup (Fin 9)).subtype) hq' hqs ?_ ?_ ?_
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact (ψ w).2
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg (fun x => ((ψ x : alternatingGroup (Fin 9)) : Perm (Fin 9))) (hc w hw)
    simpa using h1
  · rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective,
      Subgroup.card_map_of_injective ψ.injective, hW]

theorem lookup_dvd_factorial_div_two_ten {m : ℕ} (hm : 10 ≤ m) : 1814400 ∣ m.factorial / 2 := by
  have h : 2 * 1814400 ∣ m.factorial := by
    have := Nat.factorial_dvd_factorial hm
    norm_num [Nat.factorial] at this ⊢
    exact this
  exact Nat.dvd_div_of_mul_dvd (by simpa [mul_comm] using h)

end CFSG.OddStandard.AltStdSec
