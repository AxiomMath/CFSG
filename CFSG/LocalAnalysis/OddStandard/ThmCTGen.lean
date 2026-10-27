module

public import CFSG.LocalAnalysis.OddStandard.ThmCTBasic

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

theorem exists_gens_of_card_le {G : Type*} [Group G] [Finite G] :
    ∀ (m k : ℕ) (H Q : Subgroup G), H ≤ Q →
      (∃ s : Finset G, s.card ≤ k ∧ Subgroup.closure (s : Set G) = H) →
      Nat.card Q ≤ 2 ^ m * Nat.card H →
      ∃ s : Finset G, s.card ≤ k + m ∧ Subgroup.closure (s : Set G) = Q := by
  classical
  intro m
  induction m with
  | zero =>
    intro k H Q hHQ hgen hcard
    obtain ⟨s, hs, hsH⟩ := hgen
    have : H = Q := Subgroup.eq_of_le_of_card_ge hHQ (by simpa using hcard)
    exact ⟨s, by simpa using hs, hsH.trans this⟩
  | succ m ih =>
    intro k H Q hHQ hgen hcard
    obtain ⟨s, hs, hsH⟩ := hgen
    by_cases hEq : H = Q
    · exact ⟨s, by omega, hsH.trans hEq⟩
    · obtain ⟨x, hxQ, hxH⟩ :=
        IsConcreteLE.not_le_iff_exists.mp (fun h => hEq (le_antisymm hHQ h))
      set H' : Subgroup G := Subgroup.closure ((insert x s : Finset G) : Set G) with hH'
      have hsub : (s : Set G) ⊆ H := by
        rw [← hsH]; exact Subgroup.subset_closure
      have hH'Q : H' ≤ Q := by
        rw [hH', Subgroup.closure_le]
        intro y hy
        rw [Finset.coe_insert, Set.mem_insert_iff] at hy
        rcases hy with rfl | hy
        · exact hxQ
        · exact hHQ (hsub hy)
      have hHH' : H ≤ H' := by
        rw [← hsH]
        exact Subgroup.closure_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
      have hxH' : x ∈ H' := Subgroup.subset_closure (by simp)
      have hne : Nat.card H ≠ Nat.card H' := by
        intro h
        have : H = H' := Subgroup.eq_of_le_of_card_ge hHH' h.symm.le
        exact hxH (this ▸ hxH')
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hHH'
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hne (by rw [hc, mul_one])
      have hpos : 0 < Nat.card H := Nat.card_pos
      have hc0 : c ≠ 0 := by
        rintro rfl
        have : 0 < Nat.card H' := Nat.card_pos
        rw [hc, mul_zero] at this
        exact absurd this (lt_irrefl 0)
      have h2 : 2 * Nat.card H ≤ Nat.card H' := by
        rw [hc, mul_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      obtain ⟨s', hs', hs'Q⟩ := ih (k + 1) H' Q hH'Q
        ⟨insert x s, (Finset.card_insert_le _ _).trans (by omega), rfl⟩
        (by calc Nat.card Q ≤ 2 ^ (m + 1) * Nat.card H := hcard
              _ = 2 ^ m * (2 * Nat.card H) := by ring
              _ ≤ 2 ^ m * Nat.card H' := Nat.mul_le_mul_left _ h2)
      exact ⟨s', by omega, hs'Q⟩

@[expose] def ω : F4c := ⟨0, 1⟩

@[expose] def g1 : Tc := ⟨1, 0, 0⟩
@[expose] def g2 : Tc := ⟨ω, 0, 0⟩
@[expose] def g3 : Tc := ⟨0, 1, 0⟩
@[expose] def g4 : Tc := ⟨0, ω, 0⟩

theorem decomp : ∀ x : Tc, x = ⟨x.a, 0, 0⟩ * ⟨0, x.b, 0⟩ * ⟨0, 0, x.c + x.a * x.b⟩ := by
  decide +kernel

theorem F4c_cases : ∀ a : F4c, a = 0 ∨ a = 1 ∨ a = ω ∨ a = 1 + ω := by decide +kernel

theorem closure_gens : Subgroup.closure ({g1, g2, g3, g4} : Set Tc) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  set S := Subgroup.closure ({g1, g2, g3, g4} : Set Tc) with hS
  have h1 : g1 ∈ S := Subgroup.subset_closure (by simp)
  have h2 : g2 ∈ S := Subgroup.subset_closure (by simp)
  have h3 : g3 ∈ S := Subgroup.subset_closure (by simp)
  have h4 : g4 ∈ S := Subgroup.subset_closure (by simp)
  have hA : ∀ a : F4c, (⟨a, 0, 0⟩ : Tc) ∈ S := by
    intro a
    rcases F4c_cases a with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact h1
    · exact h2
    · have : (⟨1 + ω, 0, 0⟩ : Tc) = g1 * g2 := by
        refine UT3.ext ?_ ?_ ?_ <;> simp [g1, g2, UT3.mul_def]
      rw [this]; exact S.mul_mem h1 h2
  have hB : ∀ b : F4c, (⟨0, b, 0⟩ : Tc) ∈ S := by
    intro b
    rcases F4c_cases b with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact h3
    · exact h4
    · have : (⟨0, 1 + ω, 0⟩ : Tc) = g3 * g4 := by
        refine UT3.ext ?_ ?_ ?_ <;> simp [g3, g4, UT3.mul_def]
      rw [this]; exact S.mul_mem h3 h4
  have hZ : ∀ c : F4c, (⟨0, 0, c⟩ : Tc) ∈ S := by
    have e1 : ⁅g1, g3⁆ = (⟨0, 0, 1⟩ : Tc) := by rw [comm_eq]; ext <;> simp [g1, g3]
    have e2 : ⁅g1, g4⁆ = (⟨0, 0, ω⟩ : Tc) := by rw [comm_eq]; ext <;> simp [g1, g4]
    have m1 : (⟨0, 0, 1⟩ : Tc) ∈ S := by
      rw [← e1, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem h1 h3) (S.inv_mem h1)) (S.inv_mem h3)
    have m2 : (⟨0, 0, ω⟩ : Tc) ∈ S := by
      rw [← e2, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem h1 h4) (S.inv_mem h1)) (S.inv_mem h4)
    intro c
    rcases F4c_cases c with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact m1
    · exact m2
    · have : (⟨0, 0, 1 + ω⟩ : Tc) = ⟨0, 0, 1⟩ * ⟨0, 0, ω⟩ := by
        refine UT3.ext ?_ ?_ ?_ <;> simp [UT3.mul_def]
      rw [this]; exact S.mul_mem m1 m2
  rw [decomp x]
  exact S.mul_mem (S.mul_mem (hA _) (hB _)) (hZ _)

theorem orderOf_eq_four {x : Tc} (hx : x * x ≠ 1) : orderOf x = 4 := by
  have h1 : x ^ 2 ^ 1 ≠ 1 := by simpa [pow_two] using hx
  have h2 : x ^ 2 ^ (1 + 1) = 1 := pow_four x
  have := orderOf_eq_prime_pow h1 h2
  simpa using this

theorem gen4 (Q : Subgroup Tc) :
    ∃ s : Finset Tc, s.card ≤ 4 ∧ Subgroup.closure (s : Set Tc) = Q := by
  classical
  have hdvd : Nat.card Q ∣ 2 ^ 6 := by
    have := Subgroup.card_subgroup_dvd_card Q
    rw [card_Tc] at this
    simpa using this
  obtain ⟨i, hi, hQi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_cases h16 : i ≤ 4
  · obtain ⟨s, hs, hsQ⟩ := exists_gens_of_card_le 4 0 ⊥ Q bot_le ⟨∅, by simp, by simp⟩
      (by
        rw [Subgroup.card_bot, hQi]
        exact (Nat.pow_le_pow_right (by norm_num) h16).trans (by simp))
    exact ⟨s, by omega, hsQ⟩
  · have hi5 : i = 5 ∨ i = 6 := by omega
    rcases hi5 with rfl | rfl
    ·
      have hnot : ∃ x ∈ Q, x * x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hle : Nat.card Q ≤ 28 := by
          calc Nat.card Q ≤ Nat.card {t : Tc // t * t = 1} :=
                Nat.card_le_card_of_injective (fun a => ⟨a.1, hcon a.1 a.2⟩)
                  (fun a b hab => Subtype.ext (congrArg (fun t : {t : Tc // t * t = 1} => t.1) hab))
            _ = 28 := card_sq
        rw [hQi] at hle
        norm_num at hle
      obtain ⟨x, hxQ, hx⟩ := hnot
      have hord := orderOf_eq_four hx
      obtain ⟨s, hs, hsQ⟩ := exists_gens_of_card_le 3 1 (Subgroup.zpowers x) Q
        (Subgroup.zpowers_le.2 hxQ) ⟨{x}, by simp, by simp [Subgroup.zpowers_eq_closure]⟩
        (by rw [Nat.card_zpowers, hord, hQi]; norm_num)
      exact ⟨s, by omega, hsQ⟩
    · have hQtop : Q = ⊤ := Subgroup.eq_top_of_card_eq Q (by rw [hQi, card_Tc]; norm_num)
      refine ⟨{g1, g2, g3, g4}, ?_, ?_⟩
      · exact Finset.card_le_four
      · rw [hQtop]; simpa using closure_gens

end CFSG.OddStandard.ThmC.T
