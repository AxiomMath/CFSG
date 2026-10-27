module

public import CFSG.Quasithin.Background.A3Structure315Defs
public import CFSG.GH74.Filter.Small.Unipotent
public import CFSG.GH74.Filter.Orthogonal.UnitaryEven
public import CFSG.GH74.Filter.Small.Exceptional
public import CFSG.GH74.Filter.Lie.TwistedD4Even
public import CFSG.GH74.Filter.Lie.TwistedF4
public import CFSG.GH74.Filter.Lie.Suzuki
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.QTGen4.Leaves.L14742

open CFSG.GH74

theorem exists_finset_closure_eq_of_card_eq_pow_two {X : Type*} [Group X] [Finite X] :
    ∀ (k : ℕ) (P : Subgroup X), Nat.card P = 2 ^ k →
      ∃ s : Finset X, s.card ≤ k ∧ Subgroup.closure (s : Set X) = P := by
  intro k
  induction k with
  | zero =>
    intro P h
    refine ⟨∅, le_rfl, ?_⟩
    rw [Finset.coe_empty, Subgroup.closure_empty]
    exact (Subgroup.eq_bot_of_card_eq P (by simpa using h)).symm
  | succ k ih =>
    intro P h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨M', hM'⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 2
      (show 2 ^ k ∣ Nat.card P from ⟨2, by rw [h]; ring⟩)
    set M : Subgroup X := M'.map P.subtype with hMdef
    have hMcard : Nat.card M = 2 ^ k := by
      rw [hMdef, Subgroup.card_map_of_injective P.subtype_injective, hM']
    have hMP : M ≤ P := fun x ⟨y, _, hy⟩ => hy ▸ y.2
    obtain ⟨s, hs, hsM⟩ := ih M hMcard
    have hne : ∃ b ∈ P, b ∉ M := by
      by_contra hcon
      push Not at hcon
      have hPM : P ≤ M := hcon
      have := Subgroup.card_le_of_le hPM
      rw [hMcard, h] at this
      have := Nat.pow_le_pow_iff_right (le_refl 2 |>.trans (le_refl 2)) |>.1 this
      omega
    obtain ⟨b, hbP, hbM⟩ := hne
    classical
    refine ⟨insert b s, (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs), ?_⟩
    have hle : Subgroup.closure ((insert b s : Finset X) : Set X) ≤ P := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [Finset.coe_insert] at hx
      rcases hx with rfl | hx
      · exact hbP
      · exact hMP (hsM ▸ Subgroup.subset_closure hx)
    have hMle : M ≤ Subgroup.closure ((insert b s : Finset X) : Set X) := by
      rw [← hsM]
      exact Subgroup.closure_mono (by simp [Finset.coe_insert])
    have hbmem : b ∈ Subgroup.closure ((insert b s : Finset X) : Set X) :=
      Subgroup.subset_closure (by simp)
    have hlt : M < Subgroup.closure ((insert b s : Finset X) : Set X) :=
      lt_of_le_of_ne hMle fun h' => hbM (h' ▸ hbmem)
    have hdvd : Nat.card (Subgroup.closure ((insert b s : Finset X) : Set X)) ∣ Nat.card P :=
      Subgroup.card_dvd_of_le hle
    have hgt : 2 ^ k < Nat.card (Subgroup.closure ((insert b s : Finset X) : Set X)) := by
      rw [← hMcard]
      exact Subgroup.card_lt_of_lt hlt
    rw [h] at hdvd
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have : Nat.card (Subgroup.closure ((insert b s : Finset X) : Set X)) = 2 ^ (k + 1) := by
      rw [hjeq] at hgt ⊢
      have hjk : k < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hgt
      have : j = k + 1 := by omega
      rw [this]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [this, h])

theorem gen4_of_card_dvd_168 {X : Type*} [Group X] [Finite X] (hd : Nat.card X ∣ 168) :
    Gen4 X := by
  intro P hP
  have : Finite P := inferInstance
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hdvd : 2 ^ j ∣ 168 := hj ▸ (Subgroup.card_subgroup_dvd_card P).trans hd
  have hj3 : j ≤ 3 := by
    by_contra h
    push Not at h
    have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 h
    have := h16.trans hdvd
    omega
  obtain ⟨s, hs, hsP⟩ := exists_finset_closure_eq_of_card_eq_pow_two j P hj
  exact ⟨s, hs.trans (by omega), hsP⟩

open CFSG.Quasithin CFSG.Open in
theorem not_isLieChar2_of_card_dvd_168
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (h : A315.IsLieChar2 n X) (hd : Nat.card X ∣ 168) : False := by
  have hG4 : Gen4 X := gen4_of_card_dvd_168 hd
  rcases h with h | h | h | h | h | h | h | h
  ·
    by_cases h5 : 5 ≤ n
    · exact (Filter.t_PSL_even_unipotent X 2 n h (by simpa using h5)) hG4
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
      rw [hc] at hd
      interval_cases n <;> revert hd <;> decide
  ·
    by_cases h3 : 3 ≤ n
    · exact (Filter.t_PSL_even_unipotent X 3 n h (by simp; omega)) hG4
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
      rw [hc] at hd
      interval_cases n
      revert hd; decide
  ·
    by_cases h3 : 3 ≤ n
    · exact (Filter.t_PSU_even X 3 n h (by simpa using h3)) hG4
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
      rw [hc] at hd
      interval_cases n
      revert hd; decide
  ·
    exact (Filter.t_PSp_even_unipotent X 2 n h (by omega)) hG4
  · exact (Filter.t_G2_even X n h) hG4
  · exact (Filter.t_3D4_even X n h) hG4
  ·
    obtain ⟨-, a, ha, hna, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
    by_cases h5 : 5 ≤ n
    · exact (Filter.t_suzuki_large X 2 n h5 h) hG4
    · have : n = 3 := by omega
      subst this
      rw [hcard] at hd
      revert hd; decide
  · exact (Filter.t_twistedF4 X n h) hG4

end CFSG.GH74.QTGen4.Leaves.L14742

end
