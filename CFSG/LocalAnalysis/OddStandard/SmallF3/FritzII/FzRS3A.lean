module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def fzrPhi (Y : Subgroup G) : Subgroup G :=
  ⁅Y, Y⁆ ⊔ Subgroup.closure ((fun a : G => a ^ 2) '' (Y : Set G))

private theorem fzrPhi_le (Y : Subgroup G) : fzrPhi Y ≤ Y := by
  refine sup_le (Subgroup.commutator_le_self Y) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  exact Y.pow_mem ha 2

private theorem fzrPhi_conj_mem {Y : Subgroup G} {g : G}
    (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) :
    ∀ x ∈ fzrPhi Y, g * x * g⁻¹ ∈ fzrPhi Y := by
  let c : G →* G := (MulAut.conj g).toMonoidHom
  have hc : ∀ x : G, c x = g * x * g⁻¹ := fun x => MulAut.conj_apply g x
  have key : fzrPhi Y ≤ (fzrPhi Y).comap c := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      change c ⁅a, b⁆ ∈ fzrPhi Y
      rw [map_commutatorElement, hc a, hc b]
      exact Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator (hY a ha) (hY b hb))
    · rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      change c (a ^ 2) ∈ fzrPhi Y
      rw [hc]
      have h2 : g * a ^ 2 * g⁻¹ = (g * a * g⁻¹) ^ 2 := by
        rw [← hc (a ^ 2), ← hc a, map_pow]
      rw [h2]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨g * a * g⁻¹, hY a ha, rfl⟩)
  intro x hx
  have := key hx
  rwa [Subgroup.mem_comap, hc] at this

private theorem commutator_mem_of_index_two {K : Type*} [Group K] {H : Subgroup K}
    (hH : H.index = 2) (x y : K) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hH,
    Subgroup.mul_mem_iff_of_index_two hH, Subgroup.mul_mem_iff_of_index_two hH,
    inv_mem_iff, inv_mem_iff]
  tauto

private theorem fzrPhi_lt {Y : Subgroup G} (hY : IsPGroup 2 Y) (hne : Y ≠ ⊥) :
    fzrPhi Y < Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : (1 : ℕ) < Nat.card Y := (Subgroup.one_lt_card_iff_ne_bot Y).mpr hne
  obtain ⟨m, hm⟩ := hY.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact absurd hm hlt.ne'
  have hdvd : 2 ∣ Nat.card Y := hm ▸ dvd_pow_self 2 hm0
  haveI : Group.IsNilpotent ↥Y := IsPGroup.isNilpotent (p := 2) hY
  obtain ⟨H, hHidx, hHnorm⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := Y) (k := 2) hdvd
  haveI : H.Normal := hHnorm
  refine lt_of_le_of_lt ?_ (lt_of_le_of_ne (Subgroup.map_subtype_le (H := Y) H) ?_)
  · refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      have hmem := Subgroup.mem_map_of_mem Y.subtype
        (commutator_mem_of_index_two hHidx (⟨a, ha⟩ : Y) (⟨b, hb⟩ : Y))
      simpa using hmem
    · rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      have hmem := Subgroup.mem_map_of_mem Y.subtype
        (Subgroup.sq_mem_of_index_two hHidx (⟨a, ha⟩ : Y))
      simpa using hmem
  · intro heq
    have hHtop : H = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro y
      have : Y.subtype y ∈ H.map Y.subtype := by rw [heq]; exact y.2
      obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp this
      rwa [← Y.subtype_injective hhy]
    rw [hHtop, Subgroup.index_top] at hHidx
    omega

private theorem fzrPhi_iterate_le (Y : Subgroup G) (k : ℕ) :
    (fzrPhi^[k]) Y ≤ Y := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (fzrPhi_le _).trans ih

theorem fzr_series_exists {X : Subgroup G} {A : Set G} (hX : IsPGroup 2 X)
    (hA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∃ (n : ℕ) (W : ℕ → Subgroup G), W 0 = X ∧ W n = ⊥ ∧ (∀ i < n, W (i + 1) ≤ W i) ∧
      (∀ i ≤ n, ∀ g ∈ A, ∀ x ∈ W i, g * x * g⁻¹ ∈ W i) ∧
      (∀ i < n, ∀ a ∈ W i, ∀ b ∈ W i, ⁅a, b⁆ ∈ W (i + 1)) ∧
      (∀ i < n, ∀ a ∈ W i, a ^ 2 ∈ W (i + 1)) := by
  classical
  let W : ℕ → Subgroup G := fun i => (fzrPhi^[i]) X
  have hW0 : W 0 = X := rfl
  have hWsucc : ∀ i, W (i + 1) = fzrPhi (W i) := by
    intro i
    show (fzrPhi^[i + 1]) X = fzrPhi ((fzrPhi^[i]) X)
    rw [show i + 1 = i.succ from rfl, Function.iterate_succ_apply']
  have hWle : ∀ i, W i ≤ X := fun i => fzrPhi_iterate_le X i
  have hW2 : ∀ i, IsPGroup 2 (W i) := fun i => hX.to_le (hWle i)
  refine ⟨Nat.card ↥X, W, hW0, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hWn
    have hcard : ∀ i ≤ Nat.card ↥X, W i ≠ ⊥ → Nat.card (W i) + i ≤ Nat.card ↥X := by
      intro i
      induction i with
      | zero => intro _ _; simp [hW0]
      | succ i ih =>
        intro hi hne
        have hi' : i ≤ Nat.card ↥X := by omega
        have hWi : W i ≠ ⊥ := by
          intro hbot
          apply hne
          rw [hWsucc i, hbot]
          exact le_bot_iff.mp (fzrPhi_le ⊥)
        have hdec : Nat.card (W (i + 1)) < Nat.card (W i) := by
          rw [hWsucc i]
          exact Subgroup.card_lt_of_lt (fzrPhi_lt (hW2 i) hWi)
        have := ih hi' hWi
        omega
    have := hcard (Nat.card ↥X) le_rfl hWn
    have hpos : 1 < Nat.card (W (Nat.card ↥X)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hWn
    omega
  · intro i _
    rw [hWsucc i]
    exact fzrPhi_le _
  · intro i
    induction i with
    | zero =>
      intro _ g hg x hx
      rw [hW0] at hx ⊢
      exact hA g hg x hx
    | succ i ih =>
      intro hi g hg x hx
      rw [hWsucc i] at hx ⊢
      exact fzrPhi_conj_mem (fun y hy => ih (by omega) g hg y hy) x hx
  · intro i _ a ha b hb
    rw [hWsucc i]
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hb)
  · intro i _ a ha
    rw [hWsucc i]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, ha, rfl⟩)

end CFSG.OddStandard.SmallF3.FritzII
