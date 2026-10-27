module

public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped Pointwise

section Lines

variable {K : Type} [Group K] [Finite K]

theorem irred62x_card_lines {f : ℕ} (hf : f.Prime) {A : Subgroup K} (hA3 : Nat.card A = f ^ 3)
    (hA1 : ∀ y ∈ A, y ^ f = 1) :
    Nat.card {L : Subgroup K // L ≤ A ∧ Nat.card L = f} = f ^ 2 + f + 1 := by
  classical
  have : Fact f.Prime := ⟨hf⟩
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (Subgroup K)
  let S : Finset K := Finset.univ.filter fun a => a ∈ A ∧ a ≠ 1
  let T : Finset (Subgroup K) := Finset.univ.filter fun L => L ≤ A ∧ Nat.card L = f
  have hord : ∀ a ∈ A, a ≠ 1 → orderOf a = f := fun a ha ha1 => orderOf_eq_prime (hA1 a ha) ha1
  have hS : S.card = f ^ 3 - 1 := by
    have h1 : Nat.card A = (Finset.univ.filter fun a => a ∈ A).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h2 : S = (Finset.univ.filter fun a => a ∈ A).erase 1 := by
      ext a
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [h2, Finset.card_erase_of_mem (by simp [one_mem]), ← h1, hA3]
  have hT : Nat.card {L : Subgroup K // L ≤ A ∧ Nat.card L = f} = T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmaps : (S : Set K).MapsTo (fun a => (zpowers a : Subgroup K)) (T : Set (Subgroup K)) := by
    intro a ha
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨Subgroup.zpowers_le.2 ha.1, by rw [Nat.card_zpowers, hord a ha.1 ha.2]⟩
  have hfib : ∀ L ∈ T, (S.filter fun a => (zpowers a : Subgroup K) = L).card = f - 1 := by
    intro L hL
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    have h3 : (S.filter fun a => (zpowers a : Subgroup K) = L) =
        (Finset.univ.filter fun a => a ∈ L).erase 1 := by
      ext a
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, ha1⟩, hzL⟩
        exact ⟨ha1, hzL ▸ Subgroup.mem_zpowers a⟩
      · rintro ⟨ha1, haL⟩
        refine ⟨⟨hL.1 haL, ha1⟩, ?_⟩
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haL) ?_
        rw [Nat.card_zpowers, hord a (hL.1 haL) ha1, hL.2]
    have h4 : Nat.card L = (Finset.univ.filter fun a => a ∈ L).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h3, Finset.card_erase_of_mem (by simp [one_mem]), ← h4, hL.2]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hS] at hsum
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := hf.one_lt; omega⟩
  have hg : 0 < g := by have := hf.one_lt; omega
  rw [hT]
  refine Nat.eq_of_mul_eq_mul_left hg ?_
  have : (g + 1) ^ 3 - 1 = g * ((g + 1) ^ 2 + (g + 1) + 1) := by
    have h5 : (g + 1) ^ 3 = g * ((g + 1) ^ 2 + (g + 1) + 1) + 1 := by ring
    omega
  simp only [Nat.add_sub_cancel] at hsum
  rw [this] at hsum
  rw [mul_comm g T.card]
  exact hsum.symm

theorem irred62x_exists_fixed_line {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {A : Subgroup K}
    (hA3 : Nat.card A = f ^ 3) (hA1 : ∀ y ∈ A, y ^ f = 1) {Γ : Subgroup K}
    (hΓ : ∀ g ∈ Γ, ∀ y, y ∈ A ↔ g * y * g⁻¹ ∈ A)
    (h2 : ∀ g ∈ Γ, ∃ n : ℕ, ∀ a ∈ A, g ^ (2 ^ n) * a = a * g ^ (2 ^ n)) :
    ∃ L : Subgroup K, L ≤ A ∧ Nat.card L = f ∧ ∀ g ∈ Γ, g ∈ normalizer (L : Set K) := by
  classical
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ₀ : ↥Γ →* MulAut K := (MulAut.conj : K →* MulAut K).comp Γ.subtype
  let _ : MulAction ↥Γ (Subgroup K) := MulAction.compHom (Subgroup K) ρ₀
  have hsmul : ∀ (g : ↥Γ) (L : Subgroup K), g • L = L.map (MulAut.conj (g : K)).toMonoidHom :=
    fun g L => rfl
  let Y : SubMulAction ↥Γ (Subgroup K) :=
    { carrier := {L | L ≤ A ∧ Nat.card L = f}
      smul_mem' := by
        intro g L hL
        rw [hsmul]
        refine ⟨?_, ?_⟩
        · rintro _ ⟨l, hl, rfl⟩
          exact (hΓ g g.2 l).1 (hL.1 hl)
        · rw [Subgroup.card_map_of_injective (MulAut.conj (g : K)).injective]
          exact hL.2 }
  have hY : Nat.card ↥Y = f ^ 2 + f + 1 := by
    rw [← irred62x_card_lines hf hA3 hA1]
    exact Nat.card_congr (Equiv.refl _)
  let ρ := MulAction.toPermHom ↥Γ ↥Y
  let S : Subgroup (Equiv.Perm ↥Y) := ρ.range
  have hS2 : IsPGroup 2 ↥S := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨n, hn⟩ := h2 (g : K) g.2
    refine ⟨n, Subtype.ext ?_⟩
    have hone : ρ (g ^ 2 ^ n) = 1 := by
      refine Equiv.ext fun L => ?_
      refine Subtype.ext ?_
      change (g ^ 2 ^ n) • L.1 = L.1
      rw [hsmul]
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        have hc := hn l (L.2.1 hl)
        have : (MulAut.conj ((g ^ 2 ^ n : ↥Γ) : K)).toMonoidHom l = l := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_pow]
          rw [hc, mul_inv_cancel_right]
        rw [this]
        exact hl
      · intro hx
        refine ⟨x, hx, ?_⟩
        have hc := hn x (L.2.1 hx)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_pow]
        rw [hc, mul_inv_cancel_right]
    change ρ g ^ 2 ^ n = 1
    rw [← map_pow]
    exact hone
  have hmod := hS2.card_modEq_card_fixedPoints (α := ↥Y)
  have hodd : Odd (f ^ 2 + f + 1) := by
    obtain ⟨m, hm⟩ := hf.odd_of_ne_two hf2
    exact ⟨2 * m ^ 2 + 3 * m + 1, by rw [hm]; ring⟩
  have hfix : Nat.card (MulAction.fixedPoints ↥S ↥Y) ≠ 0 := by
    intro h0
    rw [h0, hY] at hmod
    have := (Nat.modEq_zero_iff_dvd.1 hmod.symm.symm)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (by simpa using this))
  obtain ⟨⟨L, hL⟩, hLfix⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix) |>.1
  refine ⟨L, hL.1, hL.2, fun g hg => ?_⟩
  have h1 : (⟨ρ ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩ : ↥S) • (⟨L, hL⟩ : ↥Y) = ⟨L, hL⟩ := hLfix _
  have h3 : (⟨g, hg⟩ : ↥Γ) • (⟨L, hL⟩ : ↥Y) = ⟨L, hL⟩ := h1
  have h4 := congrArg Subtype.val h3
  change (⟨g, hg⟩ : ↥Γ) • L = L at h4
  rw [hsmul] at h4
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h4

end Lines

end CFSG.LocalAnalysis.RankThreeTheoremC
