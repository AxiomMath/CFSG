module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

section G4

variable {J : Type} [Group J] {A : Type} [Group A]

theorem gammaAct_eq_top_of_equivariant (α : A →* MulAut J) {ι : Type} (H : ι → Type)
    [∀ i, Group (H i)] (φ : ∀ i, H i →* J) (β : ∀ i, A →* MulAut (H i))
    (hφ : ∀ i (a : A) (x : H i), α a (φ i x) = φ i (β i a x)) (htop : ⨆ i, (φ i).range = ⊤)
    (hgen : ∀ i, gammaAct (β i) = ⊤) : gammaAct α = ⊤ := by
  rw [eq_top_iff, ← htop]
  refine iSup_le fun i => ?_
  rw [MonoidHom.range_eq_map]
  refine (Subgroup.map_mono (hgen i).ge).trans ?_
  rw [gammaAct, Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hE => ?_
  rintro _ ⟨x, hx, rfl⟩
  refine le_gammaAct α hE ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro a ha
  rw [hφ, (GenLocBasic.mem_fixedIn_map _ _ _).1 hx a ha]

end G4

section G5

variable {A : Type} [Group A]

theorem rank_ker_ge [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) {B : Type} [Group B] (χ : A →* B)
    (hχ : Nat.card χ.range ≤ 2) : pRank 2 A - 1 ≤ pRank 2 ↥χ.ker := by
  rw [GenLocBasic.adm_iff_index hA, Subgroup.index_ker]
  exact hχ

end G5

section G7

variable {J : Type} [Group J] {A : Type} [Group A]

theorem noOddNormal_of_isPGroup {H : Subgroup J} (hH : IsPGroup 2 ↥H) : NoOddNormal H := by
  intro N hNH hodd _
  have hN : IsPGroup 2 ↥N := hH.of_injective (Subgroup.inclusion hNH) (Subgroup.inclusion_injective hNH)
  have : Finite ↥N := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.1 hk

theorem locE2_of_fix (α : A →* MulAut J) (X : Subgroup J) (hX : X ≤ gammaAct α)
    (h2 : ∀ φ : MulAut J, (∀ x ∈ X, φ x = x) → ∃ n : ℕ, φ ^ (2 ^ n) = 1) : LocE2 α := by
  intro φ hodd hfix
  obtain ⟨n, hn⟩ := h2 φ fun x hx => hfix x (hX hx)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.1 hk

end G7

end CFSG.GH74.Generic.BProg.B2
