module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyDerive
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_ssub_twoGroup [Finite G] {R₀ R₁ : Subgroup G} (hR₁ : IsPGroup 2 R₁)
    (h : R₀ < R₁) : ∃ g ∈ R₁, g ∈ normalizer (R₀ : Set G) ∧ g ∉ R₀ := by
  haveI : Group.IsNilpotent R₁ := hR₁.isNilpotent
  have hlt : R₀.subgroupOf R₁ < ⊤ :=
    lt_top_iff_ne_top.2 fun h' => not_le_of_gt h (Subgroup.subgroupOf_eq_top.1 h')
  obtain ⟨x, hxn, hxR⟩ := SetLike.exists_of_lt
    ((normalizerCondition_of_isNilpotent (G := R₁)) _ hlt)
  have hx : x ∈ (normalizer (R₀ : Set G)).subgroupOf R₁ := by
    rw [Subgroup.subgroupOf_normalizer_eq h.le]
    exact hxn
  exact ⟨x, x.2, hx, fun hg => hxR (Subgroup.mem_subgroupOf.2 hg)⟩

theorem two_mul_card_le_normalizer_inf [Finite G] {R₀ R₁ : Subgroup G} (hR₁ : IsPGroup 2 R₁)
    (h : R₀ < R₁) :
    2 * Nat.card R₀ ≤ Nat.card (R₁ ⊓ normalizer (R₀ : Set G) : Subgroup G) := by
  obtain ⟨g, hg1, hgn, hg0⟩ := exists_mem_normalizer_ssub_twoGroup hR₁ h
  have hle : R₀ ≤ R₁ ⊓ normalizer (R₀ : Set G) := le_inf h.le Subgroup.le_normalizer
  have hlt : R₀ < R₁ ⊓ normalizer (R₀ : Set G) :=
    lt_of_le_of_ne hle fun heq => hg0 (heq ▸ ⟨hg1, hgn⟩)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hlt' := Subgroup.card_lt_of_lt hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have h1 : Nat.card R₀ * k ≤ Nat.card R₀ * 1 := Nat.mul_le_mul_left _ (by omega)
    rw [← hk, mul_one] at h1
    omega
  calc 2 * Nat.card R₀ = Nat.card R₀ * 2 := mul_comm _ _
    _ ≤ Nat.card R₀ * k := Nat.mul_le_mul_left _ hk2
    _ = _ := hk.symm

theorem false_of_restriction [Finite G] {H : Subgroup G} (Φ : H →* Perm (Fin 11))
    (hker : Nat.card Φ.ker ≤ 2) {B N : Subgroup G} (hBH : B ≤ H) (hNH : N ≤ H)
    (hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hBc : Nat.card B = 27) (hN : IsPGroup 2 N) (hNc : 64 ≤ Nat.card N)
    (hBN : B ≤ normalizer (N : Set G)) : False := by
  let B' : Subgroup H := B.subgroupOf H
  let N' : Subgroup H := N.subgroupOf H
  have hBc' : Nat.card B' = 27 := by
    rw [← hBc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hNc' : 64 ≤ Nat.card N' := by
    have : Nat.card N' = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    omega
  have hN' : IsPGroup 2 N' := hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hBN' : B' ≤ normalizer (N' : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hNH]
    exact fun b hb => hBN hb
  have hcube : ∀ b : H, b ∈ B' → b ^ 3 = 1 := fun b hb => Subtype.ext (by simpa using hB3 b hb)
  have hinj : ∀ b : H, b ∈ B' → Φ b = 1 → b = 1 := by
    intro b hb hΦ
    have h3 : (⟨b, hΦ⟩ : Φ.ker) ^ 3 = 1 := Subtype.ext (hcube b hb)
    have hd1 : orderOf (⟨b, hΦ⟩ : Φ.ker) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hd2 : orderOf (⟨b, hΦ⟩ : Φ.ker) ∣ Nat.card Φ.ker := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).1 hd1 with h1 | h1
    · exact congrArg (fun x : Φ.ker => (x : H)) (orderOf_eq_one_iff.1 h1)
    · have := Nat.le_of_dvd Nat.card_pos (h1 ▸ hd2)
      omega
  have hψ : Function.Injective (Φ.domRestrict B') := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact Subtype.ext (hinj b b.2 hb)
  have hEc : Nat.card (B'.map Φ) = 27 := by
    rw [← MonoidHom.domRestrict_range, ← hBc']
    exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
  have hE : Elem27 (B'.map Φ) := by
    refine ⟨?_, ?_, hEc⟩
    · rintro _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg Φ (Subtype.ext (hBcomm b₁ hb₁ b₂ hb₂))
    · rintro _ ⟨b₁, hb₁, rfl⟩
      rw [← map_pow, hcube b₁ hb₁, map_one]
  have hET : B'.map Φ ≤ normalizer ((N'.map Φ : Subgroup (Perm (Fin 11))) : Set (Perm (Fin 11))) :=
    (Subgroup.map_mono hBN').trans (Subgroup.le_normalizer_map Φ)
  have h16 := hE.card_le_sixteen (Fintype.card_fin 11) (hN'.map Φ) hET
  have hker' : Nat.card (Φ.domRestrict N').ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : (Φ.domRestrict N').ker => (⟨(x : N').1, x.2⟩ : Φ.ker)) ?_) hker
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun w : Φ.ker => (w : H)) hxy))
  have hcard := Subgroup.card_ker_mul_card_range (Φ.domRestrict N')
  rw [MonoidHom.domRestrict_range] at hcard
  have h32 : Nat.card N' ≤ 32 := by
    rw [← hcard]
    exact Nat.mul_le_mul hker' h16
  omega

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
