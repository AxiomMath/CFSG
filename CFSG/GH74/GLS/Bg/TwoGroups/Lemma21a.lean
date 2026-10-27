module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Dict
public import CFSG.GH74.GLS.Bg.TwoGroups.A44Facts

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

namespace A44

theorem val_sq (x : G96) : (x ^ 2).1 = M4.sq x.1 := by
  rw [pow_two]; rfl

theorem val_pow32 (x : G96) : (x ^ 32).1 = M4.pow32 x.1 := by
  have : x ^ 32 = ((((x ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    simp only [← pow_mul]
  rw [this, val_sq, val_sq, val_sq, val_sq, val_sq]
  rfl

theorem pow32_of_pGroup {A : Type*} [Group A] (hA : Nat.card A = 96) (N : Subgroup A)
    (hN : IsPGroup 2 N) {y : A} (hy : y ∈ N) : y ^ 32 = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨y, hy⟩
  have h0 : y ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h0
  have h2 : orderOf y ∣ 96 := hA ▸ orderOf_dvd_natCard y
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hj] at h2
  have hk5 : j ≤ 5 := by
    by_contra hlt
    have h6 : 6 ≤ j := by omega
    have h7 : 2 ^ 6 ∣ 2 ^ j := Nat.pow_dvd_pow 2 h6
    have := dvd_trans h7 h2
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact Nat.pow_dvd_pow 2 hk5

theorem pow32_eq_one_iff {x : G96} : x ^ 32 = 1 ↔ M4.pow32 x.1 = M4.one := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [val_pow32, G96.val_one] at this
  · intro h
    apply Subtype.ext
    rw [val_pow32, G96.val_one]
    exact h

end A44

open A44

theorem iv2_2_1_order : IV2_2_1_order := by
  intro B _ ⟨e⟩
  rw [Nat.card_congr (phiB e).toEquiv, Nat.card_eq_fintype_card]
  exact M4.card_G96

theorem card_A0_eq {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : Nat.card (A0 B) = 16 := by
  have hA0 : ∀ φ : MulAut B, φ ∈ A0 B ↔ (phiB e φ).1.IsA0 := fun φ => by
    rw [mem_A0_iff e, M4.isA0_iff]
  rw [Nat.card_congr ((phiB e).toEquiv.subtypeEquiv (q := fun x : G96 => x.1.IsA0) hA0),
    Nat.card_eq_fintype_card]
  exact M4.card_A0

theorem iv2_2_1_a : IV2_2_1_a := by
  intro B _ ⟨e⟩
  have hA0 : ∀ φ : MulAut B, φ ∈ A0 B ↔ (phiB e φ).1.IsA0 := fun φ => by
    rw [mem_A0_iff e, M4.isA0_iff]
  have hcard := card_A0_eq e
  have hcardA : Nat.card (MulAut B) = 96 := iv2_2_1_order B ⟨e⟩
  refine ⟨?_, ?_, hcard⟩
  ·
    apply le_antisymm
    · have hnorm : (⊤ : Subgroup (MulAut B)) ≤
          normalizer ((A0 B : Subgroup (MulAut B)) : Set (MulAut B)) := by
        intro g _
        rw [mem_normalizer_iff]
        have fwd : ∀ g : MulAut B, ∀ h ∈ A0 B, g * h * g⁻¹ ∈ A0 B := by
          intro g h hh
          rw [hA0] at hh ⊢
          have := M4.A0_normal (phiB e g).1 (phiB e h).1 (phiB e g).2 hh
          rw [map_mul, map_mul, map_inv]
          exact this
        intro h
        constructor
        · exact fun hh => fwd g h hh
        · intro hh
          have := fwd g⁻¹ _ hh
          simpa [mul_assoc] using this
      have hp : IsPGroup 2 (A0 B) := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
      exact le_iSup (fun N : {N : Subgroup (MulAut B) // N ≤ ⊤ ∧
        ⊤ ≤ normalizer (N : Set (MulAut B)) ∧ IsPGroup 2 N} => N.1) ⟨A0 B, le_top, hnorm, hp⟩
    · apply iSup_le
      rintro ⟨N, -, hnorm, hp⟩
      intro g hg
      rw [hA0]
      by_contra hne
      have hnorm' : ∀ g' : MulAut B, ∀ h, h ∈ N ↔ g' * h * g'⁻¹ ∈ N :=
        fun g' => mem_normalizer_iff.mp (hnorm (mem_top g'))
      rcases M4.not_two_group (phiB e g).1 (phiB e g).2 hne with h1 | ⟨h, hh, h2⟩
      · apply h1
        have h3 : (phiB e g) ^ 32 = 1 := by
          rw [← map_pow, pow32_of_pGroup hcardA N hp hg, map_one]
        exact pow32_eq_one_iff.mp h3
      · apply h2
        have hΦ : phiB e ((phiB e).symm ⟨h, hh⟩) = ⟨h, hh⟩ := (phiB e).apply_symm_apply _
        have hconj : (phiB e).symm ⟨h, hh⟩ * g * ((phiB e).symm ⟨h, hh⟩)⁻¹ ∈ N :=
          (hnorm' _ g).mp hg
        have hprod : g * ((phiB e).symm ⟨h, hh⟩ * g * ((phiB e).symm ⟨h, hh⟩)⁻¹) ∈ N :=
          mul_mem hg hconj
        have h3 : (phiB e (g * ((phiB e).symm ⟨h, hh⟩ * g * ((phiB e).symm ⟨h, hh⟩)⁻¹))) ^ 32 = 1 := by
          rw [← map_pow, pow32_of_pGroup hcardA N hp hprod, map_one]
        have h4 := pow32_eq_one_iff.mp h3
        rw [map_mul, map_mul, map_mul, map_inv, hΦ] at h4
        exact h4
  · constructor
    · intro a ha b hb
      apply (phiB e).injective
      apply Subtype.ext
      rw [map_mul, map_mul, G96.val_mul, G96.val_mul]
      exact M4.A0_comm _ _ ((hA0 a).mp ha) ((hA0 b).mp hb)
    · intro a ha
      apply (phiB e).injective
      apply Subtype.ext
      rw [map_pow, map_one, pow_two, G96.val_mul, G96.val_one]
      exact M4.A0_sq _ ((hA0 a).mp ha)

end CFSG.GH74.GLS.Bg.TwoGroups
