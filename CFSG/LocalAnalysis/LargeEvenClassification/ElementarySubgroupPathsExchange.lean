module

public import CFSG.LocalAnalysis.LargeEvenClassification.ElementarySubgroupPathsCore

public section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open

universe u

theorem elementary_path_hyperplane {D : Type u} [CommGroup D] [Finite D]
    {p k d : ℕ} (hprime : p.Prime)
    (X J : Subgroup D) (hXcard : Nat.card X = p ^ k)
    (hJcard : Nat.card J = p ^ d) (hJX : J ≤ X) (hdk : d < k) :
    ∃ H : Subgroup D, J ≤ H ∧ H ≤ X ∧ Nat.card H = p ^ (k - 1) := by
  have hdivSmall : Nat.card J ∣ p ^ (k - 1) := by
    rw [hJcard]
    exact Nat.pow_dvd_pow p (by omega)
  have hdivLarge : p ^ (k - 1) ∣ Nat.card X := by
    rw [hXcard]
    exact Nat.pow_dvd_pow p (by omega)
  obtain ⟨H, hHcard, hJH, hHX⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hprime hdivSmall hdivLarge hJX
  exact ⟨H, hJH, hHX, hHcard⟩

theorem elementary_path_exchange {D : Type u} [CommGroup D] [Finite D]
    {p k d : ℕ} (hprime : p.Prime) (hD : ∀ x : D, x ^ p = 1)
    (X Y : Subgroup D) (hXcard : Nat.card X = p ^ k)
    (hYcard : Nat.card Y = p ^ k) (hJcard : Nat.card (X ⊓ Y : Subgroup D) = p ^ d)
    (hdk : d < k) :
    ∃ X₁ : Subgroup D, ∃ d₁ : ℕ,
      Nat.card X₁ = p ^ k ∧ Nat.card (X ⊓ X₁ : Subgroup D) = p ^ (k - 1) ∧
      Nat.card (X₁ ⊓ Y : Subgroup D) = p ^ d₁ ∧ d + 1 ≤ d₁ ∧ d₁ ≤ k := by
  let : Fact p.Prime := ⟨hprime⟩
  let J := X ⊓ Y
  obtain ⟨H, hJH, hHX, hHcard⟩ :=
    elementary_path_hyperplane hprime X J hXcard hJcard inf_le_left hdk
  have hnotYX : ¬ Y ≤ X := by
    intro hYX
    have heq : p ^ d = p ^ k := by
      rw [← hJcard, inf_eq_right.mpr hYX, hYcard]
    have := Nat.pow_right_injective hprime.two_le heq
    omega
  obtain ⟨y, hyY, hyX⟩ := IsConcreteLE.not_le_iff_exists.mp hnotYX
  have hyOne : y ≠ 1 := by intro h; exact hyX (h ▸ X.one_mem)
  have hyOrder : orderOf y = p := orderOf_eq_prime (hD y) hyOne
  let T := Subgroup.zpowers y
  have hTcard : Nat.card T = p ^ 1 := by rw [Nat.card_zpowers, hyOrder, pow_one]
  have hTY : T ≤ Y := Subgroup.zpowers_le.mpr hyY
  have hdisjointX : Disjoint X T := elementary_path_zpowers_disjoint hprime X y hyOrder hyX
  have hdisjointH : Disjoint H T := hdisjointX.mono_left hHX
  have hdisjointJ : Disjoint J T := hdisjointX.mono_left inf_le_left
  let X₁ := H ⊔ T
  have hX₁card : Nat.card X₁ = p ^ k := by
    have hcard := elementary_path_disjoint_sup_card H T hHcard hTcard hdisjointH
    have hpositive : 1 ≤ k := by omega
    simpa only [Nat.sub_add_cancel hpositive] using hcard
  have hXinf : X ⊓ X₁ = H := by
    rw [elementary_path_inf_sup_of_le X H T hHX,
      disjoint_iff.mp hdisjointX, sup_bot_eq]
  have hJplus : Nat.card (J ⊔ T : Subgroup D) = p ^ (d + 1) :=
    elementary_path_disjoint_sup_card J T hJcard hTcard hdisjointJ
  have hJplusLe : J ⊔ T ≤ X₁ ⊓ Y :=
    le_inf (sup_le (hJH.trans le_sup_left) le_sup_right) (sup_le inf_le_right hTY)
  have hgroup : IsPGroup p D := isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by
    simpa only [pow_one] using hD x⟩)
  obtain ⟨d₁, hd₁card⟩ := (hgroup.to_subgroup (X₁ ⊓ Y)).exists_card_eq
  have hlow : d + 1 ≤ d₁ := by
    apply (Nat.pow_le_pow_iff_right hprime.one_lt).mp
    rw [← hJplus, ← hd₁card]
    exact Subgroup.card_le_of_le hJplusLe
  have hupp : d₁ ≤ k := by
    apply (Nat.pow_le_pow_iff_right hprime.one_lt).mp
    rw [← hd₁card, ← hYcard]
    exact Subgroup.card_le_of_le inf_le_right
  exact ⟨X₁, d₁, hX₁card, hXinf ▸ hHcard, hd₁card, hlow, hupp⟩

end CFSG.LargeEvenClassification.Helpers
