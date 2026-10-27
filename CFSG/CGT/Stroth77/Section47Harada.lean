module

public import CFSG.CGT.Stroth77.Section42Core
public import CFSG.CGT.Stroth77.Section42Fusion

public section

namespace CFSG.CGT.Stroth77.Stroth47

open Stroth42Core

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_iff_of_mul_self_mem {U : Subgroup G} {f : G}
    (hf : f ∈ Subgroup.normalizer (U : Set G)) (hf2 : f * f ∈ U) {y : G} :
    y ∈ U ⊔ Subgroup.zpowers f ↔ ∃ w ∈ U, ∃ k : Bool, y = w * bpow f k := by
  have hle : Subgroup.zpowers f ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le).mpr hf
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle, Set.mem_mul]
  constructor
  · rintro ⟨w, hw, z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hn : n = 2 * (n / 2) + n % 2 := by omega
    have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hsplit : f ^ n = (f * f) ^ (n / 2) * bpow f (decide (n % 2 = 1)) := by
      conv_lhs => rw [hn]
      rw [zpow_add, zpow_mul, zpow_two]
      rcases hr with h | h <;> simp [h, bpow]
    refine ⟨w * (f * f) ^ (n / 2), U.mul_mem hw (U.zpow_mem hf2 _), decide (n % 2 = 1), ?_⟩
    rw [hsplit, mul_assoc]
  · rintro ⟨w, hw, k, rfl⟩
    refine ⟨w, hw, bpow f k, ?_, rfl⟩
    cases k
    · exact one_mem _
    · exact Subgroup.mem_zpowers f

theorem relIndex_sup_zpowers_of_mul_self_mem {U : Subgroup G} {f : G}
    (hf : f ∈ Subgroup.normalizer (U : Set G)) (hf2 : f * f ∈ U) (hfU : f ∉ U) :
    U.relIndex (U ⊔ Subgroup.zpowers f) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨f, Subgroup.mem_sup_right (Subgroup.mem_zpowers f), fun y hy => ?_⟩
  obtain ⟨w, hw, k, rfl⟩ := (mem_sup_zpowers_iff_of_mul_self_mem hf hf2).mp hy
  have hnot : w * f ∉ U := fun h => hfU (by simpa using U.mul_mem (U.inv_mem hw) h)
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
    exact Or.inr ⟨hw, hnot⟩
  · simp only [bpow, ↓reduceIte]
    exact Or.inl ⟨by rw [mul_assoc]; exact U.mul_mem hw hf2, hnot⟩

theorem conj_mul_inv_mem {D U : Subgroup G} {g : G} (hgD : g ∈ Subgroup.normalizer (D : Set G))
    (hUD : U ≤ Subgroup.normalizer (D : Set G)) {s : Set G}
    (hU : U = D ⊔ Subgroup.closure s) (hs : ∀ x ∈ s, g⁻¹ * x * g * x⁻¹ ∈ D) :
    ∀ x ∈ U, g⁻¹ * x * g * x⁻¹ ∈ D := by
  have hcl : U = Subgroup.closure ((D : Set G) ∪ s) := by
    rw [hU, Subgroup.closure_union, Subgroup.closure_eq]
  have hN : ∀ y ∈ Subgroup.closure ((D : Set G) ∪ s), y ∈ Subgroup.normalizer (D : Set G) :=
    fun y hy => hUD (hcl ▸ hy)
  intro x hx
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · have h1 : g⁻¹ * x * g ∈ D := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgD) x).mp hx
        rwa [inv_inv] at this
      exact D.mul_mem h1 (D.inv_mem hx)
    · exact hs x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have h1 : x * (g⁻¹ * y * g * y⁻¹) * x⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hN x hx) _).mp ihy
    have h2 := D.mul_mem ihx h1
    rwa [show g⁻¹ * x * g * x⁻¹ * (x * (g⁻¹ * y * g * y⁻¹) * x⁻¹) =
      g⁻¹ * (x * y) * g * (x * y)⁻¹ by group] at h2
  | inv x hx ih =>
    have h1 : x⁻¹ * (g⁻¹ * x * g * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN x hx)) _).mp (D.inv_mem ih)
    rwa [show x⁻¹ * (g⁻¹ * x * g * x⁻¹)⁻¹ * x⁻¹⁻¹ = g⁻¹ * x⁻¹ * g * x⁻¹⁻¹ by group] at h1

variable [Finite G]

theorem false_of_harada_four [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) {D U P : Subgroup G} {x z : G} {j : ℕ} (hUS : U ≤ S) (hU : U.relIndex S = 2)
    (hPU : P ≤ U) (hxS : x ∈ S) (hxU : x ∉ U) (hj : 2 ≤ j) (hxz : x ^ 2 ^ j = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (h4 : ∀ y ∈ U, y * z = z * y → y ^ 2 ^ j ≠ z)
    (h5 : ∀ y ∈ (S : Subgroup G), y ^ 4 ∈ D)
    (h6 : ∀ y ∈ (S : Subgroup G), y ∉ U → y ^ 4 ≠ 1)
    (h8 : ∀ y ∈ (S : Subgroup G), y ∉ U → ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = z → y ^ 2 ^ j ≠ 1) :
    False := by
  have hpowD : ∀ y ∈ (S : Subgroup G), ∀ l : ℕ, 2 ≤ l → y ^ 2 ^ l ∈ D := by
    intro y hy l hl
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hl
    rw [show 2 ^ (l + 2) = 4 * 2 ^ l by ring, pow_mul]
    exact D.pow_mem (h5 y hy) _
  have hconj : ∀ g : G, g⁻¹ * x * g ∉ U := by
    intro g hyU
    have hrz : IsConj ((g⁻¹ * x * g) ^ 2 ^ j) z := by
      rw [Stroth42.conj_pow', hxz]; exact Stroth42.isConj_of_conj_eq rfl
    obtain ⟨p, hpU, hp⟩ :=
      Stroth42.exists_conj_pow_eq hPU hz2 hz1 h3 (hpowD _ (hUS hyU) j hj) hrz
    have hy'U : p⁻¹ * (g⁻¹ * x * g) * p ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hpU) hyU) hpU
    refine h4 _ hy'U ?_ hp
    rw [← hp]
    exact ((Commute.refl _).pow_right _).eq
  refine EvenSporadicStandard.TwoHS.false_of_thompson_pow hnonab S.isPGroup' S.not_dvd_index hUS
    hU hxS hxU (fun g k hgS => ?_) hconj
  by_contra hgU
  set y := g⁻¹ * x ^ (2 * k) * g with hy
  have hk : x ^ (2 * k) ≠ 1 := by
    rintro h1; apply hgU; rw [hy, h1]; simp
  obtain ⟨l, hlj, hl, hlj'⟩ := Stroth42.exists_pow_eq_of_even hxz hz2 hz1 hk
  have hrz : IsConj (y ^ 2 ^ l) z := by
    rw [hy, Stroth42.conj_pow', hl]; exact Stroth42.isConj_of_conj_eq rfl
  have h22 := Stroth42.mul_self_eq_one_of_isConj hrz hz2
  rcases (show l = 0 ∨ l = 1 ∨ 2 ≤ l by omega) with rfl | rfl | hl2
  · apply h6 y hgS hgU
    rw [pow_zero, pow_one] at h22
    rw [show y ^ 4 = y * y * (y * y) by rw [← sq, ← sq, ← pow_mul], h22, one_mul]
  · apply h6 y hgS hgU
    rw [pow_one] at h22
    rw [show y ^ 4 = y ^ 2 * y ^ 2 by rw [← pow_add]]
    exact h22
  · obtain ⟨p, hpU, hp⟩ := Stroth42.exists_conj_pow_eq hPU hz2 hz1 h3 (hpowD y hgS l hl2) hrz
    have hy'S : p⁻¹ * y * p ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hUS hpU)) hgS)
        (hUS hpU)
    have hy'U : p⁻¹ * y * p ∉ U := fun h' => hgU (by
      have := U.mul_mem (U.mul_mem hpU h') (U.inv_mem hpU)
      rwa [show p * (p⁻¹ * y * p) * p⁻¹ = y by group] at this)
    exact h8 _ hy'S hy'U l (by omega) hp
      (by rw [Stroth42.conj_pow', hy, Stroth42.conj_pow', hlj']; group)

end CFSG.CGT.Stroth77.Stroth47
