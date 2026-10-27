module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrMax
public import Certificates.Certificate26790

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem exists_sylow_of_data
    (ρ : D8 →* X) (hρinj : Function.Injective ρ) (Q : Subgroup X) {τ v x : X}
    (hρQ : ∀ a, ρ a ∈ Q)
    (hQ : ∀ y : X, (y * τ = τ * y ∧ y * v = v * y) ↔ y ∈ Q)
    (hτ : τ = ρ (DihedralGroup.r 2))
    (hx2 : x * x = 1) (hxτ : x * τ * x⁻¹ = v) (hxv : x * v * x⁻¹ = τ)
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hc : ∀ a b : D8, ρ a * (x * ρ b * x⁻¹) = (x * ρ b * x⁻¹) * ρ a)
    (hinf : ∀ a b : D8, ρ a = x * ρ b * x⁻¹ → ρ a = 1)
    (hdec : ∀ q ∈ Q, ∃ a b : D8, q = ρ a * (x * ρ b * x⁻¹))
    (hτvc : τ * v = v * τ) (hτ1 : τ ≠ 1) (hτv : τ ≠ v) (hv1 : v ≠ 1)
    (hnc : ¬ ∃ g : X, τ * v = g * τ * g⁻¹) :
    ∃ P : Sylow 2 X, Nonempty (↥P ≃* W8) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxn : ∀ a b : D8, x ≠ ρ a * (x * ρ b * x⁻¹) := by
    intro a b h
    have hxQ' : x ∈ Q := by
      rw [h]; exact Q.mul_mem (hρQ a) (hxQ _ (hρQ b))
    have h1 := ((hQ x).2 hxQ').1
    have h2 : x * τ * x⁻¹ = τ := by
      calc x * τ * x⁻¹ = τ * x * x⁻¹ := by rw [h1]
        _ = τ := by group
    exact hτv (h2.symm.trans hxτ)
  set Φ := wrHom ρ x hx2 hc with hΦdef
  have hΦ : ∀ w, Φ w = wrMap ρ x w := fun w => rfl
  have hΦinj : Function.Injective Φ := wrHom_injective ρ x hx2 hc hρinj hinf hxn
  set P : Subgroup X := Φ.range with hPdef
  have hΦmk : ∀ a b : D8, Φ ⟨fun r => if r = 1 then a else b, 1⟩ = ρ a * (x * ρ b * x⁻¹) := by
    intro a b; rw [hΦ, wrMap_mk]; simp
  have hΦmk' : ∀ a b : D8,
      Φ ⟨fun r => if r = 1 then a else b, eps⟩ = ρ a * (x * ρ b * x⁻¹) * x := by
    intro a b; rw [hΦ, wrMap_mk]; simp [eps_ne_one]
  have hQP : Q ≤ P := by
    intro q hq
    obtain ⟨a, b, rfl⟩ := hdec q hq
    exact ⟨_, hΦmk a b⟩
  have hxP : x ∈ P := by
    refine ⟨⟨fun r => if r = 1 then 1 else 1, eps⟩, ?_⟩
    rw [hΦmk']; simp
  have hcardP : Nat.card P = 2 ^ 7 := by
    have h1 : Nat.card P = Nat.card W8 :=
      (Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv).symm
    rw [h1, RegularWreathProduct.card, DihedralGroup.nat_card]
    simp
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hcardP
  have hVfwd : ∀ w : W8, (∃ a'' : W8, ∀ p : W8, p * w * p⁻¹ = w ∨ p * w * p⁻¹ = a'') →
      ∃ a ∈ P, ∀ p ∈ P, p * Φ w * p⁻¹ = Φ w ∨ p * Φ w * p⁻¹ = a := by
    rintro w ⟨a'', ha''⟩
    refine ⟨Φ a'', ⟨a'', rfl⟩, ?_⟩
    rintro _ ⟨p, rfl⟩
    rcases ha'' p with h | h
    · left; rw [← map_inv Φ p, ← map_mul, ← map_mul, h]
    · right; rw [← map_inv Φ p, ← map_mul, ← map_mul, h]
  have hVbwd : ∀ w : W8, (∃ a ∈ P, ∀ p ∈ P, p * Φ w * p⁻¹ = Φ w ∨ p * Φ w * p⁻¹ = a) →
      ∃ a'' : W8, ∀ p : W8, p * w * p⁻¹ = w ∨ p * w * p⁻¹ = a'' := by
    rintro w ⟨_, ⟨a'', rfl⟩, ha⟩
    refine ⟨a'', fun p => ?_⟩
    rcases ha (Φ p) ⟨p, rfl⟩ with h | h
    · left; apply hΦinj; rw [map_mul, map_mul, map_inv]; exact h
    · right; apply hΦinj; rw [map_mul, map_mul, map_inv]; exact h
  have hρ1 : ρ 1 = 1 := map_one ρ
  have e11 : ρ 1 * (x * ρ 1 * x⁻¹) = 1 := by simp [hρ1]
  have e12 : ρ 1 * (x * ρ (DihedralGroup.r 2) * x⁻¹) = v := by
    rw [hρ1, one_mul, ← hτ, hxτ]
  have e21 : ρ (DihedralGroup.r 2) * (x * ρ 1 * x⁻¹) = τ := by
    rw [hρ1]; simp [hτ]
  have e22 : ρ (DihedralGroup.r 2) * (x * ρ (DihedralGroup.r 2) * x⁻¹) = τ * v := by
    rw [← hτ, hxτ]
  have hV : ∀ z ∈ P, (∃ a ∈ P, ∀ p ∈ P, p * z * p⁻¹ = z ∨ p * z * p⁻¹ = a) ↔
      (z = 1 ∨ z = τ ∨ z = v ∨ z = τ * v) := by
    rintro _ ⟨w, rfl⟩
    have hW := Certificates.certificate26790 w
    constructor
    · intro h
      obtain ⟨hr, hl⟩ := hW.1 (hVbwd w h)
      obtain ⟨f, p⟩ := w
      have hr' : p = 1 := hr
      subst hr'
      have hl' : ∀ q, f q = 1 ∨ f q = DihedralGroup.r 2 := hl
      rw [hΦ]
      simp only [wrMap, ↓reduceIte, mul_one]
      rcases hl' 1 with h1 | h1 <;> rcases hl' eps with h2 | h2 <;> rw [h1, h2]
      · exact Or.inl e11
      · exact Or.inr (Or.inr (Or.inl e12))
      · exact Or.inr (Or.inl e21)
      · exact Or.inr (Or.inr (Or.inr e22))
    · intro h
      have key : ∀ c₁ c₂ : D8, (c₁ = 1 ∨ c₁ = DihedralGroup.r 2) →
          (c₂ = 1 ∨ c₂ = DihedralGroup.r 2) → Φ w = ρ c₁ * (x * ρ c₂ * x⁻¹) →
          ∃ a ∈ P, ∀ p ∈ P, p * Φ w * p⁻¹ = Φ w ∨ p * Φ w * p⁻¹ = a := by
        intro c₁ c₂ h1 h2 h3
        have hw : w = ⟨fun r => if r = 1 then c₁ else c₂, 1⟩ := hΦinj (by rw [h3, hΦmk])
        subst hw
        apply hVfwd
        apply hW.2
        refine ⟨rfl, fun q => ?_⟩
        rcases eq_one_or_eps q with rfl | rfl
        · simpa using h1
        · simpa [eps_ne_one] using h2
      rcases h with h | h | h | h
      · exact key 1 1 (Or.inl rfl) (Or.inl rfl) (by rw [h, e11])
      · exact key (DihedralGroup.r 2) 1 (Or.inr rfl) (Or.inl rfl) (by rw [h, e21])
      · exact key 1 (DihedralGroup.r 2) (Or.inl rfl) (Or.inr rfl) (by rw [h, e12])
      · exact key (DihedralGroup.r 2) (DihedralGroup.r 2) (Or.inr rfl) (Or.inr rfl)
          (by rw [h, e22])
  obtain ⟨R, hPR⟩ := hP2.exists_le_sylow
  have hRP : (R : Subgroup X) ≤ P :=
    le_of_isPGroup P Q hQP hQ hτvc hxP hxτ hxv hτ1 hτv hv1 hnc hV R R.isPGroup' hPR
  have heq : (R : Subgroup X) = P := le_antisymm hRP hPR
  exact ⟨R, ⟨(MulEquiv.subgroupCongr heq).trans (MonoidHom.ofInjective hΦinj).symm⟩⟩

end CFSG.EvenSporadicStandard.TwoHS
