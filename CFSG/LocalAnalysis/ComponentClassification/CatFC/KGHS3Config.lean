module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3OddLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3HSData
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3L3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3L5
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3L11
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSCentralExt

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup Matrix CFSG.Blueprint.NativeSporadic

@[expose] def HSType (Y : Type) [Group Y] : Prop :=
  CFSG.IsQuasisimple Y ∧ IsSporadic (Y ⧸ center Y) .HS

theorem HSType.of_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y' ⧸ center Y' ≃* Y ⧸ center Y)
    (hq : CFSG.IsQuasisimple Y') (hY : HSType Y) : HSType Y' :=
  ⟨hq, by obtain ⟨f⟩ := hY.2; exact ⟨e.trans f⟩⟩


theorem HSType.center_sq {Y : Type} [Group Y] [Finite Y] (hY : HSType Y) :
    ∀ z ∈ center Y, z ^ 2 = 1 := by
  intro z hz
  by_cases hbot : center Y = ⊥
  · rw [hbot, Subgroup.mem_bot] at hz
    rw [hz]; simp
  · have hcard := EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot
      hY.1.1 hY.2 hbot
    have : (⟨z, hz⟩ : ↥(center Y)) ^ Nat.card ↥(center Y) = 1 := pow_card_eq_one'
    rw [hcard] at this
    exact congrArg Subtype.val this

theorem HSType.exists_C3 {Y : Type} [Group Y] [Finite Y] (hY : HSType Y) :
    ∃ a b g : Y, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ g * a * g⁻¹ = b ∧
      g * b * g⁻¹ = a * b := by
  obtain ⟨e⟩ := hY.2
  obtain ⟨a₀, b₀, g₀, ha, hb, hab, ha1, hga, hgb⟩ := hs_C3
  refine exists_C3_lift hY.center_sq (a := e.symm a₀) (b := e.symm b₀) (g := e.symm g₀) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, ha, map_one]
  · rw [← map_pow, hb, map_one]
  · rw [← map_mul, ← map_mul, hab]
  · intro h; apply ha1; simpa using congrArg e h
  · rw [← map_mul, ← map_inv, ← map_mul, hga]
  · rw [← map_mul, ← map_inv, ← map_mul, hgb, map_mul]

theorem HSType.exists_C5 {Y : Type} [Group Y] [Finite Y] (hY : HSType Y) :
    ∃ x y z g w : Y, z ^ 5 = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧ g * z * g⁻¹ = z ^ 2 ∧
      w * x = x * w ∧ w * y = y * w ∧ w * z = z * w ∧ w ^ 2 = 1 ∧ x * y * x⁻¹ * y⁻¹ = z * w := by
  obtain ⟨e⟩ := hY.2
  obtain ⟨x₀, y₀, z₀, g₀, hz, hz5, hz1, hxz, hyz, hgz⟩ := hs_C5
  refine exists_C5_lift hY.center_sq (x := e.symm x₀) (y := e.symm y₀) (z := e.symm z₀)
    (g := e.symm g₀) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hz]; simp
  · rw [← map_pow, hz5, map_one]
  · intro h; apply hz1; simpa using congrArg e h
  · rw [← map_mul, ← map_mul, hxz]
  · rw [← map_mul, ← map_mul, hyz]
  · rw [← map_mul, ← map_inv, ← map_mul, hgz, map_pow]

theorem HSType.exists_C11 {Y : Type} [Group Y] [Finite Y] (hY : HSType Y) :
    ∃ u h : Y, u ^ 11 = 1 ∧ u ≠ 1 ∧ h * u * h⁻¹ = u ^ 3 := by
  obtain ⟨e⟩ := hY.2
  obtain ⟨u₀, h₀, hu, hu1, hhu⟩ := hs_C11
  refine exists_C11_lift hY.center_sq (u := e.symm u₀) (h := e.symm h₀) ?_ ?_ ?_
  · rw [← map_pow, hu, map_one]
  · intro h; apply hu1; simpa using congrArg e h
  · rw [← map_mul, ← map_inv, ← map_mul, hhu, map_pow]

section Linear

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def matHom (Y : Subgroup (GL ι F)) : ↥Y →* Matrix ι ι F :=
  (Units.coeHom (Matrix ι ι F)).comp Y.subtype

theorem matHom_injective (Y : Subgroup (GL ι F)) : Function.Injective (matHom Y) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

theorem matHom_isUnit (Y : Subgroup (GL ι F)) (a : ↥Y) : IsUnit (matHom Y a) :=
  (a : GL ι F).isUnit

theorem matHom_ne_one (Y : Subgroup (GL ι F)) {a : ↥Y} (ha : a ≠ 1) : matHom Y a ≠ 1 := by
  intro h
  apply ha
  apply matHom_injective Y
  rw [h, map_one]

theorem hsType_eight_le_card (hF : ringChar F ≠ 3) (Y : Subgroup (GL ι F)) (hY : HSType ↥Y) :
    8 ≤ Fintype.card ι := by
  obtain ⟨a, b, g, ha, hb, hab, ha1, hga, hgb⟩ := hY.exists_C3
  refine eight_le_card_of_singer3 hF (matHom Y a) (matHom Y b) (matHom Y g) ?_ ?_ ?_
    (matHom_ne_one Y ha1) (matHom_isUnit Y g) ?_ ?_
  · simpa only [map_pow, map_one] using congrArg (matHom Y) ha
  · simpa only [map_pow, map_one] using congrArg (matHom Y) hb
  · simpa only [map_mul] using congrArg (matHom Y) hab
  · simpa only [map_mul] using congrArg (matHom Y) (mul_inv_eq_iff_eq_mul.mp hga)
  · simpa only [map_mul] using congrArg (matHom Y) (mul_inv_eq_iff_eq_mul.mp hgb)

theorem hsType_twenty_le_card (hF : ringChar F ≠ 5) (Y : Subgroup (GL ι F)) (hY : HSType ↥Y) :
    20 ≤ Fintype.card ι := by
  obtain ⟨x, y, z, g, w, hz5, hz1, hxz, hyz, hgz, hwx, hwy, hwz, hw2, hc⟩ := hY.exists_C5
  have hc' : x * y = z * w * (y * x) := by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = z * w * (y * x) := by rw [hc]
  refine twenty_le_card_of_heis5 hF (matHom Y x) (matHom Y y) (matHom Y z) (matHom Y g)
    (matHom Y w) ?_ (matHom_ne_one Y hz1) (matHom_isUnit Y x) (matHom_isUnit Y y)
    (matHom_isUnit Y g) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [map_pow, map_one] using congrArg (matHom Y) hz5
  · simpa only [map_mul] using congrArg (matHom Y) hxz
  · simpa only [map_mul] using congrArg (matHom Y) hyz
  · simpa only [map_mul, map_pow] using congrArg (matHom Y) (mul_inv_eq_iff_eq_mul.mp hgz)
  · simpa only [map_mul] using congrArg (matHom Y) hwx
  · simpa only [map_mul] using congrArg (matHom Y) hwy
  · simpa only [map_mul] using congrArg (matHom Y) hwz
  · simpa only [map_pow, map_one] using congrArg (matHom Y) hw2
  · simpa only [map_mul] using congrArg (matHom Y) hc'

theorem hsType_ten_le_card (hF : ringChar F ≠ 11) (Y : Subgroup (GL ι F)) (hY : HSType ↥Y)
    (Bm : Matrix ι ι F) (hBm : IsUnit Bm.det)
    (hB : ∀ s ∈ Y, ((s : GL ι F) : Matrix ι ι F)ᵀ * Bm * ((s : GL ι F) : Matrix ι ι F) = Bm) :
    10 ≤ Fintype.card ι := by
  obtain ⟨u, h, hu, hu1, hhu⟩ := hY.exists_C11
  refine ten_le_card_of_eleven_selfDual hF (matHom Y u) (matHom Y h) ?_ (matHom_ne_one Y hu1)
    (matHom_isUnit Y h) ?_ Bm hBm (hB (u : GL ι F) u.2)
  · simpa only [map_pow, map_one] using congrArg (matHom Y) hu
  · simpa only [map_mul, map_pow] using congrArg (matHom Y) (mul_inv_eq_iff_eq_mul.mp hhu)

theorem no_hsType_card_eq_eight (hF3 : ringChar F ≠ 3) (hcard : Fintype.card ι = 8)
    (Bm : Matrix ι ι F) (hBm : IsUnit Bm.det) (Y : Subgroup (GL ι F)) (hY : HSType ↥Y)
    (hB : ∀ s ∈ Y, ((s : GL ι F) : Matrix ι ι F)ᵀ * Bm * ((s : GL ι F) : Matrix ι ι F) = Bm) :
    False := by
  by_cases h5 : ringChar F = 5
  · have := hsType_ten_le_card (by omega) Y hY Bm hBm hB
    omega
  · have := hsType_twenty_le_card h5 Y hY
    omega

theorem no_hsType_card_lt_eight (hF3 : ringChar F ≠ 3) (hcard : Fintype.card ι < 8)
    (Y : Subgroup (GL ι F)) (hY : HSType ↥Y) : False := by
  have := hsType_eight_le_card hF3 Y hY
  omega

end Linear

theorem false_of_three_pow_five_dvd {S : Type} [Group S] [Finite S]
    (h3 : (Nat.card S).factorization 3 ≤ 4) (hd : 3 ^ 5 ∣ Nat.card S) : False := by
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hd
  omega

end CFSG.ComponentClassification.CatFC.KGHS3
