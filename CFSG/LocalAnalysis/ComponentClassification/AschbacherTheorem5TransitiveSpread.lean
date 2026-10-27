module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {X : Type} [Group X] [Finite X]

theorem Spread.mem_mul_of_card {V A B : Subgroup X} (hAV : A ≤ V) (hBV : B ≤ V)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card A * Nat.card B = Nat.card V) {v : X} (hv : v ∈ V) :
    ∃ a ∈ A, ∃ b ∈ B, v = a * b := by
  have hBN : B ≤ Subgroup.normalizer (A : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hsup : A ⊔ B = V := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hAV hBV)
    rw [AschbacherTheorem3.card_sup_of_le_normalizer hBN hAB, hcard]
  have hmem : v ∈ ((A ⊔ B : Subgroup X) : Set X) := hsup ▸ hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBN] at hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hmem
  exact ⟨a, ha, b, hb, rfl⟩

theorem Spread.mem_spread {V U P T : Subgroup X} {Y : Set X} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hUV : U ≤ V) (hPV : P ≤ V) (hTV : T ≤ V)
    (hU : Nat.card U * Nat.card P = Nat.card V) (hT : Nat.card T * Nat.card P = Nat.card V)
    (hUP : U ⊓ P = ⊥) (hTU : T ⊓ U = ⊥) (hTP : T ⊓ P = ⊥)
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ = u)
    (htrans : ∀ p ∈ P, ∀ p' ∈ P, p ≠ 1 → p' ≠ 1 → ∃ y ∈ Y, y * p * y⁻¹ = p')
    {v : X} (hv : v ∈ V) : v ∈ U ∨ v ∈ P ∨ ∃ y ∈ Y, ∃ t ∈ T, v = y * t * y⁻¹ := by
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ V, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_left (by
    rw [← pow_two]; exact hV.2 a ha)
  obtain ⟨u, hu, p, hp, rfl⟩ := Spread.mem_mul_of_card hUV hPV
    (fun a ha b hb => hcommV a (hUV ha) b (hPV hb)) hUP hU hv
  by_cases hp1 : p = 1
  · left
    rw [hp1, mul_one]
    exact hu
  by_cases hu1 : u = 1
  · right; left
    rw [hu1, one_mul]
    exact hp
  right; right
  obtain ⟨t, ht, p₀, hp₀, hutp⟩ := Spread.mem_mul_of_card hTV hPV
    (fun a ha b hb => hcommV a (hTV ha) b (hPV hb)) hTP hT (hUV hu)
  have hp₀1 : p₀ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hutp
    have hmem : u ∈ T ⊓ U := ⟨hutp ▸ ht, hu⟩
    rw [hTU, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  obtain ⟨y, hy, hyp⟩ := htrans p₀ hp₀ p hp hp₀1 hp1
  refine ⟨y, hy, t, ht, ?_⟩
  have htup : t = u * p₀ := by
    calc t = t * p₀ * p₀⁻¹ := by group
      _ = u * p₀ := by rw [← hutp, hsq p₀ (hPV hp₀)]
  rw [htup]
  calc u * p = (y * u * y⁻¹) * (y * p₀ * y⁻¹) := by rw [hYU y hy u hu, hyp]
    _ = y * (u * p₀) * y⁻¹ := by group

theorem spread_exclusion {V U P T R : Subgroup X} {Y : Set X} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hUV : U ≤ V) (hPV : P ≤ V) (hTV : T ≤ V)
    (hU : Nat.card U * Nat.card P = Nat.card V) (hT : Nat.card T * Nat.card P = Nat.card V)
    (hUP : U ⊓ P = ⊥) (hTU : T ⊓ U = ⊥) (hTP : T ⊓ P = ⊥)
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ = u)
    (htrans : ∀ p ∈ P, ∀ p' ∈ P, p ≠ 1 → p' ≠ 1 → ∃ y ∈ Y, y * p * y⁻¹ = p')
    (hRV : R ≤ V) (hRU : R ⊓ U = ⊥) (hRP : R ⊓ P = ⊥)
    (hRT : ∀ y ∈ Y, ∀ t ∈ T, y * t * y⁻¹ ∈ R → y * t * y⁻¹ = 1) : R = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  rcases Spread.mem_spread hV hUV hPV hTV hU hT hUP hTU hTP hYU htrans (hRV hv) with
    h | h | ⟨y, hy, t, ht, rfl⟩
  · have hmem : v ∈ R ⊓ U := ⟨hv, h⟩
    rwa [hRU, Subgroup.mem_bot] at hmem
  · have hmem : v ∈ R ⊓ P := ⟨hv, h⟩
    rwa [hRP, Subgroup.mem_bot] at hmem
  · exact hRT y hy t ht hv

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
