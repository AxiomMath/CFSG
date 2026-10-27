module

public import CFSG.RankThree.PartOne.K133.SimpleSL2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup

theorem eq_of_card_eq_two {B : Type*} [Group B] (h2 : Nat.card B = 2) {c d : B} (hc : c ≠ 1)
    (hd : d ≠ 1) : c = d := by
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp h2
  have h1 : (1 : B) ∈ ({x, y} : Set B) := huniv ▸ Set.mem_univ _
  have hc' : c ∈ ({x, y} : Set B) := huniv ▸ Set.mem_univ _
  have hd' : d ∈ ({x, y} : Set B) := huniv ▸ Set.mem_univ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 hc' hd'
  rcases h1 with h1 | h1 <;> rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl <;>
    simp_all

theorem sl2_sq_eq_one_mem_center {A F : Type} [Group A] [Field F] [Fintype F]
    (hF : Odd (Fintype.card F)) (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F) {c : A}
    (hc : c ^ 2 = 1) : c ∈ center A := by
  have h2 : (2 : F) ≠ 0 := by
    refine Ring.two_ne_zero fun h => ?_
    have := FiniteField.even_card_iff_char_two.mp h
    rw [Nat.odd_iff] at hF
    omega
  have hm := RankThree.PartOne.K133.sl2_involution_mem_center h2 (e c) (by rw [← map_pow, hc,
    map_one])
  rw [mem_center_iff] at hm ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact hm (e g)

theorem false_of_commute_lifts {A H : Type} [Group A] [Group H] (hZ : Nat.card (center A) = 2)
    (hinv : ∀ c : A, c ^ 2 = 1 → c ∈ center A) (ψ : A →* H)
    (hker : ∀ c, c ∈ center A ↔ ψ c = 1) {a b : A}
    (ha2 : ψ a * ψ a = 1) (hb2 : ψ b * ψ b = 1) (ha1 : ψ a ≠ 1) (hb1 : ψ b ≠ 1)
    (hab : ψ a ≠ ψ b) (hcomm : a * b = b * a) : False := by
  have ha2' : a ^ 2 ∈ center A := (hker _).2 (by rw [map_pow, pow_two, ha2])
  have hb2' : b ^ 2 ∈ center A := (hker _).2 (by rw [map_pow, pow_two, hb2])
  have ha2ne : a ^ 2 ≠ 1 := fun h1 => ha1 ((hker a).1 (hinv a h1))
  have hb2ne : b ^ 2 ≠ 1 := fun h1 => hb1 ((hker b).1 (hinv b h1))
  have hsame : a ^ 2 = b ^ 2 := by
    have := eq_of_card_eq_two hZ (c := ⟨a ^ 2, ha2'⟩) (d := ⟨b ^ 2, hb2'⟩)
      (fun h => ha2ne (congrArg Subtype.val h)) (fun h => hb2ne (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  have hsq : (a ^ 2) ^ 2 = 1 := by
    have : Finite (center A) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    have h1 : (⟨a ^ 2, ha2'⟩ : center A) ^ Nat.card (center A) = 1 := pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hab2 : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
          rw [pow_two, pow_two, pow_two]
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hcomm]
            _ = a * a * (b * b) := by group
      _ = (a ^ 2) ^ 2 := by rw [← hsame, pow_two (a ^ 2)]
      _ = 1 := hsq
  have h1 : ψ (a * b) = 1 := (hker _).1 (hinv _ hab2)
  rw [map_mul] at h1
  apply hab
  calc ψ a = ψ a * (ψ b * ψ b) := by rw [hb2, mul_one]
    _ = (ψ a * ψ b) * ψ b := by group
    _ = ψ b := by rw [h1, one_mul]

end CFSG.ComponentClassification.HarrisLit.L35
