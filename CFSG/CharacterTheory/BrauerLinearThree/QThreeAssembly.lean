module

public import CFSG.CharacterTheory.BrauerLinearThree.SixA
public import CFSG.CharacterTheory.BrauerLinearThree.LayerCube
public import CFSG.CharacterTheory.BrauerLinearThree.LocalRecognition

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem card_centralizer_conditions_of_card
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) :
    ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
      Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
          Nat.card F ^ 3 * (Nat.card F - 1) ∧
        ((∀ g : G, g * Q * g⁻¹ ∉ rootX₁ φ) →
          Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3) :=
  card_centralizer_of_six_A φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard
    (not_dvd_card_centralizer_of_dvd_add_one φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard)

include φ hZ hZodd h2 hJ in
theorem statedClassicalModel_of_cube_dvd
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hcube : Nat.card F ^ 3 ∣ Nat.card G) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hcard := card_mul_eq_of_cube_dvd φ hZ hZodd h2 hJ hnonab hq (by omega) p f hp hf hF hcube
  exact statedClassicalModel_of_local φ hZ hZodd h2 hJ hcard
    (card_centralizer_conditions_of_card φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hcard)
    hnonab p f hp hf hF

include φ hZ hZodd h2 hJ in
theorem statedClassicalModel_of_u_ne_one
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hu : Nat.card F - 1 ≠ 2 * Nat.card Z) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f :=
  statedClassicalModel_of_cube_dvd φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF
    (cube_dvd_card_of_u_ne_one φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hu)

omit [Field F] [Finite F] in
theorem two_ne_zero_of_card_eq [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) : (2 : F) ≠ 0 := by
  intro h
  let : Fintype F := Fintype.ofFinite F
  have hc : ((Nat.card F : ℕ) : F) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  rw [hF, hk] at hc
  push_cast at hc
  rw [h] at hc
  simp at hc

theorem brauer_linear_three_involution_centralizer_q3mod4_of_u_eq_one
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 4 = 3 ∧ 3 < p ^ f)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (Z : Subgroup (GL (Fin 2) F)) [Z.Normal]
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
    (x : G) (hx : orderOf x = 2) (e : Subgroup.centralizer ({x} : Set G) ≃* GL (Fin 2) F ⧸ Z)
    (hu1 : Nat.card F - 1 = 2 * Nat.card Z → Nat.card F ^ 3 ∣ Nat.card G) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hq' : Nat.card F % 4 = 3 := by rw [hF]; exact hq.1
  have hq7 : 7 ≤ Nat.card F := by rw [hF]; omega
  have h2 := two_ne_zero_of_card_eq hp hp2 hF
  by_cases hu : Nat.card F - 1 = 2 * Nat.card Z
  · exact statedClassicalModel_of_cube_dvd e hZ hZodd h2 hx hnonab hq' hq7 p f hp hf hF (hu1 hu)
  · exact statedClassicalModel_of_u_ne_one e hZ hZodd h2 hx hnonab hq' hq7 p f hp hf hF hu

end CFSG.BrauerLinearThree
