module

public import CFSG.CharacterTheory.BrauerLinearThree.NineOrder
public import CFSG.CharacterTheory.BrauerLinearThree.FourGOrder

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem cube_dvd_card_of_u_ne_one
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hu : Nat.card F - 1 ≠ 2 * Nat.card Z) : Nat.card F ^ 3 ∣ Nat.card G :=
  cube_dvd_card_of_four_G φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF
    (fun _ hz hz1 => centralizer_le_of_mem_centerSub φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF
      hz hz1) hu

include φ hZ hZodd h2 hJ in
theorem card_mul_eq_of_u_ne_one
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hu : Nat.card F - 1 ≠ 2 * Nat.card Z) :
    Nat.card G * Nat.card Z = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) :=
  card_mul_eq_of_cube_dvd φ hZ hZodd h2 hJ hnonab hq (by omega) p f hp hf hF
    (cube_dvd_card_of_u_ne_one φ hZ hZodd h2 hJ hnonab hq hq7 p f hp hf hF hu)

end CFSG.BrauerLinearThree
