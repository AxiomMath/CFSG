module

public import CFSG.CharacterTheory.BrauerLinearThree.QThreeAssembly
public import CFSG.CharacterTheory.BrauerLinearThree.TenCube

public section

namespace CFSG.BrauerLinearThree

theorem brauer_linear_three_involution_centralizer_q3mod4
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 4 = 3 ∧ 3 < p ^ f)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (Z : Subgroup (GL (Fin 2) F)) [Z.Normal]
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
    (x : G) (hx : orderOf x = 2) (e : Subgroup.centralizer ({x} : Set G) ≃* GL (Fin 2) F ⧸ Z) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hq' : Nat.card F % 4 = 3 := by rw [hF]; exact hq.1
  have hq7 : 7 ≤ Nat.card F := by rw [hF]; omega
  have h2 := two_ne_zero_of_card_eq hp hp2 hF
  exact brauer_linear_three_involution_centralizer_q3mod4_of_u_eq_one p f hp hp2 hf hq G hnonab
    F hF Z hZ hZodd x hx e (cube_dvd_card_of_u_eq_one e hZ hZodd h2 hx hnonab hq' hq7 p f hp hf hF)

end CFSG.BrauerLinearThree
