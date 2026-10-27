module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

@[expose] public section

namespace CFSG

theorem card_GL_fin_two_zmod_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 3) 2]
  simp [Fin.prod_univ_two]

theorem card_GL_fin_one_zmod_three : Nat.card (GL (Fin 1) (ZMod 3)) = 2 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 3) 1]
  simp [Fin.prod_univ_one]

theorem MonoidHom.eq_one_of_coprime_six_GL_fin_two {G : Type*} [Group G] [Finite G]
    (hcop : Nat.Coprime (Nat.card G) 6) (ρ : G →* GL (Fin 2) (ZMod 3)) : ρ = 1 := by
  have hcop48 : Nat.Coprime (Nat.card G) 48 := by
    have h2 : Nat.Coprime (Nat.card G) 2 := hcop.coprime_dvd_right (by norm_num)
    have h8 : Nat.Coprime (Nat.card G) 8 := by simpa using h2.pow_right 3
    simpa using hcop.mul_right h8
  have hdvd : Nat.card ρ.range ∣ Nat.card (GL (Fin 2) (ZMod 3)) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  rw [card_GL_fin_two_zmod_three] at hdvd
  have hcard : Nat.card ρ.range = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop48 (Subgroup.card_range_dvd ρ) hdvd
  exact MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hcard)

end CFSG
