module

public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut
public import CFSG.ClassicalInvolution.Asc77.AscT3RAct

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Out

variable {F : Type} [Field F]

theorem conjAut_toGL (g : SL(2, F)) :
    Q3T6.conjAut (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj g := by
  ext b : 1
  apply Subtype.ext
  have h1 : ((Matrix.SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 2) F) =
      Matrix.SpecialLinearGroup.toGL g⁻¹ := (map_inv _ g).symm
  rw [Q3T6.conjAut_apply, Q3T6.coe_conjSL, h1, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, MulAut.conj_apply,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem units_eq_one_or_neg_one [Finite F] (hF : Nat.card F = 3) (u : Fˣ) : u = 1 ∨ u = -1 := by
  have h2 : Nat.card Fˣ = 2 := by rw [Nat.card_units, hF]
  have hu : u ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Fˣ) (x := u)
    rwa [h2] at this
  have hu' : (u : F) * (u : F) = 1 := by
    have := congrArg (fun x : Fˣ => (x : F)) hu
    simpa [pow_two] using this
  rcases mul_self_eq_one_iff.mp hu' with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; exact h))

theorem mul_inv_mem_inn_of_not_inn [Finite F] (hF : Nat.card F = 3) {α β : MulAut SL(2, F)}
    (hα : α ∉ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range)
    (hβ : β ∉ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) :
    α * β⁻¹ ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
  obtain ⟨G, hG⟩ := Q3T6.Fa.sl2_aut_eq_conj_of_card_three hF α
  obtain ⟨H, hH⟩ := Q3T6.Fa.sl2_aut_eq_conj_of_card_three hF β
  have hαG : α = Q3T6.conjAut G := by
    ext b : 1
    exact hG b
  have hβH : β = Q3T6.conjAut H := by
    ext b : 1
    exact hH b
  have hdet : ∀ M : GL (Fin 2) F, Matrix.GeneralLinearGroup.det M = 1 →
      Q3T6.conjAut M ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
    intro M hM
    have hmem : M ∈ (Matrix.SpecialLinearGroup.toGL : SL(2, F) →* GL (Fin 2) F).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hM
    obtain ⟨g, rfl⟩ := hmem
    exact ⟨g, (conjAut_toGL g).symm⟩
  have hG1 : Matrix.GeneralLinearGroup.det G ≠ 1 := fun h => hα (by rw [hαG]; exact hdet G h)
  have hH1 : Matrix.GeneralLinearGroup.det H ≠ 1 := fun h => hβ (by rw [hβH]; exact hdet H h)
  have hGH : Matrix.GeneralLinearGroup.det G = Matrix.GeneralLinearGroup.det H := by
    rcases units_eq_one_or_neg_one hF (Matrix.GeneralLinearGroup.det G) with h | h
    · exact absurd h hG1
    · rcases units_eq_one_or_neg_one hF (Matrix.GeneralLinearGroup.det H) with h' | h'
      · exact absurd h' hH1
      · rw [h, h']
  have hdet1 : Matrix.GeneralLinearGroup.det (G * H⁻¹) = 1 := by
    rw [map_mul, map_inv, hGH, mul_inv_cancel]
  have h2 := hdet _ hdet1
  rw [map_mul, map_inv] at h2
  rw [hαG, hβH]
  exact h2

end Out

section Act

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
  {L : Subgroup G} {e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)}

theorem mem_of_phiG_inner (hF : Odd (Nat.card F)) {T RL Rp : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hRT : RL ≤ T) (hRL : IsSylow2In RL L)
    (hRp : ∀ y ∈ T, phiG L e y = 1 → y ∈ Rp) {y : G} (hyT : y ∈ T)
    (hin : phiG L e y ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) : y ∈ RL ⊔ Rp := by
  obtain ⟨r, hr, hry⟩ := exists_mem_of_phiG_inner hF hT2 hTN hRT hRL hyT hin
  have hrN : r ∈ Subgroup.normalizer (L : Set G) := hTN (hRT hr)
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hTN hyT
  have h1 : phiG L e (r⁻¹ * y) = 1 := by
    rw [phiG_mul (Subgroup.inv_mem _ hrN) hyN, phiG_inv hrN, hry, inv_mul_cancel]
  have h2 : r⁻¹ * y ∈ Rp := hRp _ (T.mul_mem (T.inv_mem (hRT hr)) hyT) h1
  have : y = r * (r⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right h2)

theorem mem_sup_of_not_inner (hF3 : Nat.card F = 3) {T RL Rp V : Subgroup G} {v : G}
    (hT2 : IsPGroup 2 ↥T) (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hRT : RL ≤ T)
    (hRL : IsSylow2In RL L) (hRp : ∀ y ∈ T, phiG L e y = 1 → y ∈ Rp) (hvV : v ∈ V)
    (hvT : v ∈ T) (hv : phiG L e v ∉ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) {x : G}
    (hxT : x ∈ T) : x ∈ RL ⊔ Rp ⊔ V := by
  have hF : Odd (Nat.card F) := by rw [hF3]; exact ⟨1, rfl⟩
  by_cases hx : phiG L e x ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range
  · exact Subgroup.mem_sup_left (mem_of_phiG_inner hF hT2 hTN hRT hRL hRp hxT hx)
  · have hxN : x ∈ Subgroup.normalizer (L : Set G) := hTN hxT
    have hvN : v ∈ Subgroup.normalizer (L : Set G) := hTN hvT
    have hxv : phiG L e (x * v⁻¹) ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
      rw [phiG_mul hxN (Subgroup.inv_mem _ hvN), phiG_inv hvN]
      exact mul_inv_mem_inn_of_not_inn hF3 hx hv
    have hxvT : x * v⁻¹ ∈ T := T.mul_mem hxT (T.inv_mem hvT)
    have h1 := mem_of_phiG_inner hF hT2 hTN hRT hRL hRp hxvT hxv
    have : x = (x * v⁻¹) * v := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hvV)

end Act

end CFSG.ClassicalInvolution.Q3.Q3T6D
