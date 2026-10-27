module

public import CFSG.CharacterTheory.Semidihedral.OddFieldLift

public section

namespace CFSG.Wreathed.SylowCentralizerOddField

universe u v

open CFSG.Semidihedral.OddFieldLift CFSG.Semidihedral.SemilinearOddExtensions

@[expose] noncomputable def fieldProjection (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : Gamma F Sigma →* Sigma :=
  (gammaFieldEquiv F Sigma).toMonoidHom.comp
    (SemidirectProduct.rightHom.comp (gammaSemidirectEquiv F Sigma).symm.toMonoidHom)

theorem fieldProjection_mul (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (g : Gamma F Sigma) (hg : g ∈ gammaLinear F Sigma) (sigma : Sigma) :
    fieldProjection F Sigma (g * ((gammaFieldEquiv F Sigma).symm sigma : Gamma F Sigma)) =
      sigma := by
  have h : (gammaSemidirectEquiv F Sigma) (SemidirectProduct.mk ⟨g, hg⟩
      ((gammaFieldEquiv F Sigma).symm sigma)) =
        g * ((gammaFieldEquiv F Sigma).symm sigma : Gamma F Sigma) :=
    internalSemidirectEquiv_apply _ _ _ _
  simp only [fieldProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← h, MulEquiv.symm_apply_apply, SemidirectProduct.rightHom_eq_right,
    MulEquiv.apply_symm_apply]

theorem map_eq_one_of_pow_two_pow {G Q : Type*} [Group G] [Group Q] [Finite Q]
    (hQ : Odd (Nat.card Q)) (φ : G →* Q) {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) : φ x = 1 := by
  have h1 : orderOf (φ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (φ x) ∣ Nat.card Q := orderOf_dvd_natCard (φ x)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Q) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hQ)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end CFSG.Wreathed.SylowCentralizerOddField
