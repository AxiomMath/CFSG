module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverUnitriangularFour

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OrthogonalEightCover

open Matrix LinearFlag LinearCover

variable {K : Type} [Field K]

@[expose] noncomputable def unitriangularEquivU4 (φ : K ≃+* ZMod 2) : unitriangular 4 K ≃* U4 :=
  let f : unitriangular 4 K →* U4 :=
    ((SpecialLinearGroup.map (φ : K →+* ZMod 2)).comp (unitriangular 4 K).subtype).codRestrict
      U4 fun A => ⟨fun i j hij => by simp [A.2.1 i j hij], fun i => by simp [A.2.2 i]⟩
  let g : U4 →* unitriangular 4 K :=
    ((SpecialLinearGroup.map (φ.symm : ZMod 2 →+* K)).comp U4.subtype).codRestrict
      (unitriangular 4 K) fun A => ⟨fun i j hij => by simp [A.2.1 i j hij], fun i => by
        simp [A.2.2 i]⟩
  MonoidHom.toMulEquiv f g
    (MonoidHom.ext fun A => by
      apply Subtype.ext
      ext i j
      change φ.symm (φ (((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j)) = _
      exact φ.symm_apply_apply _)
    (MonoidHom.ext fun A => by
      apply Subtype.ext
      ext i j
      change φ (φ.symm (((A : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) i j)) = _
      exact φ.apply_symm_apply _)

theorem levi_four_kernel_sq_eq_one (hK : Nat.card K = 2) {X : Type*} [Group X]
    (ρ : SpecialLinearGroup (Fin 4) K →* X) (hρ : Function.Injective ρ) {F : Type*} [Group F]
    [Finite F] [Group.IsPerfect F] (θ : F →* ρ.range) (hθ : Function.Surjective θ)
    (hcen : θ.ker ≤ Subgroup.center F) (h2 : IsPGroup 2 θ.ker) : ∀ c ∈ θ.ker, c ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  obtain ⟨P₁, hP₁⟩ := exists_sylow_unitriangular (K := K) 2 (n := 4) (by norm_num)
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  set S : Sylow 2 ρ.range := P₁.mapSurjective ρ.rangeRestrict_surjective with hSdef
  have hS : (S : Subgroup ρ.range) = (unitriangular 4 K).map ρ.rangeRestrict := by
    rw [hSdef, Sylow.coe_mapSurjective, hP₁]
  have hinj : Function.Injective ρ.rangeRestrict := MonoidHom.rangeRestrict_injective_iff.mpr hρ
  let e : (S : Subgroup ρ.range) ≃* U4 := ((MulEquiv.subgroupCongr hS).trans
    ((unitriangular 4 K).equivMapOfInjective _ hinj).symm).trans
      (unitriangularEquivU4 (FiniteField.ringEquivOfCardEq hcard))
  have := (perfect_cover_kernel_bound_of_sylow θ hθ hcen h2 S e).1
  exact fun c hc => CFSG.elemPow_eq_one_of_isElementaryAbelian c hc

end OrthogonalEightCover

end CFSG.LocalAnalysis.ComponentInitial
