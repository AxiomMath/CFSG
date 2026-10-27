module

public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG
open scoped IsMulCommutative

theorem card_le_four_of_faithful_p_sq {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P E : Subgroup G} [IsElementaryAbelian p ↥P] [Finite P] (hPcard : Nat.card ↥P = p ^ 2)
    (hnorm : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P) (hE : ∀ e ∈ E, e * e = 1)
    (hfaith : ∀ e ∈ E, (∀ x ∈ P, e * x * e⁻¹ = x) → e = 1) : Nat.card ↥E ≤ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hfin : Module.Finite (ZMod p) (Additive ↥P) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) (Additive ↥P) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive ↥P)
    rw [Nat.card_zmod] at h
    have hV' : Nat.card (Additive ↥P) = p ^ 2 := by rw [← hPcard]; rfl
    rw [hV'] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let b : Module.Basis (Fin 2) (ZMod p) (Additive ↥P) :=
    Module.finBasisOfFinrankEq (ZMod p) (Additive ↥P) hdim
  let act : ↥E → (Additive ↥P →+ Additive ↥P) := fun e =>
    { toFun := fun x => Additive.ofMul (⟨(e : G) * ((Additive.toMul x : ↥P) : G) * (e : G)⁻¹,
        hnorm e e.2 _ (Additive.toMul x : ↥P).2⟩ : ↥P)
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [toMul_add]
        simp [mul_assoc] }
  let f : ↥E →* Module.End (ZMod p) (Additive ↥P) :=
    { toFun := fun e => AddMonoidHom.toZModLinearMap p (act e)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [act]
      map_mul' := fun e₁ e₂ => by
        refine LinearMap.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [act, mul_assoc] }
  have hf1 : ∀ e : ↥E, f e = 1 → e = 1 := by
    intro e he
    apply Subtype.ext
    refine hfaith e e.2 fun x hx => ?_
    have := congrArg (fun T => Additive.toMul (T (Additive.ofMul (⟨x, hx⟩ : ↥P)))) he
    simpa [f, act] using this
  let ρ : ↥E →* GL (Fin 2) (ZMod p) :=
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).toMonoidHom.comp
      f.toHomUnits
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : f.toHomUnits e = 1 := by
      have : (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv) (f.toHomUnits e) =
          (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv) 1 := by
        rw [map_one]; exact he
      exact (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).injective this
    exact hf1 e (congrArg Units.val h1)
  have hsq : ∀ x ∈ ρ.range, x * x = 1 := by
    rintro _ ⟨e, rfl⟩
    rw [← map_mul]
    have : e * e = 1 := Subtype.ext (hE e e.2)
    rw [this, map_one]
  have := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_gl2 h2 ρ.range hsq
  calc Nat.card ↥E = Nat.card ρ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ ≤ 4 := this

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
