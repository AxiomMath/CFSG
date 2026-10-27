module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResEData

public section

namespace CFSG.EvenSporadicStandard.M24Std

theorem card_mulAut_dvd_gl12 {Cc : Type} [Group Cc] [Finite Cc]
    (hcomm : ∀ a b : Cc, a * b = b * a) (h2 : ∀ a : Cc, a * a = 1)
    (hcard : Nat.card Cc = 2 ^ 12) : Nat.card (MulAut Cc) ∣ gl12 := by
  classical
  let _ : CommGroup Cc := { (inferInstance : Group Cc) with mul_comm := hcomm }
  let V := Additive Cc
  have h2' : ∀ x : V, (2 : ℕ) • x = 0 := by
    intro x
    show Additive.ofMul ((Additive.toMul x) ^ 2) = Additive.ofMul 1
    rw [sq, h2]
  let _ : Module (ZMod 2) V := AddCommGroup.zmodModule h2'
  have : Fintype V := Fintype.ofFinite V
  have hfin : Module.finrank (ZMod 2) V = 12 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
    have hV : Fintype.card V = 2 ^ 12 := by
      rw [Fintype.card_eq_nat_card]
      exact hcard
    rw [ZMod.card, hV] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hfin
  let lin : MulAut Cc → (V →ₗ[ZMod 2] V) := fun α =>
    AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive α).toAddMonoidHom
  have hlin_apply : ∀ α x, lin α x = Additive.ofMul (α (Additive.toMul x)) := fun α x => rfl
  let M : MulAut Cc →* Matrix (Fin 12) (Fin 12) (ZMod 2) :=
    { toFun := fun α => LinearMap.toMatrix b b (lin α)
      map_one' := by
        have : lin 1 = LinearMap.id := by
          ext x
          rfl
        rw [this, LinearMap.toMatrix_id]
      map_mul' := fun α β => by
        rw [← LinearMap.toMatrix_mul]
        congr 1 }
  have hinj : Function.Injective M := by
    intro α β hαβ
    have h1 : lin α = lin β := (LinearMap.toMatrix b b).injective hαβ
    apply MulEquiv.ext
    intro x
    have := congrArg (fun f : V →ₗ[ZMod 2] V => f (Additive.ofMul x)) h1
    simpa [hlin_apply] using this
  have hdvd := Subgroup.card_dvd_of_injective M.toHomUnits (by
    intro α β h
    apply hinj
    have := congrArg Units.val h
    simpa using this)
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 12) (ZMod 2)) = gl12 := by
    rw [Matrix.card_GL_field, ZMod.card, gl12]
    exact Fin.prod_univ_eq_prod_range (fun i => 2 ^ 12 - 2 ^ i) 12
  exact hGL ▸ hdvd

end CFSG.EvenSporadicStandard.M24Std
