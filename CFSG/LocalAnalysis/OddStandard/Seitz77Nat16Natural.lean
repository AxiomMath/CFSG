module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Diag
public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Weyl
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {F : Type*} [Field F]

@[expose] noncomputable def linRep (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)) :
    SL(2, F) →* Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin 8) (Fin 8) (ZMod 2) ≃ₐ[ZMod 2]
    Module.End (ZMod 2) (Fin 8 → ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2) →* _).comp
    ((Units.coeHom (Matrix (Fin 8) (Fin 8) (ZMod 2))).comp ρ)

theorem linRep_apply (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)) (g : SL(2, F)) (v : Fin 8 → ZMod 2) :
    linRep ρ g v = (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v := by
  simp [linRep, Matrix.toLinAlgEquiv'_apply]

theorem linRep_injective (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) :
    Function.Injective (linRep ρ) := by
  intro g g' h
  apply hρ
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have := LinearMap.congr_fun h v
  rwa [linRep_apply, linRep_apply] at this

@[expose] def conjEnd {G : Type*} [Monoid G] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (r : G →* AddMonoid.End M) : G →* AddMonoid.End N where
  toFun g := e.toAddMonoidHom.comp ((r g).comp e.symm.toAddMonoidHom)
  map_one' := AddMonoidHom.ext fun n => by
    simp only [map_one]
    show e (e.symm n) = n
    exact e.apply_symm_apply n
  map_mul' g g' := AddMonoidHom.ext fun n => by
    simp only [map_mul]
    show e (r g (r g' (e.symm n))) = e (r g (e.symm (e (r g' (e.symm n)))))
    rw [e.symm_apply_apply]

theorem conjEnd_apply {G : Type*} [Monoid G] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (r : G →* AddMonoid.End M) (g : G) (n : N) :
    conjEnd e r g n = e (r g (e.symm n)) := rfl

@[expose] noncomputable def addRep (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)) :
    SL(2, F) →* AddMonoid.End (Fin 8 → ZMod 2) where
  toFun g := (linRep ρ g).toAddMonoidHom
  map_one' := AddMonoidHom.ext fun v => by
    simp only [map_one]
    rfl
  map_mul' g g' := AddMonoidHom.ext fun v => by
    simp only [map_mul]
    rfl

theorem addRep_apply (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)) (g : SL(2, F)) (v : Fin 8 → ZMod 2) :
    addRep ρ g v = (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v := linRep_apply ρ g v


theorem tE_pow_eq_one_iff (a : F) (ha : a ≠ 0) (n : ℕ) : tE a ha ^ n = 1 ↔ a ^ n = 1 := by
  rw [tE_pow]
  constructor
  · intro h
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simpa [tE] using this
  · intro h
    rw [tE_congr _ one_ne_zero h, tE_one]

theorem orderOf_tE (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1) :
    orderOf (tE ζ (zeta_ne_zero hζ)) = 15 := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  rw [orderOf_eq_iff (by norm_num)]
  rw [orderOf_eq_iff (by norm_num)] at hord
  refine ⟨(tE_pow_eq_one_iff _ _ _).2 hord.1, fun m hm hm0 => ?_⟩
  rw [Ne, tE_pow_eq_one_iff]
  exact hord.2 m hm hm0

theorem card_SL2 (hF : Nat.card F = 16) : Nat.card SL(2, F) = 4080 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  let _ := Fintype.ofFinite F
  have hq : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  norm_num


open Pointwise in
theorem exists_conj_pow_of_orderOf_three (hF : Nat.card F = 16) {x y : SL(2, F)}
    (hx : orderOf x = 3) (hy : orderOf y = 3) : ∃ (g : SL(2, F)) (k : ℕ), x = g * y ^ k * g⁻¹ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Finite SL(2, F) := inferInstance
  have h3 : (Nat.card SL(2, F)).factorization 3 = 1 := by
    rw [card_SL2 hF]
    have e : (4080 : ℕ) = 3 * 1360 := by norm_num
    rw [e, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 1360 by norm_num)]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 SL(2, F) := Sylow.ofCard (Subgroup.zpowers x) (by
    rw [Nat.card_zpowers, hx, h3]; norm_num)
  let Q : Sylow 3 SL(2, F) := Sylow.ofCard (Subgroup.zpowers y) (by
    rw [Nat.card_zpowers, hy, h3]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) Q P
  have hxP : x ∈ (P : Subgroup SL(2, F)) := Subgroup.mem_zpowers x
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
  obtain ⟨s, hs, hsx⟩ := hxP
  have hs' : s ∈ Submonoid.powers y :=
    (mem_powers_iff_mem_zpowers).2 (by simpa [Q] using hs)
  obtain ⟨k, rfl⟩ := hs'
  exact ⟨g, k, by rw [← hsx]; simp [MulAut.smul_def]⟩


@[expose] def scaleFst (κ : F) (hκ : κ ≠ 0) : (F × F) ≃+ (F × F) where
  toFun v := (κ⁻¹ * v.1, v.2)
  invFun v := (κ * v.1, v.2)
  left_inv v := by simp [hκ]
  right_inv v := by simp [hκ]
  map_add' a b := by ext <;> simp [mul_add]

section Main

variable (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)

include hF hζ

theorem natural_module_aux (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ)
    (hfpf : ∀ v : Fin 8 → ZMod 2, linRep ρ (tE ζ (zeta_ne_zero hζ) ^ 5) v = v → v = 0) :
    ∃ Φ : (Fin 8 → ZMod 2) ≃+ (F × F), ∀ g w, Φ (linRep ρ g w) = natHom g (Φ w) := by
  have := charP_two hF
  have hz := zeta_ne_zero hζ
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  have hinj := linRep_injective ρ hρ
  let H : Module.End (ZMod 2) (Fin 8 → ZMod 2) := linRep ρ (tE ζ hz)
  let R : Module.End (ZMod 2) (Fin 8 → ZMod 2) := linRep ρ wE
  have hζ15 : ζ ^ 15 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hord] at this
  have hH15 : H ^ 15 = 1 := by
    rw [← map_pow, (tE_pow_eq_one_iff ζ hz 15).2 hζ15, map_one]
  have hH3 : H ^ 3 ≠ 1 := by
    intro h
    rw [← map_pow, ← map_one (linRep ρ)] at h
    have h1 := (tE_pow_eq_one_iff ζ hz 3).1 (hinj h)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    norm_num at h2
  have hR2 : R * R = 1 := by
    rw [← map_mul, wE_mul_wE, map_one]
  have htE14 : tE ζ hz ^ 14 = tE ζ⁻¹ (inv_ne_zero hz) := by
    rw [tE_pow]
    exact tE_congr _ _ (Weights16.inv_eq_pow_fourteen hord).symm
  have hRH : R * H = H ^ 14 * R := by
    rw [← map_mul, ← map_pow, ← map_mul, htE14, wE_mul_tE ζ hz]
  have hfpf5 : ∀ v, (H ^ 5) v = v → v = 0 := by
    intro v hv
    apply hfpf
    rwa [map_pow]
  have hV : Module.finrank (ZMod 2) (Fin 8 → ZMod 2) = 8 := by simp
  obtain ⟨Θ, hΘ⟩ := exists_diagonalizing (V := Fin 8 → ZMod 2) H hF hζ hV R hH15 hH3 hR2 hRH hfpf5
  let r : SL(2, F) →* AddMonoid.End (F × F) := conjEnd Θ.symm (addRep ρ)
  have hr : ∀ g v, r g v = Θ.symm (linRep ρ g (Θ v)) := fun g v => rfl
  have hh : ∀ v, r (tE ζ hz) v = (ζ * v.1, ζ⁻¹ * v.2) := by
    intro v
    rw [hr, Θ.symm_apply_eq]
    exact hΘ v.1 v.2
  have hrinj : Function.Injective r := by
    intro g g' h
    apply hinj
    refine LinearMap.ext fun w => ?_
    have := DFunLike.congr_fun h (Θ.symm w)
    rw [hr, hr, Θ.apply_symm_apply] at this
    exact Θ.symm.injective this
  obtain ⟨κ, hκ, hnat⟩ := natural_of_torus hF hζ r hz hh hrinj
  refine ⟨Θ.symm.trans (scaleFst κ hκ), fun g w => ?_⟩
  have h1 := hnat g (Θ.symm w)
  rw [hr, Θ.apply_symm_apply] at h1
  exact h1


end Main

@[expose] def prodEquivFin : (F × F) ≃+ (Fin 2 → F) where
  toFun v := ![v.1, v.2]
  invFun f := (f 0, f 1)
  left_inv v := rfl
  right_inv f := by
    ext i
    fin_cases i <;> rfl
  map_add' a b := by
    ext i
    fin_cases i <;> rfl

theorem prodEquivFin_apply (v : F × F) : prodEquivFin v = ![v.1, v.2] := rfl

theorem mulVec_prodEquivFin (g : SL(2, F)) (v : F × F) :
    (g : Matrix (Fin 2) (Fin 2) F) *ᵥ prodEquivFin v = prodEquivFin (natHom g v) := by
  rw [prodEquivFin_apply, prodEquivFin_apply, natHom_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem natural_module (hF : Nat.card F = 16) (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2))
    (hρ : Function.Injective ρ) {x : SL(2, F)} (hx : orderOf x = 3)
    (hfpf : ∀ v : Fin 8 → ZMod 2, (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v → v = 0) :
    ∃ Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F), ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
      Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v := by
  obtain ⟨ζ, hζ⟩ := Weights16.exists_pow_four_eq hF
  have hz := zeta_ne_zero hζ
  have hy : orderOf (tE ζ hz ^ 5) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [orderOf_tE hF hζ]; norm_num), orderOf_tE hF hζ]
  obtain ⟨g, k, hxeq⟩ := exists_conj_pow_of_orderOf_three hF hx hy
  have hcg : ∀ w, linRep ρ g⁻¹ (linRep ρ g w) = w := by
    intro w
    calc linRep ρ g⁻¹ (linRep ρ g w) = (linRep ρ g⁻¹ * linRep ρ g) w := rfl
      _ = linRep ρ (g⁻¹ * g) w := by rw [map_mul]
      _ = w := by rw [inv_mul_cancel, map_one]; rfl
  have hfpf5 : ∀ v, linRep ρ (tE ζ hz ^ 5) v = v → v = 0 := by
    intro v hv
    have hk : ∀ k : ℕ, (linRep ρ (tE ζ hz ^ 5) ^ k) v = v := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hv, ih]
    have h1 : linRep ρ x (linRep ρ g v) = linRep ρ g v := by
      rw [hxeq, map_mul, map_mul, map_pow, Module.End.mul_apply, Module.End.mul_apply, hcg, hk]
    have h2 : linRep ρ g v = 0 := hfpf _ (by rw [← linRep_apply]; exact h1)
    calc v = linRep ρ g⁻¹ (linRep ρ g v) := (hcg v).symm
      _ = 0 := by rw [h2, map_zero]
  obtain ⟨Φ, hΦ⟩ := natural_module_aux hF hζ ρ hρ hfpf5
  refine ⟨Φ.trans prodEquivFin, fun g v => ?_⟩
  show prodEquivFin (Φ _) = _
  rw [← linRep_apply, hΦ, ← mulVec_prodEquivFin]
  rfl


end Nat16

end CFSG.OddStandard.Seitz77
