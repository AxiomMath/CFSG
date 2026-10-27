module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Fix

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {F : Type*} [Field F]

@[expose] noncomputable def fStr (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) :
    F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2) where
  toFun a := AddMonoidHom.toZModLinearMap 2 (Φ.symm.toAddMonoidHom.comp
    ((AddMonoidHom.mk' (fun w : Fin 2 → F => a • w) (fun w w' => smul_add a w w')).comp
      Φ.toAddMonoidHom))
  map_one' := LinearMap.ext fun v => by
    show Φ.symm ((1 : F) • Φ v) = v
    rw [one_smul, AddEquiv.symm_apply_apply]
  map_mul' a b := LinearMap.ext fun v => by
    show Φ.symm ((a * b) • Φ v) = Φ.symm (a • Φ (Φ.symm (b • Φ v)))
    rw [AddEquiv.apply_symm_apply, mul_smul]
  map_zero' := LinearMap.ext fun v => by
    show Φ.symm ((0 : F) • Φ v) = 0
    rw [zero_smul, map_zero]
  map_add' a b := LinearMap.ext fun v => by
    show Φ.symm ((a + b) • Φ v) = Φ.symm (a • Φ v) + Φ.symm (b • Φ v)
    rw [add_smul, map_add]

theorem fStr_apply (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (a : F) (v : Fin 8 → ZMod 2) :
    Φ (fStr Φ a v) = a • Φ v := by
  show Φ (Φ.symm (a • Φ v)) = a • Φ v
  exact AddEquiv.apply_symm_apply _ _

theorem fStr_commute {ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)}
    {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
    (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
      Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)
    (g : SL(2, F)) (a : F) (v : Fin 8 → ZMod 2) :
    (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ fStr Φ a v =
      fStr Φ a ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) := by
  apply Φ.injective
  rw [hΦ, fStr_apply, fStr_apply, hΦ, Matrix.mulVec_smul]

@[expose] def matAct : Matrix (Fin 2) (Fin 2) F →* AddMonoid.End (F × F) where
  toFun M := AddMonoidHom.mk' (fun v => (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2))
    (fun v w => by ext <;> simp <;> ring)
  map_one' := by
    refine AddMonoidHom.ext fun v => ?_
    show (_, _) = v
    simp
  map_mul' A B := by
    refine AddMonoidHom.ext fun v => ?_
    show (_, _) = (_, _)
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    constructor <;> ring

theorem matAct_apply (M : Matrix (Fin 2) (Fin 2) F) (v : F × F) :
    matAct M v = (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2) := rfl

theorem matAct_injective : Function.Injective (matAct : Matrix (Fin 2) (Fin 2) F → _) := by
  intro A B h
  have h1 := DFunLike.congr_fun h (1, 0)
  have h2 := DFunLike.congr_fun h (0, 1)
  simp only [matAct_apply, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1.1
  · exact h2.1
  · exact h1.2
  · exact h2.2

section Range

variable {ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)} {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
  (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
    Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)

@[expose] def fMatrix (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n : GL (Fin 8) (ZMod 2)) :
    Matrix (Fin 2) (Fin 2) F :=
  !![(coordMap Φ n (1, 0)).1, (coordMap Φ n (0, 1)).1;
    (coordMap Φ n (1, 0)).2, (coordMap Φ n (0, 1)).2]

@[expose] noncomputable def fDet (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F))
    (n : GL (Fin 8) (ZMod 2)) : F :=
  (fMatrix Φ n).det

theorem coordMap_eq_matAct (n : GL (Fin 8) (ZMod 2))
    (hlin : IsSemilinear 0 (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))
    (u : F × F) : coordMap Φ n u = matAct (fMatrix Φ n) u := by
  have hlin' := (isSemilinear_iff_coord Φ n 0).1 hlin
  simp only [pow_zero, pow_one] at hlin'
  have := semilinear_form (coordMap Φ n) (j := 0) (fun a v => by simpa using hlin' a v) u.1 u.2
  simp only [pow_zero, pow_one] at this
  rw [Prod.mk.eta] at this
  rw [this, matAct_apply]
  ext <;> simp [fMatrix, mul_comm]

include hΦ

theorem coordMap_ρ (g : SL(2, F)) (u : F × F) : coordMap Φ (ρ g) u = natHom g u := by
  obtain ⟨v, rfl⟩ := (coord Φ).surjective u
  rw [coordMap_apply, coord_natural hΦ]

theorem fDet_ρ (g : SL(2, F)) : fDet Φ (ρ g) = 1 := by
  have h1 := coordMap_ρ hΦ g (1, 0)
  have h2 := coordMap_ρ hΦ g (0, 1)
  simp only [fDet, fMatrix, Matrix.det_fin_two_of, h1, h2, natHom_apply, mul_one, mul_zero,
    add_zero, zero_add]
  exact det_entries g

theorem exists_eq_of_linear_det (n : GL (Fin 8) (ZMod 2))
    (hlin : IsSemilinear 0 (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))
    (hdet : fDet Φ n = 1) : ∃ g : SL(2, F), ρ g = n := by
  let g : SL(2, F) := ⟨fMatrix Φ n, hdet⟩
  refine ⟨g, ?_⟩
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  apply (coord Φ).injective
  rw [coord_natural hΦ, ← coordMap_apply Φ n]
  show matAct (fMatrix Φ n) (coord Φ v) = coordMap Φ n (coord Φ v)
  rw [coordMap_eq_matAct n hlin]

omit hΦ

theorem fDet_eq_one_of_pow (hF : Nat.card F = 16) (n : GL (Fin 8) (ZMod 2))
    (hlin : IsSemilinear 0 (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))
    {m : ℕ} (hn : n ^ 2 ^ m = 1) : fDet Φ n = 1 := by
  let N := coordMap Φ n
  let M := fMatrix Φ n
  have hN : ∀ u, N u = matAct M u := coordMap_eq_matAct n hlin
  let N' : AddMonoid.End (F × F) := N.toAddMonoidHom
  have hNM : N' = matAct M := DFunLike.ext _ _ hN
  have hpow : ∀ (k : ℕ) (v : Fin 8 → ZMod 2),
      (N' ^ k) (coord Φ v) =
        coord Φ (((n ^ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      calc (N' ^ (k + 1)) (coord Φ v) = N ((N' ^ k) (coord Φ v)) := by
            rw [pow_succ']; rfl
        _ = N (coord Φ (((n ^ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) :=
            by rw [ih]
        _ = coord Φ (((n ^ (k + 1) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
            v) := by
            rw [coordMap_apply Φ n, Matrix.mulVec_mulVec, pow_succ', Units.val_mul]
  have hN1 : N' ^ 2 ^ m = 1 := by
    refine DFunLike.ext _ _ fun u => ?_
    obtain ⟨v, rfl⟩ := (coord Φ).surjective u
    rw [hpow, hn]
    simp
  have hMpow : M ^ 2 ^ m = 1 := by
    apply matAct_injective
    rw [map_pow, ← hNM, hN1, map_one]
  have hdet : M.det ^ 2 ^ m = 1 := by rw [← Matrix.det_pow, hMpow, Matrix.det_one]
  have hdet0 : M.det ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero m two_ne_zero)] at hdet
    exact zero_ne_one hdet
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have h15 : M.det ^ 15 = 1 := by
    let _ := Fintype.ofFinite F
    have hq : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
    have := FiniteField.pow_card_sub_one_eq_one M.det hdet0
    rwa [hq] at this
  have h1 := orderOf_dvd_of_pow_eq_one hdet
  have h2 := orderOf_dvd_of_pow_eq_one h15
  have hcop : Nat.Coprime (2 ^ m) 15 := Nat.Coprime.pow_left m (by norm_num)
  have : orderOf M.det = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact orderOf_eq_one_iff.1 this

include hΦ

theorem exists_eq_of_linear_pow (hF : Nat.card F = 16) (n : GL (Fin 8) (ZMod 2))
    (hlin : IsSemilinear 0 (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))
    {m : ℕ} (hn : n ^ 2 ^ m = 1) : ∃ g : SL(2, F), ρ g = n :=
  exists_eq_of_linear_det hΦ n hlin (fDet_eq_one_of_pow hF n hlin hn)

end Range

section Involution

variable {ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)}
  {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
  (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
    Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)
  (n : GL (Fin 8) (ZMod 2)) (hnU : ∀ c : F, ∃ c' : F, n * ρ (uE c) * n⁻¹ = ρ (uE c'))
  (hsl : IsSemilinear 2 (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))

include hΦ hnU hsl

theorem borel_involution_mu (hn2 : n * n = 1) :
    ∃ p s t : F, p ≠ 0 ∧ t ≠ 0 ∧
      (∀ x y : F, coordMap Φ n (x, y) = (p * x ^ 2 ^ 2 + s * y ^ 2 ^ 2, t * y ^ 2 ^ 2)) ∧
      (∀ c : F, n * ρ (uE c) * n⁻¹ = ρ (uE ((p / t) * c ^ 2 ^ 2))) ∧
      p * p ^ 4 = 1 ∧ t * t ^ 4 = 1 := by
  obtain ⟨p, s, t, hp, ht, hform, hact⟩ := borel_normalizer_form hΦ n hnU hsl
  have hN2 : ∀ u, coordMap Φ n (coordMap Φ n u) = u := by
    intro u
    obtain ⟨v, rfl⟩ := (coord Φ).surjective u
    rw [coordMap_apply, coordMap_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hn2,
      Units.val_one, Matrix.one_mulVec]
  refine ⟨p, s, t, hp, ht, hform, hact, ?_, ?_⟩
  · have h1 := hN2 (1, 0)
    rw [hform 1 0] at h1
    simp only [one_pow, mul_one, zero_pow (pow_ne_zero 2 two_ne_zero), mul_zero, add_zero] at h1
    rw [hform] at h1
    simp only [mul_zero, add_zero, zero_pow (pow_ne_zero 2 two_ne_zero), Prod.mk.injEq] at h1
    have h2 := h1.1
    simpa using h2
  · have h1 := hN2 (0, 1)
    rw [hform 0 1] at h1
    simp only [one_pow, mul_one, mul_zero, zero_add, zero_pow (pow_ne_zero 2 two_ne_zero)] at h1
    rw [hform] at h1
    have h2 := congrArg Prod.snd h1
    simpa using h2

end Involution

end Nat16

end CFSG.OddStandard.Seitz77
