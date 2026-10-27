module

public import CFSG.CGT.Foote82.T66.Proof511Order13
public import CFSG.CGT.Foote82.T66.Proof511PSL43Data
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.CGT.Foote82.Proof511

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem eq_uMat {U : M43} (hlow : ∀ i j : Fin 4, j < i → U i j = 0) (hdiag : ∀ i, U i i = 1) :
    U = uMat (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, hdiag] <;> exact hlow _ _ (by decide)

theorem uMat_pow_three_apply (a b c d e f : ZMod 3) :
    (uMat a b c d e f ^ 3) 0 3 = a * d * f := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  have : (uMat a b c d e f ^ 3) 0 3 = 3 * c + 3 * (a * e + b * f) + a * d * f := by
    simp [uMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_four]
    ring
  rw [this, h3]
  ring

theorem mul_eq_one_symm {B B' : M43} (h : B * B' = 1) : B' * B = 1 := by
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.nonsing_inv_mul B (Matrix.isUnit_det_of_right_inverse h)

theorem conjM_mul {B B' : M43} (h : B * B' = 1) (X Y : M43) :
    (B' * X * B) * (B' * Y * B) = B' * (X * Y) * B := by
  calc (B' * X * B) * (B' * Y * B) = B' * X * (B * B') * Y * B := by
        simp only [Matrix.mul_assoc]
    _ = B' * (X * Y) * B := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem conjM_pow {B B' : M43} (h : B * B' = 1) (X : M43) (n : ℕ) :
    (B' * X * B) ^ n = B' * X ^ n * B := by
  induction n with
  | zero => simp [mul_eq_one_symm h]
  | succ n ih => rw [pow_succ, ih, conjM_mul h, ← pow_succ]

theorem conjM_scalar {B B' : M43} (h : B * B' = 1) (s : ZMod 3) :
    B' * Matrix.scalar (Fin 4) s * B = Matrix.scalar (Fin 4) s := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, mul_eq_one_symm h, Matrix.smul_one_eq_diagonal]

theorem eq_scalar_of_conjM {B B' : M43} (h : B * B' = 1) {X : M43} {s : ZMod 3}
    (hX : B' * X * B = Matrix.scalar (Fin 4) s) : X = Matrix.scalar (Fin 4) s := by
  have h' := mul_eq_one_symm h
  have e : B * (B' * X * B) * B' = X := by
    calc B * (B' * X * B) * B' = (B * B') * X * (B * B') := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]
  rw [← e, hX, conjM_scalar h']

theorem exists_conj_mul_orderOf_eq_thirteen (x : projectiveSL 4 (ZMod 3)) (hx : orderOf x = 3) :
    ∃ g₂ g₃ : projectiveSL 4 (ZMod 3), orderOf (x * (g₂ * x * g₂⁻¹) * (g₃ * x * g₃⁻¹)) = 13 := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := ZMod 3) 3 (n := 4) (by norm_num)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (projectiveSL 4 (ZMod 3)) Q P₀
  have hxk : k * x * k⁻¹ ∈ projUnitriangular 4 (ZMod 3) := by
    rw [← hP₀, ← hk]
    exact (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).2 (by
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hQ (Subgroup.mem_zpowers x))
  obtain ⟨u, hu, hpu⟩ := Subgroup.mem_map.1 hxk
  have hu3 : u ^ 3 = 1 := by
    have h1 : proj 4 (ZMod 3) (u ^ 3) = 1 := by
      rw [map_pow, hpu, conj_pow, hx3, mul_one, mul_inv_cancel]
    have hmem : u ^ 3 ∈ unitriangular 4 (ZMod 3) ⊓ scalars 4 (ZMod 3) :=
      ⟨(unitriangular 4 (ZMod 3)).pow_mem hu 3, proj_eq_one_iff.1 h1⟩
    rw [unitriangular_inf_scalars, Subgroup.mem_bot] at hmem
    exact hmem
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one] at hpu
    have hx1 : x = 1 := by
      have := congrArg (fun z => k⁻¹ * z * k) hpu
      simpa [mul_assoc] using this.symm
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hu
  set U : M43 := (u : Matrix (Fin 4) (Fin 4) (ZMod 3)) with hUdef
  have hUmat : U = uMat (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3) :=
    eq_uMat (fun i j h => hlow i j h) (fun i => hdiag i)
  have hU3 : U ^ 3 = 1 := by
    have h := congrArg (fun A : type_of% u => (A : Matrix (Fin 4) (Fin 4) (ZMod 3))) hu3
    exact h
  have hadf := uMat_pow_three_apply (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
  rw [← hUmat, hU3, Matrix.one_apply_ne (by decide)] at hadf
  have hU1 : uMat (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3) ≠ 1 := by
    rw [← hUmat]
    intro h
    exact hu1 (Subtype.ext h)
  obtain ⟨B, B', i, hi, hBB', hBU⟩ := exists_conj_repM _ _ _ _ _ _ hadf.symm hU1
  rw [← hUmat] at hBU
  have hB'B : B' * B = 1 := mul_eq_one_symm hBB'
  have hU : U = B' * repM i * B := by
    calc U = B' * B * U := by rw [hB'B, Matrix.one_mul]
      _ = B' * repM i * B := by rw [Matrix.mul_assoc, hBU, ← Matrix.mul_assoc]
  have hdetB : B'.det * B.det = 1 := by rw [← Matrix.det_mul, hB'B, Matrix.det_one]
  have hdetA2' : (wA2' i).det = 1 := by
    have := congrArg Matrix.det (wA2_mul i hi)
    rwa [Matrix.det_mul, det_wA2 i hi, one_mul, Matrix.det_one] at this
  have hdetA3' : (wA3' i).det = 1 := by
    have := congrArg Matrix.det (wA3_mul i hi)
    rwa [Matrix.det_mul, det_wA3 i hi, one_mul, Matrix.det_one] at this
  have hdetconj : ∀ A : M43, A.det = 1 → (B' * A * B).det = 1 := fun A hA => by
    rw [Matrix.det_mul, Matrix.det_mul, hA, mul_one, hdetB]
  let g₂ : type_of% u := ⟨B' * wA2 i * B, hdetconj _ (det_wA2 i hi)⟩
  let g₂' : type_of% u := ⟨B' * wA2' i * B, hdetconj _ hdetA2'⟩
  let g₃ : type_of% u := ⟨B' * wA3 i * B, hdetconj _ (det_wA3 i hi)⟩
  let g₃' : type_of% u := ⟨B' * wA3' i * B, hdetconj _ hdetA3'⟩
  have hg₂ : g₂⁻¹ = g₂' := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    show (B' * wA2 i * B) * (B' * wA2' i * B) = 1
    rw [conjM_mul hBB', wA2_mul i hi, Matrix.mul_one, hB'B]
  have hg₃ : g₃⁻¹ = g₃' := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    show (B' * wA3 i * B) * (B' * wA3' i * B) = 1
    rw [conjM_mul hBB', wA3_mul i hi, Matrix.mul_one, hB'B]
  set p := u * (g₂ * u * g₂⁻¹) * (g₃ * u * g₃⁻¹) with hpdef
  have hpmat : (p : Matrix (Fin 4) (Fin 4) (ZMod 3)) = B' * wH i * B := by
    rw [hpdef, hg₂, hg₃]
    show U * ((B' * wA2 i * B) * U * (B' * wA2' i * B)) *
      ((B' * wA3 i * B) * U * (B' * wA3' i * B)) = B' * wH i * B
    rw [hU, conjM_mul hBB', conjM_mul hBB', conjM_mul hBB', conjM_mul hBB',
      conjM_mul hBB', conjM_mul hBB', wH]
  have hp13 : proj 4 (ZMod 3) p ^ 13 = 1 := by
    rw [← map_pow]
    refine proj_eq_one_iff.2 ⟨Units.mk0 (wS i) (by
      intro h0
      have := wS_pow i hi
      rw [h0] at this
      norm_num at this), Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        exact wS_pow i hi), ?_⟩
    show (p : Matrix (Fin 4) (Fin 4) (ZMod 3)) ^ 13 = Matrix.scalar (Fin 4) (wS i)
    rw [hpmat, conjM_pow hBB', wH_pow i hi, conjM_scalar hBB']
  have hp1 : proj 4 (ZMod 3) p ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 h
    have hc' : B' * wH i * B = Matrix.scalar (Fin 4) (c : ZMod 3) := by
      rw [← hpmat]
      exact hc
    exact wH_ne_scalar i hi c (eq_scalar_of_conjM hBB' hc')
  have hord : orderOf (proj 4 (ZMod 3) p) = 13 := orderOf_eq_prime hp13 hp1
  refine ⟨k⁻¹ * proj 4 (ZMod 3) g₂ * k, k⁻¹ * proj 4 (ZMod 3) g₃ * k, ?_⟩
  have hx' : x = k⁻¹ * proj 4 (ZMod 3) u * k := by rw [hpu]; group
  have hprod : x * (k⁻¹ * proj 4 (ZMod 3) g₂ * k * x * (k⁻¹ * proj 4 (ZMod 3) g₂ * k)⁻¹) *
      (k⁻¹ * proj 4 (ZMod 3) g₃ * k * x * (k⁻¹ * proj 4 (ZMod 3) g₃ * k)⁻¹) =
      (MulAut.conj k⁻¹) (proj 4 (ZMod 3) p) := by
    rw [hx', hpdef, MulAut.conj_apply]
    simp only [map_mul, map_inv]
    group
  rw [hprod, MulEquiv.orderOf_eq]
  exact hord

theorem exists_conj_mul_orderOf_eq_thirteen_of_mulEquiv {G : Type*} [Group G]
    (e : G ≃* projectiveSL 4 (ZMod 3)) (x : G) (hx : orderOf x = 3) :
    ∃ g₂ g₃ : G, orderOf (x * (g₂ * x * g₂⁻¹) * (g₃ * x * g₃⁻¹)) = 13 := by
  obtain ⟨g₂, g₃, h⟩ := exists_conj_mul_orderOf_eq_thirteen (e x) (by rw [MulEquiv.orderOf_eq, hx])
  refine ⟨e.symm g₂, e.symm g₃, ?_⟩
  rw [← MulEquiv.orderOf_eq e]
  simpa using h

@[expose] def slRingCongr {n : ℕ} {K K' : Type*} [Field K] [Field K'] (σ : K ≃+* K') :
    SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K' where
  toFun := SpecialLinearGroup.map σ.toRingHom
  invFun := SpecialLinearGroup.map σ.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

@[expose] def projectiveSLRingCongr {n : ℕ} {K K' : Type*} [Field K] [Field K'] (σ : K ≃+* K') :
    projectiveSL n K ≃* projectiveSL n K' :=
  QuotientGroup.congr (scalars n K) (scalars n K') (slRingCongr σ) (by
    rw [scalars_eq_center, scalars_eq_center]
    exact Subgroup.map_center_eq (slRingCongr σ))

theorem nonempty_mulEquiv_projectiveSL_of_lieModel {G : Type} [Group G]
    (hL : CFSG.Blueprint.LieModel G .PSL 4 3 1) : Nonempty (G ≃* projectiveSL 4 (ZMod 3)) := by
  rcases hL with ⟨-, -, K, iK, fK, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · letI := Fintype.ofFinite K
    have hcard : Fintype.card K = 3 := by
      rw [← Nat.card_eq_fintype_card, hK, pow_one]
    let σ : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hcard).symm
    exact ⟨(e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm).trans
        ((QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 4 K).symm).trans
          (projectiveSLRingCongr σ))⟩
  all_goals exact absurd h0 (by norm_num)

theorem not_psl43 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {J : Subgroup (CFSG.Quasithin.G11.GLV V)} (_hJ : CFSG.IsQuasisimple ↥J)
    (_hZ : Odd (Nat.card (Subgroup.center ↥J))) {c : CFSG.Quasithin.G11.GLV V} (hcJ : c ∈ J)
    (hc3 : orderOf c = 3) (hcZ : (⟨c, hcJ⟩ : ↥J) ∉ Subgroup.center ↥J)
    (hdim : Module.finrank (ZMod 2)
      ↥(CFSG.Quasithin.G11.commSpace (Subgroup.zpowers c) ⊤) = 2)
    (hL : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 3 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E⟩ := nonempty_mulEquiv_projectiveSL_of_lieModel hL
  set c' : ↥J := ⟨c, hcJ⟩ with hc'
  have hc'3 : orderOf c' = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hc3
  set x : ↥J ⧸ Subgroup.center ↥J := (c' : ↥J ⧸ Subgroup.center ↥J) with hxdef
  have hx3 : orderOf x = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hxdef, ← QuotientGroup.mk_pow, ← hc'3, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h
      exact hcZ ((QuotientGroup.eq_one_iff c').1 h)
  obtain ⟨γ₂, γ₃, hγ⟩ := exists_conj_mul_orderOf_eq_thirteen_of_mulEquiv E x hx3
  obtain ⟨h₂, rfl⟩ := QuotientGroup.mk_surjective γ₂
  obtain ⟨h₃, rfl⟩ := QuotientGroup.mk_surjective γ₃
  set y : ↥J := c' * (h₂ * c' * h₂⁻¹) * (h₃ * c' * h₃⁻¹) with hy
  have hy13 : orderOf (y : ↥J ⧸ Subgroup.center ↥J) = 13 := by
    rw [hy]
    simpa [hxdef] using hγ
  have h13 : 13 ∣ orderOf y := by
    rw [← hy13]
    exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center ↥J)) y
  rw [← Subgroup.orderOf_coe] at h13
  refine false_of_three_conj (h₂ := (h₂ : CFSG.Quasithin.G11.GLV V))
    (h₃ := (h₃ : CFSG.Quasithin.G11.GLV V)) hdim ?_
  simpa [hy, hc'] using h13

end CFSG.CGT.Foote82.Proof511
