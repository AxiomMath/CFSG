module

public import CFSG.LieType.Chevalley.E7Three.CentralizerFour

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KA5L CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.FourCube

open scoped MatrixGroups Pointwise

variable {K : Type} [Field K] [CharP K 2]

theorem exists_conj_HSL_of_pow_three [IsAlgClosed K] {X : SL(2, K)} (h3 : X ^ 3 = 1)
    (h1 : X ≠ 1) : ∃ (Q : SL(2, K)) (a : Kˣ), IsPrimitiveRoot a 3 ∧ Q * X * Q⁻¹ = HSL a := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨Q, hQ⟩ := CFSG.RankThree.Chevalley.exists_conj_lower_eq_zero_of_isAlgClosed X
  set Y := Q⁻¹ * X * Q with hY
  have hY3 : Y ^ 3 = 1 := by
    have := congrArg (MulAut.conj Q⁻¹) h3
    simpa [map_pow, MulAut.conj_apply, hY] using this
  have hY1 : Y ≠ 1 := by
    intro h
    apply h1
    rw [show X = Q * Y * Q⁻¹ by rw [hY]; group, h, mul_one, mul_inv_cancel]
  set p := (Y : Matrix (Fin 2) (Fin 2) K) 0 0
  set q := (Y : Matrix (Fin 2) (Fin 2) K) 0 1
  set r := (Y : Matrix (Fin 2) (Fin 2) K) 1 1
  have hYm : (Y : Matrix (Fin 2) (Fin 2) K) = !![p, q; 0, r] := by
    rw [Matrix.eta_fin_two (Y : Matrix (Fin 2) (Fin 2) K), hQ]
  have hdet : p * r = 1 := by
    have := Y.2
    rw [hYm, Matrix.det_fin_two_of] at this
    linear_combination this
  have hcube : !![p, q; 0, r] * !![p, q; 0, r] * !![p, q; 0, r] = (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) hY3
    simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one] at this
    rwa [hYm] at this
  simp only [Matrix.mul_fin_two] at hcube
  have e00 := congrFun (congrFun hcube 0) 0
  have e01 := congrFun (congrFun hcube 0) 1
  simp at e00 e01
  have hp0 : p ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hpr : p ≠ r := by
    intro hpr
    rw [← hpr] at hdet e01
    have hp1 : p = 1 := by
      have : (p + 1) * (p + 1) = 0 := by linear_combination hdet + (p + 1) * h2
      have := mul_self_eq_zero.1 this
      linear_combination this - h2
    rw [hp1] at e01 hpr
    have hq : q = 0 := by linear_combination e01 - q * h2
    apply hY1
    apply Subtype.ext
    rw [hYm, Matrix.SpecialLinearGroup.coe_one, hq, ← hpr, hp1]
    exact Matrix.one_fin_two.symm
  have hrp : r - p ≠ 0 := sub_ne_zero.2 (Ne.symm hpr)
  set s := q / (r - p) with hs
  have hU : (uSL s : SL(2, K))⁻¹ * Y * uSL s = HSL (Units.mk0 p hp0) := by
    have hUi : (uSL s : SL(2, K))⁻¹ = uSL (-s) := by
      rw [inv_eq_iff_mul_eq_one, CFSG.RankThree.PartOne.KLAY.uSL_mul_uSL, add_neg_cancel,
        CFSG.RankThree.PartOne.KLAY.uSL_zero']
    rw [hUi]
    apply Subtype.ext
    change ((uSL (-s) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (Y : Matrix (Fin 2) (Fin 2) K) *
      ((uSL s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
    rw [hYm]
    have hsr : s * (r - p) = q := div_mul_cancel₀ q hrp
    have hr : r = p⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination hdet)
    simp only [uSL, HSL, Matrix.mul_fin_two, Units.val_mk0, Units.val_inv_eq_inv_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination -hsr
    · exact hr
  refine ⟨(Q * uSL s)⁻¹, Units.mk0 p hp0, ?_, ?_⟩
  · have ha3 : (Units.mk0 p hp0) ^ 3 = 1 := Units.ext (by simpa [pow_succ] using e00)
    have ha1 : Units.mk0 p hp0 ≠ 1 := by
      intro h
      have hp1 : p = 1 := by simpa using congrArg Units.val h
      apply hpr
      rw [hp1] at hdet ⊢
      linear_combination -hdet
    have := orderOf_eq_prime ha3 ha1
    rw [← this]
    exact IsPrimitiveRoot.orderOf _
  · rw [← hU, hY]
    group

section Steinberg

variable [IsAlgClosed K]

theorem exists_conj_eq_cubeE_or_fourE {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {E : Subgroup (ModGL .E7 K)} (hEG : E ≤ adjointGroup .E7 K)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hle : cubeE ζ hζ.pow_eq_one ≤ E) :
    ∃ c ∈ (cubeSL2 K).range, E.map (MulAut.conj c).toMonoidHom = cubeE ζ hζ.pow_eq_one ∨
      E.map (MulAut.conj c).toMonoidHom = fourE ζ hζ.pow_eq_one := by
  have h3 := hζ.pow_eq_one
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hζ
  have hEC : ∀ x ∈ E, x ∈ cubeCent ζ h3 := fun x hx =>
    ⟨hEG hx, Subgroup.mem_centralizer_iff.2 fun e he => hcomm e (hle he) x hx⟩
  have hdec : ∀ x ∈ E, ∃ M : SL(2, K), cubeSL2 K M ∈ E ∧
      ∃ e ∈ cubeE ζ h3, x = cubeSL2 K M * e := by
    intro x hx
    have hx' : x ∈ ((cubeSL2 K).range : Set (ModGL .E7 K)) * (cubeE ζ h3 : Set (ModGL .E7 K)) := by
      rw [← coe_cubeCent_eq_mul hζ]
      exact hEC x hx
    obtain ⟨_, ⟨M, rfl⟩, e, he, hMe⟩ := hx'
    dsimp only at hMe
    refine ⟨M, ?_, e, he, hMe.symm⟩
    have hM : cubeSL2 K M = x * e⁻¹ := by rw [← hMe, mul_inv_cancel_right]
    rw [hM]
    exact E.mul_mem hx (E.inv_mem (hle he))
  have hcentral : ∀ (M : SL(2, K)) (e : ModGL .E7 K), e ∈ cubeE ζ h3 →
      cubeSL2 K M * e = e * cubeSL2 K M := fun M e he =>
    ((Subgroup.mem_centralizer_iff.1 (range_cubeSL2_le_cubeCent ζ h3 ⟨M, rfl⟩).2) e he).symm
  by_cases hP : ∀ M : SL(2, K), cubeSL2 K M ∈ E → M = 1
  · refine ⟨1, Subgroup.one_mem _, Or.inl ?_⟩
    have hEE : E = cubeE ζ h3 := by
      refine le_antisymm (fun x hx => ?_) hle
      obtain ⟨M, hM, e, he, rfl⟩ := hdec x hx
      rw [hP M hM, map_one, one_mul]
      exact he
    rw [hEE]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hx
    · intro hy
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  · simp only [not_forall] at hP
    obtain ⟨X, hXE, hX1⟩ := hP
    have hX3 : X ^ 3 = 1 := cubeSL2_injective hζ (by rw [map_pow, hexp _ hXE, map_one])
    obtain ⟨Q, a, ha, hQX⟩ := exists_conj_HSL_of_pow_three hX3 hX1
    refine ⟨cubeSL2 K Q, ⟨Q, rfl⟩, Or.inr ?_⟩
    have hdiag : ∀ M : SL(2, K), cubeSL2 K M ∈ E → ∃ k : ℕ, Q * M * Q⁻¹ = HSL ζ ^ k := by
      intro M hM
      have hMX : M * X = X * M :=
        cubeSL2_injective hζ (by rw [map_mul, map_mul]; exact hcomm _ hM _ hXE)
      have hc : (Q * M * Q⁻¹) * HSL a = HSL a * (Q * M * Q⁻¹) := by
        rw [← hQX]
        calc Q * M * Q⁻¹ * (Q * X * Q⁻¹) = Q * (M * X) * Q⁻¹ := by group
          _ = Q * (X * M) * Q⁻¹ := by rw [hMX]
          _ = Q * X * Q⁻¹ * (Q * M * Q⁻¹) := by group
      obtain ⟨t, ht⟩ := exists_HSL_of_commute ha hc
      have hM3 : M ^ 3 = 1 := cubeSL2_injective hζ (by rw [map_pow, hexp _ hM, map_one])
      have ht3 : (t : K) ^ 3 = 1 := by
        have h1 : (HSL t : SL(2, K)) ^ 3 = 1 := by
          rw [← ht, conj_pow, hM3, mul_one, mul_inv_cancel]
        have h2 : HSL (t ^ 3) = (1 : SL(2, K)) := by
          rw [← h1]
          exact map_pow (diagSL2 K) t 3
        have := congrFun (congrFun (congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K))
          h2) 0) 0
        simpa [HSL] using this
      obtain ⟨k, -, hk⟩ := hζK.eq_pow_of_pow_eq_one ht3
      refine ⟨k, ?_⟩
      rw [ht, show t = ζ ^ k from Units.ext (by rw [Units.val_pow_eq_pow_val, hk])]
      exact map_pow (diagSL2 K) ζ k
    have hz : cubeSL2 K (HSL ζ) ∈ fourE ζ h3 := by
      have := multiplicityWord_mem_fourE ζ h3
      rwa [multiplicityWord_eq_fourTorus ζ h3] at this
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨M, hM, e, he, rfl⟩ := hdec x hx
      obtain ⟨k, hk⟩ := hdiag M hM
      change cubeSL2 K Q * (cubeSL2 K M * e) * (cubeSL2 K Q)⁻¹ ∈ fourE ζ h3
      have hQe : e * (cubeSL2 K Q)⁻¹ = (cubeSL2 K Q)⁻¹ * e := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hcentral Q e he, mul_inv_cancel_right]
      have : cubeSL2 K Q * (cubeSL2 K M * e) * (cubeSL2 K Q)⁻¹ = cubeSL2 K (Q * M * Q⁻¹) * e := by
        rw [map_mul, map_mul, map_inv, mul_assoc (cubeSL2 K Q), mul_assoc (cubeSL2 K M), hQe]
        group
      rw [this, hk, map_pow]
      exact (fourE ζ h3).mul_mem ((fourE ζ h3).pow_mem hz k) (cubeE_le_fourE ζ h3 he)
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      change ((fourCubeHom ζ h3 f : adjointGroup .E7 K) : ModGL .E7 K) ∈
        E.map (MulAut.conj (cubeSL2 K Q)).toMonoidHom
      rw [fourCubeHom_apply, Subgroup.coe_mul, Subgroup.coe_pow]
      refine Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ ?_ _)
      · have he : ((cubeHom ζ h3 f.1 : adjointGroup .E7 K) : ModGL .E7 K) ∈ cubeE ζ h3 :=
          ⟨_, ⟨f.1, rfl⟩, rfl⟩
        refine ⟨_, hle he, ?_⟩
        change cubeSL2 K Q * _ * (cubeSL2 K Q)⁻¹ = _
        rw [hcentral Q _ he, mul_inv_cancel_right]
      ·
        have haK : IsPrimitiveRoot (a : K) 3 := IsPrimitiveRoot.coe_units_iff.2 ha
        obtain ⟨j, -, hjK⟩ := haK.eq_pow_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h3,
          Units.val_one])
        have hj : a ^ j = ζ := Units.ext (by rw [Units.val_pow_eq_pow_val, hjK])
        have hzX : (Multiplicity.multiplicityWord ζ : ModGL .E7 K) =
            cubeSL2 K Q * cubeSL2 K X ^ j * (cubeSL2 K Q)⁻¹ := by
          rw [multiplicityWord_eq_fourTorus ζ h3, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
            ← conj_pow, hQX, ← hj]
          change cubeSL2 K (HSL (a ^ j)) = _
          rw [show (HSL (a ^ j) : SL(2, K)) = HSL a ^ j from map_pow (diagSL2 K) a j]
        rw [hzX]
        exact ⟨_, E.pow_mem hXE j, rfl⟩

end Steinberg

end CFSG.LieType.Chevalley.E7Three.Centralizer

