module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreDsub
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

open scoped Matrix

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

section F1

variable {F : Type} [Field F]

theorem exists_isPrimitiveRoot_nine (h : UnitaryFieldData 2 3 F) :
    ∃ ζ : F, IsPrimitiveRoot ζ 9 := by
  have := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hN : Nat.card Fˣ = 63 := by rw [Nat.card_units, h.card]; norm_num
  have hg0 : orderOf g ≠ 0 := by rw [hg]; exact Nat.card_pos.ne'
  have hm : 9 ∣ orderOf g := by rw [hg, hN]; norm_num
  refine ⟨((g ^ (orderOf g / 9) : Fˣ) : F), IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
  have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / 9))
  rwa [orderOf_pow_orderOf_div hg0 hm] at this

theorem regular_pow_nine {Y : GL (Fin 3) F} (hY : RegularU38 Y) :
    (Y : Matrix (Fin 3) (Fin 3) F) ^ 9 = 1 := by
  obtain ⟨⟨κ, hκ3, hYκ⟩, -⟩ := hY
  have h9 : (Y : Matrix (Fin 3) (Fin 3) F) ^ 9 = ((Y : Matrix (Fin 3) (Fin 3) F) ^ 3) ^ 3 := by
    rw [← pow_mul]
  rw [h9, hYκ, smul_pow, one_pow, hκ3, one_smul]

theorem pow_three_mul_comm_of_mul_eq_smul {Ym Zm Zi : Matrix (Fin 3) (Fin 3) F} {κ c : F}
    (hκ : κ ≠ 0) (hY3 : Ym ^ 3 = κ • 1) (hZi : Zm * Zi = 1) (hZ : Zm * Ym = c • (Ym * Zm)) :
    Zm ^ 3 * Ym = Ym * Zm ^ 3 := by
  have hpowY : ∀ n : ℕ, Zm * Ym ^ n = c ^ n • (Ym ^ n * Zm) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc Zm * Ym ^ (n + 1) = (Zm * Ym) * Ym ^ n := by rw [pow_succ', Matrix.mul_assoc]
        _ = (c • (Ym * Zm)) * Ym ^ n := by rw [hZ]
        _ = c • (Ym * (Zm * Ym ^ n)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = c • (Ym * (c ^ n • (Ym ^ n * Zm))) := by rw [ih]
        _ = c ^ (n + 1) • (Ym ^ (n + 1) * Zm) := by
          rw [Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, pow_succ' c, pow_succ' Ym]
  have hpowZ : ∀ n : ℕ, Zm ^ n * Ym = c ^ n • (Ym * Zm ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc Zm ^ (n + 1) * Ym = Zm * (Zm ^ n * Ym) := by rw [pow_succ', Matrix.mul_assoc]
        _ = Zm * (c ^ n • (Ym * Zm ^ n)) := by rw [ih]
        _ = c ^ n • ((Zm * Ym) * Zm ^ n) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
        _ = c ^ n • ((c • (Ym * Zm)) * Zm ^ n) := by rw [hZ]
        _ = c ^ (n + 1) • (Ym * Zm ^ (n + 1)) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, pow_succ c, pow_succ' Zm]
  have hc3 : c ^ 3 = 1 := by
    have h1 := hpowY 3
    rw [hY3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h1
    have h2 := congrArg (fun A => A * Zi) h1
    simp only [Matrix.smul_mul, Matrix.mul_assoc, hZi, Matrix.mul_one] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
    have h4 : c ^ 3 * κ = 1 * κ := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel₀ hκ h4
  rw [hpowZ 3, hc3, one_smul]

theorem exists_isometry_conj_diag (h : UnitaryFieldData 2 3 F) {Y : unitaryIsom3 h}
    (hY : (Y : GL (Fin 3) F) ^ 9 = 1) :
    ∃ (P : unitaryIsom3 h) (d : Fin 3 → F),
      (((P⁻¹ * Y * P : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.diagonal d := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_nine h
  haveI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  let Y' : primeFormUnitary h (idGram F 3) := ⟨(Y : GL (Fin 3) F), by
    rw [mem_primeFormUnitary]
    have := mem_unitaryIsom3.1 Y.2
    simpa [idGram] using this⟩
  have hY'9 : Y' ^ 9 = 1 := Subtype.ext (by simpa using hY)
  have hcomm : ∀ x ∈ Subgroup.zpowers Y', ∀ y ∈ Subgroup.zpowers Y', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self Y' a b).eq
  have hpow : ∀ x ∈ Subgroup.zpowers Y', x ^ 9 = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hY'9, one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m (n := 3) h hζ
    (by norm_num : 9 ∣ 2 ^ 3 + 1) (Subgroup.zpowers Y') hcomm hpow
  have hPmem : (P : GL (Fin 3) F) ∈ unitaryIsom3 h := by
    have := mem_primeFormUnitary.1 P.2
    rw [mem_unitaryIsom3]
    simpa [idGram] using this
  have hdiag := hP Y' (Subgroup.mem_zpowers Y')
  refine ⟨⟨P, hPmem⟩, fun i => (((P⁻¹ * Y' * P : primeFormUnitary h (idGram F 3)) :
    GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i, ?_⟩
  exact ((Matrix.isDiag_iff_diagonal_diag _).1 hdiag).symm

theorem exists_quadratic_of_eq {d : Fin 3 → F} {i j : Fin 3} (hij : i ≠ j) (hd : d i = d j) :
    ∃ a b : F, ∀ m, d m ^ 2 = a * d m + b := by
  have h3 : ∀ i j : Fin 3, i ≠ j →
      ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ m : Fin 3, m = i ∨ m = j ∨ m = k := by decide
  obtain ⟨k, -, -, hm⟩ := h3 i j hij
  refine ⟨d i + d k, -(d i * d k), fun m => ?_⟩
  rcases hm m with hmi | hmj | hmk
  · rw [hmi]; ring
  · rw [hmj, ← hd]; ring
  · rw [hmk]; ring

theorem injective_of_not_quadratic {Ym Q Qi : Matrix (Fin 3) (Fin 3) F} {d : Fin 3 → F}
    (hQ : Q * Qi = 1) (hQi : Qi * Q = 1) (hD : Qi * Ym * Q = Matrix.diagonal d)
    (hY : ¬ ∃ a b : F, Ym ^ 2 = a • Ym + b • 1) : Function.Injective d := by
  intro i j hij
  by_contra hne
  apply hY
  obtain ⟨a, b, hk⟩ := exists_quadratic_of_eq hne hij
  have cl2 : ∀ C : Matrix (Fin 3) (Fin 3) F, Qi * (Q * C) = C := fun C => by
    rw [← Matrix.mul_assoc, hQi, Matrix.one_mul]
  have hYm : Ym = Q * Matrix.diagonal d * Qi := by
    rw [← hD]
    calc Ym = (Q * Qi) * Ym * (Q * Qi) := by rw [hQ, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Qi * Ym * Q) * Qi := by simp only [Matrix.mul_assoc]
  have hD2 : Matrix.diagonal d ^ 2 =
      a • Matrix.diagonal d + b • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.diagonal_pow, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul,
      Matrix.diagonal_add]
    congr 1
    funext k
    simp [hk k]
  have h2 : Ym ^ 2 = Q * (Matrix.diagonal d ^ 2) * Qi := by
    rw [hYm, pow_two, pow_two]
    simp only [Matrix.mul_assoc, cl2]
  refine ⟨a, b, ?_⟩
  rw [h2, hD2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hQ, ← hYm]

theorem eq_diagonal_of_commute_of_injective {d : Fin 3 → F} (hd : Function.Injective d)
    {M : Matrix (Fin 3) (Fin 3) F} (hM : M * Matrix.diagonal d = Matrix.diagonal d * M) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · have h1 := congrFun (congrFun hM i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : M i j * (d j - d i) = 0 := by
      calc M i j * (d j - d i) = M i j * d j - d i * M i j := by ring
        _ = 0 := by rw [h1, sub_self]
    have h3 : d j - d i ≠ 0 := sub_ne_zero.2 (fun h => hij (hd h.symm))
    rw [Matrix.diagonal_apply_ne _ hij]
    exact (mul_eq_zero.1 h2).resolve_right h3

theorem diagonal_pow_nine_of_isometry (h : UnitaryFieldData 2 3 F) {w : Fin 3 → F}
    (hw : ((Matrix.diagonal w).map h.bar)ᵀ * Matrix.diagonal w = 1) :
    Matrix.diagonal w ^ 9 = 1 := by
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hw
  have hw' := Matrix.diagonal_injective hw
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h1 := congrFun hw' i
  simp only [UnitaryFieldData.bar_apply] at h1
  calc (w ^ 9) i = w i ^ 9 := rfl
    _ = w i ^ 2 ^ 3 * w i := by ring
    _ = 1 := h1

theorem coe_mul_inv_isom (h : UnitaryFieldData 2 3 F) (P : unitaryIsom3 h) :
    ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((P⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

theorem coe_inv_mul_isom (h : UnitaryFieldData 2 3 F) (P : unitaryIsom3 h) :
    (((P⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
  rfl

end F1

theorem exists_pow_three_pow_eq_one_of_normalizes_regular {F : Type} [Field F]
    (h : UnitaryFieldData 2 3 F) {Y Z : unitaryIsom3 h}
    (hY : RegularU38 (Y : GL (Fin 3) F))
    (hZ : ∃ c : Fˣ, (Z : GL (Fin 3) F) * Y * (Z : GL (Fin 3) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * Y) :
    ∃ n : ℕ, (Z : GL (Fin 3) F) ^ (3 ^ n) = 1 := by
  obtain ⟨c, hc⟩ := hZ
  have hY9 : ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 9 = 1 := regular_pow_nine hY
  have hY9' : (Y : GL (Fin 3) F) ^ 9 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hY9]; rfl)
  obtain ⟨⟨κ, hκ3, hYκ⟩, hYreg⟩ := hY
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hκ3
  set Ym : Matrix (Fin 3) (Fin 3) F := ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  set Zm : Matrix (Fin 3) (Fin 3) F := ((Z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  set Zi : Matrix (Fin 3) (Fin 3) F :=
    (((Z⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hZZi : Zm * Zi = 1 := coe_mul_inv_isom h Z
  have hZiZ : Zi * Zm = 1 := coe_inv_mul_isom h Z
  have hZmat : Zm * Ym * Zi = (c : F) • Ym := by
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hc
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    exact this.trans (by rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul])
  have hZY : Zm * Ym = (c : F) • (Ym * Zm) := by
    have h1 := congrArg (fun A => A * Zm) hZmat
    simp only [Matrix.smul_mul, Matrix.mul_assoc, hZiZ, Matrix.mul_one] at h1
    exact h1
  have hcomm : Zm ^ 3 * Ym = Ym * Zm ^ 3 := pow_three_mul_comm_of_mul_eq_smul hκ0 hYκ hZZi hZY
  obtain ⟨P, d, hPd⟩ := exists_isometry_conj_diag h hY9'
  set Q : Matrix (Fin 3) (Fin 3) F := ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  set Qi : Matrix (Fin 3) (Fin 3) F :=
    (((P⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hQQi : Q * Qi = 1 := coe_mul_inv_isom h P
  have hQiQ : Qi * Q = 1 := coe_inv_mul_isom h P
  have cl1 : ∀ C : Matrix (Fin 3) (Fin 3) F, Q * (Qi * C) = C := fun C => by
    rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
  have hD : Qi * Ym * Q = Matrix.diagonal d := by
    rw [← hPd, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hdinj : Function.Injective d := injective_of_not_quadratic hQQi hQiQ hD hYreg
  set W' : unitaryIsom3 h := P⁻¹ * Z ^ 3 * P with hW'
  have hW'm : ((W' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Qi * Zm ^ 3 * Q := by
    rw [hW', Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Subgroup.coe_pow,
      Units.val_pow_eq_pow_val]
  have hcommD : ((W' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal d =
      Matrix.diagonal d * ((W' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hW'm, ← hD]
    have e1 : Qi * Zm ^ 3 * Q * (Qi * Ym * Q) = Qi * (Zm ^ 3 * Ym) * Q := by
      simp only [Matrix.mul_assoc, cl1]
    have e2 : Qi * Ym * Q * (Qi * Zm ^ 3 * Q) = Qi * (Ym * Zm ^ 3) * Q := by
      simp only [Matrix.mul_assoc, cl1]
    rw [e1, e2, hcomm]
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F,
      ((W' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal w :=
    ⟨_, eq_diagonal_of_commute_of_injective hdinj hcommD⟩
  have hW'unit := mem_unitaryIsom3.1 W'.2
  rw [hw] at hW'unit
  have h9 : ((W' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 9 = 1 := by
    rw [hw]
    exact diagonal_pow_nine_of_isometry h hW'unit
  have hW'9 : W' ^ 9 = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]; exact h9))
  have hZeq : Z ^ 3 = P * W' * P⁻¹ := by rw [hW']; group
  have h27 : Z ^ 27 = 1 := by
    rw [show (27 : ℕ) = 3 * 9 from rfl, pow_mul, hZeq, conj_pow, hW'9]
    group
  refine ⟨3, ?_⟩
  have h27' : ((Z ^ 27 : unitaryIsom3 h) : GL (Fin 3) F) = 1 := by rw [h27]; rfl
  rw [Subgroup.coe_pow] at h27'
  exact h27'

theorem inf_centralizer_eq_bot_of_regular {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    {Y : unitaryIsom3 h} (hY : RegularU38 (Y : GL (Fin 3) F))
    (T : Subgroup (MulAut (unitarySU 2 3 F 3))) (hT : ¬ 3 ∣ Nat.card T)
    (hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z) :
    T ⊓ Subgroup.centralizer ({suConj h Y} : Set (MulAut (unitarySU 2 3 F 3))) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  obtain ⟨htT, htc⟩ := Subgroup.mem_inf.1 ht
  have htc' : t * suConj h Y = suConj h Y * t := by
    have := Subgroup.mem_centralizer_singleton_iff.1 htc
    exact this
  have hcop : Nat.Coprime 3 (orderOf t) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (fun h3 => hT (h3.trans (Subgroup.orderOf_dvd_natCard T htT)))
  obtain ⟨W, rfl⟩ := mem_range_suConj_of_coprime h hcop (hTZ t htT)
  have h1 : suConj h (W * Y) = suConj h (Y * W) := by rw [map_mul, map_mul]; exact htc'
  obtain ⟨lam, hlam⟩ := exists_matrix_eq_smul_of_suConj_eq h h1
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hlam
    exact Units.ne_zero ((W * Y : unitaryIsom3 h) : GL (Fin 3) F) hlam
  have hZ : ∃ c : Fˣ, (W : GL (Fin 3) F) * (Y : GL (Fin 3) F) * (W : GL (Fin 3) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * (Y : GL (Fin 3) F) := by
    refine ⟨Units.mk0 lam hlam0, Units.ext ?_⟩
    have hWY : ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        lam • (((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
      have := hlam
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul] at this
      exact this
    rw [Units.val_mul, Units.val_mul, hWY, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul]
  obtain ⟨n, hn⟩ := exists_pow_three_pow_eq_one_of_normalizes_regular h hY hZ
  have hWn : W ^ (3 ^ n) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hn)
  have ht1 : suConj h W ^ (3 ^ n) = 1 := by rw [← map_pow, hWn, map_one]
  have hdvd : orderOf (suConj h W) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one ht1
  have : orderOf (suConj h W) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop.symm) hdvd
  exact orderOf_eq_one_iff.1 this

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
