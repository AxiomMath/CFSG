module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompUnitary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix
open CFSG.Open (StatedClassicalModel StatedProj StatedScalars)
open CFSG.Open.StatedAPI (statedProj_mk_eq_iff statedScalars_subgroupOf_le_center
  pow_three_eq_one_of_mem_statedScalars det_of_mem_statedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3 unitarySU_le_unitaryIsom3)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd (adjU_mul adjU_smul
  det_mem_rootsOfUnityU)

section Abstract

variable {G H : Type*} [Group G] [Group H]

theorem twIsConj_map_iff (e : G ≃* H) {a b : G} : IsConj (e a) (e b) ↔ IsConj a b :=
  ⟨fun h => by simpa using e.symm.toMonoidHom.map_isConj h,
    fun h => e.toMonoidHom.map_isConj h⟩

theorem twIsConj_inv {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, conj_inv.symm⟩

theorem twIsConj_apply_of_cube_inner
    (hR : ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → x ≠ 1 → y ≠ 1 → IsConj x x⁻¹ → IsConj y y⁻¹ →
      IsConj x y)
    (hN : ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → ¬ IsConj x x⁻¹ → ¬ IsConj y y⁻¹ →
      IsConj x y ∨ IsConj x⁻¹ y)
    (ψ : MulAut G) (hψ : ∃ g : G, ∀ y, ψ (ψ (ψ y)) = g * y * g⁻¹) {x : G} (hx : x ^ 3 = 1) :
    IsConj x (ψ x) := by
  have hψ3 : ψ x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  by_cases hr : IsConj x x⁻¹
  · by_cases h1 : x = 1
    · rw [h1, map_one]
    · refine hR x (ψ x) hx hψ3 h1 ((MulEquiv.map_ne_one_iff ψ).2 h1) hr ?_
      rw [← map_inv]
      exact (twIsConj_map_iff ψ).2 hr
  · have hr' : ¬ IsConj (ψ x) (ψ x)⁻¹ := fun h => hr ((twIsConj_map_iff ψ).1 (by rwa [map_inv]))
    refine (hN x (ψ x) hx hψ3 hr hr').resolve_right fun h => hr ?_
    obtain ⟨g, hg⟩ := hψ
    have h2 : IsConj x (ψ (ψ x)) := by
      have h' : IsConj (ψ x)⁻¹ (ψ (ψ x)) := by
        rw [← map_inv]
        exact (twIsConj_map_iff ψ).2 h
      have h'' := twIsConj_inv h
      rw [inv_inv] at h''
      exact h''.trans h'
    have h3 : IsConj (ψ x) x := by
      have h' := (twIsConj_map_iff ψ).2 h2
      rw [hg] at h'
      exact h'.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
    exact (h.trans h3).symm

end Abstract

section Field

variable {p n : ℕ} {F : Type} [Field F]

theorem twEq_or_eq_inv_of_pow_three {u v : F} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) : v = u ∨ v = u⁻¹ := by
  have hq : u ^ 2 + u + 1 = 0 := (mul_eq_zero.1 (by linear_combination hu :
    (u - 1) * (u ^ 2 + u + 1) = 0)).resolve_left (sub_ne_zero.2 hu1)
  have hq' : v ^ 2 + v + 1 = 0 := (mul_eq_zero.1 (by linear_combination hv :
    (v - 1) * (v ^ 2 + v + 1) = 0)).resolve_left (sub_ne_zero.2 hv1)
  rcases mul_eq_zero.1 (by linear_combination (-v) * hq + hq' + hu :
    (v - u) * (v - u ^ 2) = 0) with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_inv_of_mul_eq_one_left (by rw [sub_eq_zero.1 h]; linear_combination hu))

theorem twExists_pow_three_eq_of_nine_dvd (hF : UnitaryFieldData p n F) (h9 : 9 ∣ p ^ n + 1)
    {α : F} (hα : α ^ 3 = 1) : ∃ s : F, s ^ 3 = α ∧ hF.bar s * s = 1 := by
  have := hF.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hq := hF.one_lt_pow
  have hm : 9 ∣ orderOf g := by
    rw [hg, Nat.card_units, hF.card_eq_sq]
    have hsq : (p ^ n) ^ 2 - 1 = (p ^ n + 1) * (p ^ n - 1) := by
      zify [hq.le, Nat.one_le_pow 2 (p ^ n) (by omega)]
      ring
    rw [hsq]
    exact Dvd.dvd.mul_right h9 _
  have hg0 : orderOf g ≠ 0 := by rw [hg]; exact Nat.card_pos.ne'
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, IsPrimitiveRoot ζ 9 := by
    refine ⟨((g ^ (orderOf g / 9) : Fˣ) : F), IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
    have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / 9))
    rwa [orderOf_pow_orderOf_div hg0 hm] at this
  have hω : IsPrimitiveRoot (ζ ^ 3) 3 := hζ.pow_of_dvd (p := 3) (by norm_num) (by norm_num)
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one hα
  refine ⟨ζ ^ i, by rw [← hi]; ring, ?_⟩
  obtain ⟨k, hk⟩ := h9
  rw [mul_comm, ← UnitaryFieldData.norm, hF.norm_eq_pow, hk]
  calc (ζ ^ i) ^ (9 * k) = ((ζ ^ 9) ^ k) ^ i := by ring
    _ = 1 := by rw [hζ.pow_eq_one, one_pow, one_pow]

end Field

section Diag

variable {p n : ℕ} {F : Type} [Field F]

theorem twPow_three_eq_of_mul_eq_diagonal {A P L : Matrix (Fin 3) (Fin 3) F} {α : F}
    {e : Fin 3 → F} (hLP : L * P = 1) (hA3 : A ^ 3 = α • 1) (hAP : A * P = P * diagonal e)
    (i : Fin 3) : e i ^ 3 = α := by
  have h1 : P * diagonal e ^ 3 = A ^ 3 * P := SemiconjBy.pow_right hAP.symm 3
  rw [hA3, Matrix.smul_mul, Matrix.one_mul, Matrix.diagonal_pow] at h1
  have h2 : diagonal (e ^ 3) = α • (1 : Matrix (Fin 3) (Fin 3) F) := by
    calc diagonal (e ^ 3) = L * (P * diagonal (e ^ 3)) := by
          rw [← Matrix.mul_assoc, hLP, Matrix.one_mul]
      _ = α • 1 := by rw [h1, Matrix.mul_smul, hLP]
  simpa using congrFun (congrFun h2 i) i

theorem twDet_eq_of_mul_eq_diagonal {A P L : Matrix (Fin 3) (Fin 3) F} {e : Fin 3 → F}
    (hLP : L * P = 1) (hAP : A * P = P * diagonal e) : A.det = e 0 * e 1 * e 2 := by
  have hP : P.det ≠ 0 := fun h0 => by
    have h := congrArg Matrix.det hLP
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h
    exact zero_ne_one h
  have h := congrArg Matrix.det hAP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three,
    mul_comm A.det] at h
  exact mul_left_cancel₀ hP h

theorem twMul_submatrix_eq {A P : Matrix (Fin 3) (Fin 3) F} {e : Fin 3 → F}
    (hAP : A * P = P * diagonal e) (τ : Equiv.Perm (Fin 3)) :
    A * P.submatrix id τ = P.submatrix id τ * diagonal (e ∘ τ) := by
  rw [← Matrix.submatrix_diagonal_equiv, ← Matrix.submatrix_mul _ _ _ _ _ τ.bijective, ← hAP,
    Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_id_id]

theorem twAdj_submatrix_mul (hF : UnitaryFieldData p n F) {P : Matrix (Fin 3) (Fin 3) F}
    (hPu : (P.map hF.bar)ᵀ * P = 1) (τ : Equiv.Perm (Fin 3)) :
    ((P.submatrix id τ).map hF.bar)ᵀ * P.submatrix id τ = 1 := by
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hPu, Matrix.submatrix_one_equiv]

theorem twExists_unitary_mul_eq_diagonal (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {A : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map hF.bar)ᵀ * A = 1) {α s : F}
    (hA3 : A ^ 3 = α • 1) (hs : s ^ 3 = α) (hsu : hF.bar s * s = 1) :
    ∃ (P : Matrix (Fin 3) (Fin 3) F) (e : Fin 3 → F), (P.map hF.bar)ᵀ * P = 1 ∧
      A * P = P * diagonal e := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hsu
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 3) (Fin 3) F, S = s⁻¹ • A := ⟨_, rfl⟩
  have hS3 : S ^ 3 = 1 := by
    rw [hS, smul_pow, hA3, smul_smul, ← hs, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hs0),
      one_smul]
  have hSu : (S.map hF.bar)ᵀ * S = 1 := by
    rw [hS, adjU_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu, map_inv₀, ← mul_inv,
      hsu, inv_one, one_smul]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : GL (Fin 3) F, (Sg : Matrix (Fin 3) (Fin 3) F) = S :=
    ⟨⟨S, (S.map hF.bar)ᵀ, mul_eq_one_comm.mp hSu, hSu⟩, rfl⟩
  have hSgU : Sg ∈ primeFormUnitary hF (idGram F 3) := by
    rw [mem_primeFormUnitary, hSg]
    simpa [idGram] using hSu
  obtain ⟨t, ht⟩ : ∃ t : primeFormUnitary hF (idGram F 3), (t : GL (Fin 3) F) = Sg :=
    ⟨⟨Sg, hSgU⟩, rfl⟩
  have htm : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = S := by rw [ht, hSg]
  have ht3 : t ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, htm, hS3]
    rfl
  have hcomm : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self t i j).eq
  have hpow : ∀ x ∈ Subgroup.zpowers t, x ^ 3 = 1 := by
    rintro x ⟨i, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, ht3, _root_.one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hF Nat.prime_three h3
    (Subgroup.zpowers t) hcomm hpow
  obtain ⟨Pm, hPm⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  obtain ⟨Pi, hPi⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = (((P : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  have hPPi : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPu : (Pm.map hF.bar)ᵀ * Pm = 1 := by
    rw [hPm]
    simpa [idGram] using mem_primeFormUnitary.1 P.2
  have hD : (Pi * S * Pm).IsDiag := by
    have h1 := hP t (Subgroup.mem_zpowers t)
    have h2 : ((P⁻¹ * t * P : primeFormUnitary hF (idGram F 3)) : GL (Fin 3) F) =
        (P : GL (Fin 3) F)⁻¹ * (t : GL (Fin 3) F) * (P : GL (Fin 3) F) := rfl
    rw [h2, Units.val_mul, Units.val_mul, htm, ← hPm, ← hPi] at h1
    exact h1
  have hSP : S * Pm = Pm * (Pi * S * Pm) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  have hDe : diagonal (fun i => s * (Pi * S * Pm) i i) = s • (Pi * S * Pm) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, hD hij, smul_zero]
  refine ⟨Pm, fun i => s * (Pi * S * Pm) i i, hPu, ?_⟩
  have hAS : A = s • S := by rw [hS, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  rw [hDe, Matrix.mul_smul, ← hSP, hAS, Matrix.smul_mul]

theorem twHasCyclicVec3_of_pow_three_eq_one (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {A : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map hF.bar)ᵀ * A = 1) (hA3 : A ^ 3 = 1)
    (hdet : A.det = 1) (hA : ∀ c : F, A ≠ c • 1) : HasCyclicVec3 A := by
  have hA3' : A ^ 3 = (1 : F) • 1 := by rw [hA3, one_smul]
  obtain ⟨P, e, hPu, hAP⟩ := twExists_unitary_mul_eq_diagonal hF h3 hAu hA3' (one_pow 3)
    (by rw [map_one, one_mul])
  have he := twPow_three_eq_of_mul_eq_diagonal hPu hA3' hAP
  have hd := (twDet_eq_of_mul_eq_diagonal hPu hAP).symm.trans hdet
  have hPP : P * (P.map hF.bar)ᵀ = 1 := mul_eq_one_comm.mp hPu
  have hsc : ∀ c : F, e 0 = c → e 1 = c → e 2 = c → False := fun c h0 h1 h2 => hA c (by
    have he' : e = fun _ => c := funext fun i => by fin_cases i <;> assumption
    calc A = A * P * (P.map hF.bar)ᵀ := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = c • 1 := by
        rw [hAP, he', ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mul, hPP])
  have hP : IsUnit P :=
    (Matrix.isUnit_iff_isUnit_det P).2 (Matrix.isUnit_det_of_left_inverse hPu)
  by_cases h01 : e 0 = e 1
  · rw [← h01] at hd
    exact (hsc (e 0) rfl h01.symm (by linear_combination e 0 * hd - e 2 * he 0)).elim
  by_cases h02 : e 0 = e 2
  · rw [← h02] at hd
    exact (hsc (e 0) rfl (by linear_combination e 0 * hd - e 1 * he 0) h02.symm).elim
  by_cases h12 : e 1 = e 2
  · rw [← h12] at hd
    exact (hsc (e 1) (by linear_combination e 1 * hd - e 0 * he 1) rfl h12.symm).elim
  exact hasCyclicVec3_iff.2 ⟨_, linearIndependent_cyclic_of_mul_eq hP hAP
    (linearIndependent_cyclic_diagonal h01 h02 h12)⟩

theorem twDiagonal_eq_smul {d : Fin 3 → F} {u : F} (h01 : d 0 = d 1) (h3 : d 0 ^ 3 = u)
    (hd : d 0 * d 1 * d 2 = 1) : diagonal d = d 0 • diagonal ![1, 1, u⁻¹] := by
  have hu0 : u ≠ 0 := by
    rw [← h3]
    exact pow_ne_zero 3 (left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd))
  have h2 : d 2 = d 0 * u⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hu0, ← h3]
    rw [← h01] at hd
    linear_combination d 0 * hd
  rw [← Matrix.diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp [h01, h2]

theorem twExists_unitary_mul_eq_smul_diagonal (hF : UnitaryFieldData p n F)
    (h3 : 3 ∣ p ^ n + 1) {A : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map hF.bar)ᵀ * A = 1)
    {u s : F} (hA3 : A ^ 3 = u • 1) (hu : u ≠ 1) (hdet : A.det = 1) (hs : s ^ 3 = u)
    (hsu : hF.bar s * s = 1) :
    ∃ (P : Matrix (Fin 3) (Fin 3) F) (a : F), (P.map hF.bar)ᵀ * P = 1 ∧ a ^ 3 = u ∧
      A * P = P * (a • diagonal ![1, 1, u⁻¹]) := by
  obtain ⟨P, e, hPu, hAP⟩ := twExists_unitary_mul_eq_diagonal hF h3 hAu hA3 hs hsu
  have hP : IsUnit P :=
    (Matrix.isUnit_iff_isUnit_det P).2 (Matrix.isUnit_det_of_left_inverse hPu)
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 3), e (τ 0) = e (τ 1) := by
    by_cases h01 : e 0 = e 1
    · exact ⟨1, h01⟩
    by_cases h02 : e 0 = e 2
    · refine ⟨Equiv.swap 1 2, ?_⟩
      rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide,
        show (Equiv.swap (1 : Fin 3) 2) 1 = 2 by decide]
      exact h02
    by_cases h12 : e 1 = e 2
    · refine ⟨Equiv.swap 0 2, ?_⟩
      rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 by decide,
        show (Equiv.swap (0 : Fin 3) 2) 1 = 1 by decide]
      exact h12.symm
    have hcyc : HasCyclicVec3 A := hasCyclicVec3_iff.2 ⟨_, linearIndependent_cyclic_of_mul_eq hP
      hAP (linearIndependent_cyclic_diagonal h01 h02 h12)⟩
    exact absurd ((hcyc.det_eq hA3).symm.trans hdet) hu
  have hAP' := twMul_submatrix_eq hAP τ
  have hPu' := twAdj_submatrix_mul hF hPu τ
  have he0 := twPow_three_eq_of_mul_eq_diagonal hPu' hA3 hAP' 0
  refine ⟨P.submatrix id τ, (e ∘ τ) 0, hPu', he0, ?_⟩
  rw [hAP', twDiagonal_eq_smul (d := e ∘ τ) hτ he0
    ((twDet_eq_of_mul_eq_diagonal hPu' hAP').symm.trans hdet)]

theorem twConj_of_mul_eq_smul (hF : UnitaryFieldData p n F)
    {A B P R D : Matrix (Fin 3) (Fin 3) F} {a b : F} (hb : b ≠ 0)
    (hPu : (P.map hF.bar)ᵀ * P = 1) (hAP : A * P = P * (a • D)) (hBR : B * R = R * (b • D)) :
    R * (P.map hF.bar)ᵀ * A = (a / b) • (B * (R * (P.map hF.bar)ᵀ)) := by
  have hPP : P * (P.map hF.bar)ᵀ = 1 := mul_eq_one_comm.mp hPu
  have hA : A = a • (P * D * (P.map hF.bar)ᵀ) := by
    calc A = A * P * (P.map hF.bar)ᵀ := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = a • (P * D * (P.map hF.bar)ᵀ) := by rw [hAP, Matrix.mul_smul, Matrix.smul_mul]
  have hB : B * R = b • (R * D) := by rw [hBR, Matrix.mul_smul]
  rw [hA, Matrix.mul_smul, ← Matrix.mul_assoc B, hB, Matrix.smul_mul, smul_smul,
    div_mul_cancel₀ a hb]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc R, hPu, Matrix.mul_one]

end Diag

section Classes

variable {p n : ℕ} {F : Type} [Field F]

theorem twCoe_pow_three (x : unitarySU p n F 3) :
    (((x ^ 3 : unitarySU p n F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem twPow_three_eq_one_of_mem {z : unitarySU p n F 3}
    (hz : z ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3)) : z ^ 3 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_three_eq_one_of_mem_statedScalars hz (det_of_mem_statedSU z.2))

theorem twMk_eq_one_of_eq_smul {x : unitarySU p n F 3} {c : F}
    (hx : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1) :
    (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) = 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h := det_of_mem_statedSU x.2
    rw [hx, zero_smul, Matrix.det_zero] at h
    exact zero_ne_one h
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 c hc, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hx, Units.val_mk0,
    Matrix.smul_one_eq_diagonal]

theorem twExists_pow_three_eq_smul {x : unitarySU p n F 3}
    (hx : x ^ 3 ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3)) :
    ∃ u : F, u ^ 3 = 1 ∧ ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = u • 1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨c, hc⟩ := hx
  have hm : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = (c : F) • 1 := by
    rw [← twCoe_pow_three, ← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  refine ⟨c, ?_, hm⟩
  have h := congrArg Matrix.det hm
  rwa [Matrix.det_pow, det_of_mem_statedSU x.2, one_pow, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin, eq_comm] at h

theorem twPow_three_eq_of_isConj {x y : unitarySU p n F 3}
    (hx : x ^ 3 ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3))
    (hxy : IsConj (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) (QuotientGroup.mk y)) :
    y ^ 3 = x ^ 3 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hc
  have hzc := statedScalars_subgroupOf_le_center _ hc
  have hxc := statedScalars_subgroupOf_le_center _ hx
  set z := (g * x * g⁻¹)⁻¹ * y with hz
  have hcomm : Commute (g * x * g⁻¹) z := Subgroup.mem_center_iff.1 hzc (g * x * g⁻¹)
  have hy : y = g * x * g⁻¹ * z := by rw [hz, mul_inv_cancel_left]
  rw [hy, hcomm.mul_pow, twPow_three_eq_one_of_mem hc, mul_one, conj_pow,
    Subgroup.mem_center_iff.1 hxc g, mul_inv_cancel_right]

theorem twPow_three_eq_one_of_isConj_inv {x : unitarySU p n F 3}
    (hx : x ^ 3 ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3))
    (h : IsConj (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) (QuotientGroup.mk x⁻¹)) :
    x ^ 3 = 1 := by
  have h1 : (x ^ 3)⁻¹ = x ^ 3 := by
    rw [← inv_pow]
    exact twPow_three_eq_of_isConj hx h
  have hzz : x ^ 3 * x ^ 3 = 1 := mul_eq_one_iff_eq_inv.2 h1.symm
  calc x ^ 3 = (x ^ 3) ^ 3 * (x ^ 3 * x ^ 3)⁻¹ := by group
    _ = 1 := by rw [twPow_three_eq_one_of_mem hx, hzz, inv_one, one_mul]

theorem twEq_or_eq_inv_of_mem {z w : unitarySU p n F 3}
    (hz : z ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3))
    (hw : w ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3)) (hz1 : z ≠ 1)
    (hw1 : w ≠ 1) : w = z ∨ w = z⁻¹ := by
  have key : ∀ v : unitarySU p n F 3,
      v ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3) → v ≠ 1 →
      ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 3) c = v ∧ (c : F) ^ 3 = 1 ∧ (c : F) ≠ 1 := by
    intro v hv hv1
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hv
    obtain ⟨c, hc⟩ := hv
    refine ⟨c, hc, ?_, fun h => hv1 (Subtype.ext ?_)⟩
    · have h := congrArg (fun g : GL (Fin 3) F => (GeneralLinearGroup.det g : F)) hc
      simp only [GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val,
        GeneralLinearGroup.val_det_apply, det_of_mem_statedSU v.2] at h
      exact h
    · rw [← hc, Units.val_eq_one.1 h, map_one, Subgroup.coe_one]
  obtain ⟨c, hc, hc3, hc1⟩ := key z hz hz1
  obtain ⟨d, hd, hd3, hd1⟩ := key w hw hw1
  rcases twEq_or_eq_inv_of_pow_three hc3 hd3 hc1 hd1 with h | h
  · exact Or.inl (Subtype.ext (by rw [← hc, ← hd, Units.ext h]))
  · refine Or.inr (Subtype.ext ?_)
    rw [Subgroup.coe_inv, ← hc, ← hd, ← map_inv]
    congr 1
    exact Units.ext (by rw [h, Units.val_inv_eq_inv_val])

theorem twIsConj_mk_of_unitary (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    {x y : unitarySU p n F 3} {α w : F} (hw : w ≠ 0)
    (hx3 : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1)
    {g : Matrix (Fin 3) (Fin 3) F} (hgu : (g.map hF.bar)ᵀ * g = 1)
    (hgx : g * ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      w • (((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g)) :
    IsConj (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) (QuotientGroup.mk y) := by
  obtain ⟨G, hG⟩ : ∃ G : GL (Fin 3) F, (G : Matrix (Fin 3) (Fin 3) F) = g :=
    ⟨⟨g, (g.map hF.bar)ᵀ, mul_eq_one_comm.mp hgu, hgu⟩, rfl⟩
  have hGu : G ∈ unitaryIsom3 hF := mem_unitaryIsom3.2 (by rw [hG]; exact hgu)
  obtain ⟨δ, hδ, hdetδ⟩ := exists_unitaryIsom_commute_det_eq_of_pow_three hF h3
    (γ := ⟨(x : GL (Fin 3) F), unitarySU_le_unitaryIsom3 x.2⟩) hx3
    (inv_mem (det_mem_rootsOfUnityU hF hGu))
  have hGδ : G * δ ∈ unitarySU p n F 3 := (mem_unitarySU_iff hF).2 ⟨by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, hdetδ, mul_inv_cancel, Units.val_one],
    mem_unitaryIsom3.1 (mul_mem hGu δ.2)⟩
  refine isConj_iff.2 ⟨QuotientGroup.mk ⟨G * δ, hGδ⟩, ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    statedProj_mk_eq_iff]
  refine ⟨(Units.mk0 w hw)⁻¹, ?_⟩
  have hδ' : (δ : GL (Fin 3) F) * (x : GL (Fin 3) F) = (x : GL (Fin 3) F) * δ := hδ
  have hc : ((⟨G * δ, hGδ⟩ * x * ⟨G * δ, hGδ⟩⁻¹ : unitarySU p n F 3) : GL (Fin 3) F) =
      G * (x : GL (Fin 3) F) * G⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    calc G * (δ : GL (Fin 3) F) * x * (G * δ)⁻¹ =
          G * ((δ : GL (Fin 3) F) * x) * (δ : GL (Fin 3) F)⁻¹ * G⁻¹ := by group
      _ = G * (x : GL (Fin 3) F) * G⁻¹ := by rw [hδ']; group
  have hm : ((G * (x : GL (Fin 3) F) * G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      w • ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Units.val_mul, hG, hgx, Matrix.smul_mul, Matrix.mul_assoc, ← hG,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hc, hm, Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, inv_mul_cancel₀ hw, one_smul]

theorem twIsConj_mk_of_pow_three_eq_smul (hF : UnitaryFieldData p n F) (h9 : 9 ∣ p ^ n + 1)
    {x y : unitarySU p n F 3} {u : F} (hu : u ≠ 1) (hu3 : u ^ 3 = 1)
    (hx3 : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = u • 1)
    (hy3 : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = u • 1) :
    IsConj (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) (QuotientGroup.mk y) := by
  have h3 : 3 ∣ p ^ n + 1 := (by norm_num : 3 ∣ 9).trans h9
  obtain ⟨s, hs, hsu⟩ := twExists_pow_three_eq_of_nine_dvd hF h9 hu3
  obtain ⟨hxd, hxu⟩ := (mem_unitarySU_iff hF).1 x.2
  obtain ⟨hyd, hyu⟩ := (mem_unitarySU_iff hF).1 y.2
  obtain ⟨P, a, hPu, ha, hxP⟩ :=
    twExists_unitary_mul_eq_smul_diagonal hF h3 hxu hx3 hu hxd hs hsu
  obtain ⟨R, b, hRu, hb, hyR⟩ :=
    twExists_unitary_mul_eq_smul_diagonal hF h3 hyu hy3 hu hyd hs hsu
  have hu0 : u ≠ 0 := by
    rintro rfl
    norm_num at hu3
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← ha]; norm_num)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hb]; norm_num)
  have hdd : (((P.map hF.bar)ᵀ).map hF.bar)ᵀ = P := by
    ext i j
    simp [UnitaryFieldData.bar_bar]
  refine twIsConj_mk_of_unitary hF h3 (div_ne_zero ha0 hb0) hx3 (g := R * (P.map hF.bar)ᵀ) ?_
    (twConj_of_mul_eq_smul hF hb0 hPu hxP hyR)
  rw [adjU_mul, hdd, Matrix.mul_assoc, ← Matrix.mul_assoc _ R, hRu, Matrix.one_mul,
    mul_eq_one_comm.mp hPu]

theorem twIsConj_mk_of_pow_three_eq (hF : UnitaryFieldData p n F) (h9 : 9 ∣ p ^ n + 1)
    {x y : unitarySU p n F 3}
    (hx : x ^ 3 ∈ (StatedScalars (Fin 3) F).subgroupOf (unitarySU p n F 3)) (hxy : x ^ 3 = y ^ 3)
    (hx1 : (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) ≠ 1)
    (hy1 : (QuotientGroup.mk y : StatedProj (unitarySU p n F 3)) ≠ 1) :
    IsConj (QuotientGroup.mk x : StatedProj (unitarySU p n F 3)) (QuotientGroup.mk y) := by
  have h3 : 3 ∣ p ^ n + 1 := (by norm_num : 3 ∣ 9).trans h9
  obtain ⟨u, hu3, hxu⟩ := twExists_pow_three_eq_smul hx
  have hyu : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = u • 1 := by
    rw [← twCoe_pow_three, ← hxy, twCoe_pow_three, hxu]
  by_cases hu : u = 1
  · subst hu
    obtain ⟨hxd, hxU⟩ := (mem_unitarySU_iff hF).1 x.2
    obtain ⟨hyd, hyU⟩ := (mem_unitarySU_iff hF).1 y.2
    have hxc := twHasCyclicVec3_of_pow_three_eq_one hF h3 hxU (by rw [hxu, one_smul]) hxd
      fun c hc => hx1 (twMk_eq_one_of_eq_smul hc)
    have hyc := twHasCyclicVec3_of_pow_three_eq_one hF h3 hyU (by rw [hyu, one_smul]) hyd
      fun c hc => hy1 (twMk_eq_one_of_eq_smul hc)
    obtain ⟨g, hg, hgx⟩ := twExists_unitarySU_conj_of_hasCyclicVec3 hF h3
      (unitarySU_le_unitaryIsom3 x.2) (unitarySU_le_unitaryIsom3 y.2) hxu hyu
      (hxd.trans hyd.symm) hxc hyc
    refine isConj_iff.2 ⟨QuotientGroup.mk ⟨g, hg⟩, ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    rw [hgx, mul_inv_cancel_right]
  · exact twIsConj_mk_of_pow_three_eq_smul hF h9 hu hu3 hxu hyu

theorem twIsConj_of_isConj_inv (hF : UnitaryFieldData p n F) (h9 : 9 ∣ p ^ n + 1)
    {a b : StatedProj (unitarySU p n F 3)} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (har : IsConj a a⁻¹) (hbr : IsConj b b⁻¹) : IsConj a b := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at ha3 hb3
  rw [← QuotientGroup.mk_inv] at har hbr
  exact twIsConj_mk_of_pow_three_eq hF h9 ha3 ((twPow_three_eq_one_of_isConj_inv ha3 har).trans
    (twPow_three_eq_one_of_isConj_inv hb3 hbr).symm) ha1 hb1

theorem twIsConj_or_of_not_isConj_inv (hF : UnitaryFieldData p n F) (h9 : 9 ∣ p ^ n + 1)
    {a b : StatedProj (unitarySU p n F 3)} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (har : ¬ IsConj a a⁻¹) (hbr : ¬ IsConj b b⁻¹) : IsConj a b ∨ IsConj a⁻¹ b := by
  have ha1 : a ≠ 1 := fun h => har (by rw [h, inv_one])
  have hb1 : b ≠ 1 := fun h => hbr (by rw [h, inv_one])
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at ha3 hb3
  have hx1 : x ^ 3 ≠ 1 := fun h => har (by
    rw [← QuotientGroup.mk_inv]
    refine twIsConj_mk_of_pow_three_eq hF h9 ha3 (by rw [inv_pow, h, inv_one]) ha1 ?_
    rwa [QuotientGroup.mk_inv, inv_ne_one])
  have hy1 : y ^ 3 ≠ 1 := fun h => hbr (by
    rw [← QuotientGroup.mk_inv]
    refine twIsConj_mk_of_pow_three_eq hF h9 hb3 (by rw [inv_pow, h, inv_one]) hb1 ?_
    rwa [QuotientGroup.mk_inv, inv_ne_one])
  rcases twEq_or_eq_inv_of_mem ha3 hb3 hx1 hy1 with h | h
  · exact Or.inl (twIsConj_mk_of_pow_three_eq hF h9 ha3 h.symm ha1 hb1)
  · refine Or.inr ?_
    rw [← QuotientGroup.mk_inv]
    refine twIsConj_mk_of_pow_three_eq hF h9 (by rw [inv_pow]; exact inv_mem ha3)
      (by rw [inv_pow, h]) ?_ hb1
    rwa [QuotientGroup.mk_inv, inv_ne_one]

end Classes

theorem psu3_order_three_fixed_of_cube_inner
    {G : Type} [Group G] {r n : ℕ} (hG : StatedClassicalModel G .PSU 3 r n)
    (hQ : 9 ∣ r ^ n + 1) (ψ : MulAut G)
    (hψ : ∃ g : G, ∀ y, ψ (ψ (ψ y)) = g * y * g⁻¹)
    (p : G) (hp : p ^ 3 = 1) :
    ∃ j : G, ψ p = j * p * j⁻¹ := by
  obtain ⟨⟨hr, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  have hF : UnitaryFieldData r n K := ⟨hr, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hR : ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → x ≠ 1 → y ≠ 1 → IsConj x x⁻¹ → IsConj y y⁻¹ →
      IsConj x y := fun x y hx hy hx1 hy1 hxr hyr => (twIsConj_map_iff e).1
    (twIsConj_of_isConj_inv hF hQ (by rw [← map_pow, hx, map_one])
      (by rw [← map_pow, hy, map_one]) ((MulEquiv.map_ne_one_iff e).2 hx1)
      ((MulEquiv.map_ne_one_iff e).2 hy1) (by rw [← map_inv]; exact (twIsConj_map_iff e).2 hxr)
      (by rw [← map_inv]; exact (twIsConj_map_iff e).2 hyr))
  have hN : ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → ¬ IsConj x x⁻¹ → ¬ IsConj y y⁻¹ →
      IsConj x y ∨ IsConj x⁻¹ y := fun x y hx hy hxr hyr => by
    rcases twIsConj_or_of_not_isConj_inv hF hQ (a := e x) (b := e y)
      (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one])
      (by rw [← map_inv, twIsConj_map_iff]; exact hxr)
      (by rw [← map_inv, twIsConj_map_iff]; exact hyr) with h | h
    · exact Or.inl ((twIsConj_map_iff e).1 h)
    · exact Or.inr ((twIsConj_map_iff e).1 (by rwa [map_inv]))
  obtain ⟨j, hj⟩ := isConj_iff.1 (twIsConj_apply_of_cube_inner hR hN ψ hψ hp)
  exact ⟨j, hj.symm⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
