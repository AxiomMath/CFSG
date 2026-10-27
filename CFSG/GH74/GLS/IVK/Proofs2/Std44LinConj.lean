module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix Subgroup CFSG.RankThree.CentralCover CFSG.Assembly.LowTwoRank

section Abstract

variable {S X : Type*} [Group S] [Group X]

theorem linConj_lift_involution (ρ : S →* X) (hρ : Function.Surjective ρ)
    (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {v : X} (hv : v * v = 1) :
    ∃ a : S, a * a = 1 ∧ ρ a = v := by
  obtain ⟨b, rfl⟩ := hρ v
  have hz : b * b ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul]; exact hv
  have hz3 := h3 _ hz
  refine ⟨b * (b * b), ?_, ?_⟩
  · have h1 : b * (b * b) * (b * (b * b)) = (b * b) ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h1, hz3]
  · rw [map_mul, MonoidHom.mem_ker.mp hz, mul_one]

theorem linConj_commute_of_lifts (ρ : S →* X) (hker : ρ.ker ≤ center S)
    (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a a' : S} (ha : a * a = 1) (ha' : a' * a' = 1)
    (h : ρ a * ρ a' = ρ a' * ρ a) : a * a' = a' * a := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hinv' : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'
  have ha_l : ∀ x : S, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have ha'_l : ∀ x : S, a' * (a' * x) = x := fun x => by rw [← mul_assoc, ha', one_mul]
  have hz : a * a' * a * a' ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : ρ a * ρ a' * ρ a * ρ a' = ρ a * ρ a * (ρ a' * ρ a') := by
      calc ρ a * ρ a' * ρ a * ρ a' = ρ a * (ρ a' * ρ a) * ρ a' := by group
        _ = ρ a * (ρ a * ρ a') * ρ a' := by rw [← h]
        _ = ρ a * ρ a * (ρ a' * ρ a') := by group
    simp only [map_mul] at h1 ⊢
    rw [h1, ← map_mul, ← map_mul, ha, ha', map_one, one_mul]
  have hzc := Subgroup.mem_center_iff.mp (hker hz)
  have hz3 := h3 _ hz
  have hz' : a' * a * a' * a = a * a' * a * a' := by
    have e := hzc a'
    calc a' * a * a' * a = a' * (a * a' * a * a') * a' := by
          simp only [mul_assoc, ha', mul_one]
      _ = (a * a' * a * a') * a' * a' := by rw [e]
      _ = a * a' * a * a' := by simp only [mul_assoc, ha', mul_one]
  have hz2 : (a * a' * a * a') ^ 2 = 1 := by
    rw [sq]
    calc a * a' * a * a' * (a * a' * a * a') = a * a' * a * a' * (a' * a * a' * a) := by rw [hz']
      _ = 1 := by simp only [mul_assoc, ha_l, ha'_l, ha]
  have hz1 : a * a' * a * a' = 1 := by
    calc a * a' * a * a' = (a * a' * a * a') ^ 3 * ((a * a' * a * a') ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; simp
  calc a * a' = (a * a')⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hz1)).symm
    _ = a'⁻¹ * a⁻¹ := mul_inv_rev a a'
    _ = a' * a := by rw [hinv, hinv']

end Abstract

section SL

variable {F : Type} [Field F]

theorem linConj_mem_statedSL {n : ℕ} (A : GL (Fin n) F) :
    A ∈ StatedSL n F ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem linConj_ker_pow_three (z : StatedSL 3 F)
    (hz : z ∈ (statedProjMk (StatedSL 3 F)).ker) : z ^ 3 = 1 := by
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet := (linConj_mem_statedSL (z : GL (Fin 3) F)).mp z.2
  rw [← hc] at hdet
  have hc3 : (c : F) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdet
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hc, ← map_pow]
  have : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  rw [this, map_one]
  rfl

end SL

section Eigen

variable {F : Type} [Field F]

theorem linConj_exists_mulVec_ne_zero {N : Matrix (Fin 3) (Fin 3) F} (hN : N ≠ 0) :
    ∃ x : Fin 3 → F, N *ᵥ x ≠ 0 := by
  by_contra h
  push Not at h
  apply hN
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem linConj_four_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have := mul_ne_zero h2 h2
  intro h
  apply this
  rw [show (2 : F) * 2 = 4 by norm_num]
  exact h

theorem linConj_eigenbasis {A B : Matrix (Fin 3) (Fin 3) F} (h2 : (2 : F) ≠ 0)
    (hA : A * A = 1) (hB : B * B = 1) (hAB : A * B = B * A)
    (htA : A.trace = -1) (htB : B.trace = -1) (htAB : (A * B).trace = -1) :
    ∃ M : Matrix (Fin 3) (Fin 3) F, M.det ≠ 0 ∧
      A * M = M * diagonal ![-1, -1, 1] ∧ B * M = M * diagonal ![-1, 1, -1] := by
  have h4 := linConj_four_ne_zero h2
  have hBA : B * A = A * B := hAB.symm
  have hA0 : A * ((1 - A) * (1 - B)) = -((1 - A) * (1 - B)) := by
    calc A * ((1 - A) * (1 - B)) = (A - A * A) * (1 - B) := by noncomm_ring
      _ = -((1 - A) * (1 - B)) := by rw [hA]; noncomm_ring
  have hB0 : B * ((1 - A) * (1 - B)) = -((1 - A) * (1 - B)) := by
    calc B * ((1 - A) * (1 - B)) = (B - B * A) * (1 - B) := by noncomm_ring
      _ = (1 - A) * (B - B * B) := by rw [hBA]; noncomm_ring
      _ = -((1 - A) * (1 - B)) := by rw [hB]; noncomm_ring
  have hA1 : A * ((1 - A) * (1 + B)) = -((1 - A) * (1 + B)) := by
    calc A * ((1 - A) * (1 + B)) = (A - A * A) * (1 + B) := by noncomm_ring
      _ = -((1 - A) * (1 + B)) := by rw [hA]; noncomm_ring
  have hB1 : B * ((1 - A) * (1 + B)) = (1 - A) * (1 + B) := by
    calc B * ((1 - A) * (1 + B)) = (B - B * A) * (1 + B) := by noncomm_ring
      _ = (1 - A) * (B + B * B) := by rw [hBA]; noncomm_ring
      _ = (1 - A) * (1 + B) := by rw [hB]; noncomm_ring
  have hA2 : A * ((1 + A) * (1 - B)) = (1 + A) * (1 - B) := by
    calc A * ((1 + A) * (1 - B)) = (A + A * A) * (1 - B) := by noncomm_ring
      _ = (1 + A) * (1 - B) := by rw [hA]; noncomm_ring
  have hB2 : B * ((1 + A) * (1 - B)) = -((1 + A) * (1 - B)) := by
    calc B * ((1 + A) * (1 - B)) = (B + B * A) * (1 - B) := by noncomm_ring
      _ = (1 + A) * (B - B * B) := by rw [hBA]; noncomm_ring
      _ = -((1 + A) * (1 - B)) := by rw [hB]; noncomm_ring
  have hN0 : (1 - A) * (1 - B) ≠ 0 := by
    intro h
    have h0 : ((1 - A) * (1 - B)).trace = 0 := by rw [h]; simp
    have e : (1 - A) * (1 - B) = 1 - A - B + A * B := by noncomm_ring
    rw [e] at h0
    simp [Matrix.trace_add, Matrix.trace_sub, htA, htB, htAB] at h0
    apply h4
    linear_combination h0
  have hN1 : (1 - A) * (1 + B) ≠ 0 := by
    intro h
    have h0 : ((1 - A) * (1 + B)).trace = 0 := by rw [h]; simp
    have e : (1 - A) * (1 + B) = 1 - A + B - A * B := by noncomm_ring
    rw [e] at h0
    simp [Matrix.trace_add, Matrix.trace_sub, htA, htB, htAB] at h0
    apply h4
    linear_combination h0
  have hN2 : (1 + A) * (1 - B) ≠ 0 := by
    intro h
    have h0 : ((1 + A) * (1 - B)).trace = 0 := by rw [h]; simp
    have e : (1 + A) * (1 - B) = 1 + A - B - A * B := by noncomm_ring
    rw [e] at h0
    simp [Matrix.trace_add, Matrix.trace_sub, htA, htB, htAB] at h0
    apply h4
    linear_combination h0
  obtain ⟨x₀, hx₀⟩ := linConj_exists_mulVec_ne_zero hN0
  obtain ⟨x₁, hx₁⟩ := linConj_exists_mulVec_ne_zero hN1
  obtain ⟨x₂, hx₂⟩ := linConj_exists_mulVec_ne_zero hN2
  set u₀ : Fin 3 → F := ((1 - A) * (1 - B)) *ᵥ x₀ with hu₀
  set u₁ : Fin 3 → F := ((1 - A) * (1 + B)) *ᵥ x₁ with hu₁
  set u₂ : Fin 3 → F := ((1 + A) * (1 - B)) *ᵥ x₂ with hu₂
  have hAu₀ : A *ᵥ u₀ = -u₀ := by rw [hu₀, Matrix.mulVec_mulVec, hA0, Matrix.neg_mulVec]
  have hBu₀ : B *ᵥ u₀ = -u₀ := by rw [hu₀, Matrix.mulVec_mulVec, hB0, Matrix.neg_mulVec]
  have hAu₁ : A *ᵥ u₁ = -u₁ := by rw [hu₁, Matrix.mulVec_mulVec, hA1, Matrix.neg_mulVec]
  have hBu₁ : B *ᵥ u₁ = u₁ := by rw [hu₁, Matrix.mulVec_mulVec, hB1]
  have hAu₂ : A *ᵥ u₂ = u₂ := by rw [hu₂, Matrix.mulVec_mulVec, hA2]
  have hBu₂ : B *ᵥ u₂ = -u₂ := by rw [hu₂, Matrix.mulVec_mulVec, hB2, Matrix.neg_mulVec]
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![u₀, u₁, u₂] j i with hM
  have hMv : ∀ y : Fin 3 → F, M *ᵥ y = y 0 • u₀ + y 1 • u₁ + y 2 • u₂ := by
    intro y
    ext i
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hcol : ∀ (C : Matrix (Fin 3) (Fin 3) F) (d : Fin 3 → F),
      (∀ j, C *ᵥ (![u₀, u₁, u₂] j) = d j • ![u₀, u₁, u₂] j) → C * M = M * diagonal d := by
    intro C d h
    ext i j
    have := congrFun (h j) i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simpa [hM, Matrix.mulVec, dotProduct, mul_comm] using this
  refine ⟨M, ?_, hcol A ![-1, -1, 1] ?_, hcol B ![-1, 1, -1] ?_⟩
  · intro hdet
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    rw [hMv] at hy
    have hAy : A *ᵥ (y 0 • u₀ + y 1 • u₁ + y 2 • u₂) = 0 := by rw [hy, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hAu₀, hAu₁, hAu₂] at hAy
    have h2y2 : (2 * y 2) • u₂ = 0 := by
      calc (2 * y 2) • u₂ = (y 0 • u₀ + y 1 • u₁ + y 2 • u₂) +
            (y 0 • -u₀ + y 1 • -u₁ + y 2 • u₂) := by module
        _ = 0 := by rw [hy, hAy, add_zero]
    have hy2 : y 2 = 0 := by
      rcases smul_eq_zero.mp h2y2 with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h hx₂
    rw [hy2, zero_smul, add_zero] at hy
    have hBy : B *ᵥ (y 0 • u₀ + y 1 • u₁) = 0 := by rw [hy, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hBu₀, hBu₁] at hBy
    have h2y1 : (2 * y 1) • u₁ = 0 := by
      calc (2 * y 1) • u₁ = (y 0 • u₀ + y 1 • u₁) + (y 0 • -u₀ + y 1 • u₁) := by module
        _ = 0 := by rw [hy, hBy, add_zero]
    have hy1 : y 1 = 0 := by
      rcases smul_eq_zero.mp h2y1 with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h hx₁
    rw [hy1, zero_smul, add_zero] at hy
    have hy0' : y 0 = 0 := (smul_eq_zero.mp hy).resolve_right hx₀
    apply hy0
    ext i
    fin_cases i <;> simp [hy0', hy1, hy2]
  · intro j
    fin_cases j <;> simp [hAu₀, hAu₁, hAu₂]
  · intro j
    fin_cases j <;> simp [hBu₀, hBu₁, hBu₂]

end Eigen

section GeneralLinear

variable {F : Type} [Field F]

theorem linConj_coe_oddDiag₃ :
    ((oddDiag₃ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![-1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₃]

theorem linConj_coe_oddDiag₂ :
    ((oddDiag₂ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![-1, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₂]

theorem linConj_trace_involution (h2 : (2 : F) ≠ 0) {t : GL (Fin 3) F} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hdet : (t : Matrix (Fin 3) (Fin 3) F).det = 1) :
    (t : Matrix (Fin 3) (Fin 3) F).trace = -1 := by
  obtain ⟨P, hP⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 ht2 ht1 hdet
  have h1 := Matrix.trace_units_conj' P (t : Matrix (Fin 3) (Fin 3) F)
  have h2' : ((P⁻¹ * t * P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (↑P⁻¹ : Matrix (Fin 3) (Fin 3) F) * (t : Matrix (Fin 3) (Fin 3) F) *
        (↑P : Matrix (Fin 3) (Fin 3) F) := by
    simp only [Units.val_mul]
  rw [← h2', hP, CFSG.RankThree.SubgroupLists.coe_negDiag3, Matrix.trace_diagonal,
    Fin.sum_univ_three] at h1
  rw [← h1]
  simp

theorem linConj_exists_conj (h2 : (2 : F) ≠ 0) {a a' : GL (Fin 3) F} (ha : a * a = 1)
    (ha' : a' * a' = 1) (hcomm : a * a' = a' * a) (hdet : (a : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hdet' : (a' : Matrix (Fin 3) (Fin 3) F).det = 1) (h1 : a ≠ 1) (h1' : a' ≠ 1) (hne : a ≠ a') :
    ∃ M : GL (Fin 3) F, (M : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ a * M = M * oddDiag₃ F ∧
      a' * M = M * oddDiag₂ F := by
  have hA : (a : Matrix (Fin 3) (Fin 3) F) * a = 1 := by rw [← Units.val_mul, ha, Units.val_one]
  have hB : (a' : Matrix (Fin 3) (Fin 3) F) * a' = 1 := by
    rw [← Units.val_mul, ha', Units.val_one]
  have hAB : (a : Matrix (Fin 3) (Fin 3) F) * a' = a' * a := by
    rw [← Units.val_mul, ← Units.val_mul, hcomm]
  have hmul2 : (a * a') * (a * a') = 1 := by
    calc a * a' * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [← hcomm]
      _ = a * a * (a' * a') := by group
      _ = 1 := by rw [ha, ha', one_mul]
  have hmul1 : a * a' ≠ 1 := by
    intro h
    apply hne
    have : a * a' = a * a := by rw [h, ha]
    exact (mul_left_cancel this).symm
  have hdetm : ((a * a' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdet, hdet', mul_one]
  have htA := linConj_trace_involution h2 ha h1 hdet
  have htB := linConj_trace_involution h2 ha' h1' hdet'
  have htAB := linConj_trace_involution h2 hmul2 hmul1 hdetm
  rw [Units.val_mul] at htAB
  obtain ⟨M₀, hM₀, hAM, hBM⟩ := linConj_eigenbasis h2 hA hB hAB htA htB htAB
  set δ : F := M₀.det with hδ
  set D : Matrix (Fin 3) (Fin 3) F := diagonal ![δ⁻¹, 1, 1] with hD
  have hdetD : D.det = δ⁻¹ := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have hdet1 : (M₀ * D).det = 1 := by
    rw [Matrix.det_mul, hdetD, ← hδ, mul_inv_cancel₀ hM₀]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (M₀ * D) (by rw [hdet1]; exact one_ne_zero), hdet1,
    ?_, ?_⟩
  · apply Units.ext
    show (a : Matrix (Fin 3) (Fin 3) F) * (M₀ * D) =
      (M₀ * D) * ((oddDiag₃ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [linConj_coe_oddDiag₃, ← Matrix.mul_assoc, hAM, Matrix.mul_assoc, Matrix.mul_assoc, hD,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _
  · apply Units.ext
    show (a' : Matrix (Fin 3) (Fin 3) F) * (M₀ * D) =
      (M₀ * D) * ((oddDiag₂ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [linConj_coe_oddDiag₂, ← Matrix.mul_assoc, hBM, Matrix.mul_assoc, Matrix.mul_assoc, hD,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _

end GeneralLinear

section Main

theorem linConj (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) : LinConj F := by
  intro v v' hv hv' hne hcomm
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
  have hv1 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv, sq] at this
  have hv1' : v' * v' = 1 := by
    have := pow_orderOf_eq_one v'
    rwa [hv', sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) hv1
  obtain ⟨a', ha', rfl⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) hv1'
  have hac : a * a' = a' * a := linConj_commute_of_lifts (statedProjMk (StatedSL 3 F))
    (ker_statedProjMk_le_center _) (fun z hz => linConj_ker_pow_three z hz) ha ha' hcomm
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hv
    omega
  have ha1' : a' ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hv'
    omega
  have haa : a ≠ a' := by
    rintro rfl
    exact hne rfl
  obtain ⟨M, hdetM, hM3, hM2⟩ := linConj_exists_conj h2
    (by simpa using congrArg Subtype.val ha) (by simpa using congrArg Subtype.val ha')
    (by simpa using congrArg Subtype.val hac) ((linConj_mem_statedSL _).mp a.2)
    ((linConj_mem_statedSL _).mp a'.2)
    (fun h => ha1 (Subtype.ext (by simpa using h))) (fun h => ha1' (Subtype.ext (by simpa using h)))
    (fun h => haa (Subtype.ext h))
  let m : StatedSL 3 F := ⟨M, (linConj_mem_statedSL M).mpr hdetM⟩
  have hm3 : a * m = m * ⟨oddDiag₃ F, Subgroup.subset_closure (det_oddDiag₃ F)⟩ :=
    Subtype.ext hM3
  have hm2 : a' * m = m * ⟨oddDiag₂ F, Subgroup.subset_closure (det_oddDiag₂ F)⟩ :=
    Subtype.ext hM2
  refine ⟨statedProjMk _ m⁻¹, ?_, ?_⟩
  · have e : m⁻¹ * a * m = ⟨oddDiag₃ F, Subgroup.subset_closure (det_oddDiag₃ F)⟩ := by
      rw [mul_assoc, hm3, ← mul_assoc, inv_mul_cancel, one_mul]
    calc statedProjMk _ m⁻¹ * statedProjMk _ a * (statedProjMk _ m⁻¹)⁻¹
        = statedProjMk _ (m⁻¹ * a * m) := by simp [map_mul, map_inv]
      _ = linU₀ F := by rw [e]; rfl
  · have e : m⁻¹ * a' * m = ⟨oddDiag₂ F, Subgroup.subset_closure (det_oddDiag₂ F)⟩ := by
      rw [mul_assoc, hm2, ← mul_assoc, inv_mul_cancel, one_mul]
    calc statedProjMk _ m⁻¹ * statedProjMk _ a' * (statedProjMk _ m⁻¹)⁻¹
        = statedProjMk _ (m⁻¹ * a' * m) := by simp [map_mul, map_inv]
      _ = linU₀' F := by rw [e]; rfl

end Main

end CFSG.GH74.GLS.IVK.Proofs2
