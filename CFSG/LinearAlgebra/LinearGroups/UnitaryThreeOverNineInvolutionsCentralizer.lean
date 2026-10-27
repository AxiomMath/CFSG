module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsOrthogonal
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsCount

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] def blk (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A.det⁻¹, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem det_blk (A : Matrix (Fin 2) (Fin 2) F) : (blk A).det = A.det⁻¹ * A.det := by
  rw [blk, Matrix.det_fin_three, Matrix.det_fin_two]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, head_fin_const, tail_cons]
  ring

theorem det_pow_mul_det (h : UnitaryFieldData 3 1 F) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : (A.map (· ^ 3))ᵀ * A = 1) : A.det ^ 3 * A.det = 1 := by
  have := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← map_bar_eq_cube h,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, bar_eq_cube h] at this
  exact this

theorem det_ne_zero_of_unitary (h : UnitaryFieldData 3 1 F) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : (A.map (· ^ 3))ᵀ * A = 1) : A.det ≠ 0 := by
  intro h0
  have := det_pow_mul_det h hA
  rw [h0, mul_zero] at this
  exact zero_ne_one this

theorem blk_unitary (h : UnitaryFieldData 3 1 F) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : (A.map (· ^ 3))ᵀ * A = 1) : ((blk A).map (· ^ 3))ᵀ * blk A = 1 := by
  have hd := det_pow_mul_det h hA
  have e : ∀ i j, ∑ k, A k i ^ 3 * A k j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    rw [← hA, Matrix.mul_apply]
    rfl
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Fin.sum_univ_two, one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  have hinv : (A.det ^ 3)⁻¹ * A.det⁻¹ = 1 := by rw [← mul_inv, hd, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, hinv, e00, e01, e10, e11]

@[expose] noncomputable def blkSU (hF : Nat.card F = 9) (A : Matrix (Fin 2) (Fin 2) F)
    (hA : (A.map (· ^ 3))ᵀ * A = 1) : StatedSU 3 3 F :=
  ⟨⟨blk A, ((blk A).map (· ^ 3))ᵀ,
      mul_eq_one_comm.mp (blk_unitary (unitaryFieldData_of_card hF) hA),
      blk_unitary (unitaryFieldData_of_card hF) hA⟩, by
    rw [← SetLike.mem_coe, coe_statedSU hF]
    exact ⟨blk_unitary (unitaryFieldData_of_card hF) hA, by
      rw [Units.val_mk, det_blk, inv_mul_cancel₀ (det_ne_zero_of_unitary
        (unitaryFieldData_of_card hF) hA)]⟩⟩

theorem coe_blkSU (hF : Nat.card F = 9) (A : Matrix (Fin 2) (Fin 2) F)
    (hA : (A.map (· ^ 3))ᵀ * A = 1) :
    (((blkSU hF A hA : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blk A :=
  rfl

variable {h : UnitaryFieldData 3 1 F} {hF : Nat.card F = 9}

theorem gramForm_e0_left (y : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] y = y 0 := by
  rw [gramForm_one_apply, Fin.sum_univ_three]
  simp

theorem gramForm_e0_right (x : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x ![1, 0, 0] = x 0 ^ 3 := by
  rw [gramForm_one_apply, Fin.sum_univ_three]
  simp

theorem e0_mem {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) :
    (![1, 0, 0] : Fin 3 → F) ∈ L₀.1 := by
  rw [hL₀]
  exact Submodule.mem_span_singleton_self _

theorem e0_ne_zero : (![1, 0, 0] : Fin 3 → F) ≠ 0 := fun h0 => by
  simpa using congrFun h0 0

theorem coe_tauLine_e0 {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) :
    (((tauLine h hF L₀ : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![1, -1, -1] := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [tauLine_mulVec L₀ (e0_mem hL₀) e0_ne_zero, tauLin_apply, gramForm_e0_left,
    gramForm_e0_left]
  funext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]
  ring

theorem commute_diag_iff (hF : Nat.card F = 9) (g : StatedSU 3 3 F) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![1, -1, -1] =
        diagonal ![1, -1, -1] * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ↔
      ∃ A : GL (Fin 2) F, ((A : Matrix (Fin 2) (Fin 2) F).map (· ^ 3))ᵀ * A = 1 ∧
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blk A := by
  have h := unitaryFieldData_of_card hF
  have h2 := two_ne_zero' h
  set G := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  constructor
  · intro hc
    have hgK : (g : GL (Fin 3) F) ∈ (StatedSU 3 3 F : Set (GL (Fin 3) F)) := g.2
    rw [coe_statedSU hF] at hgK
    obtain ⟨hU, hdet⟩ := hgK
    rw [← hG] at hU hdet
    have hent : ∀ i j, G i j * ![(1 : F), -1, -1] j = ![(1 : F), -1, -1] i * G i j :=
      fun i j => by
        have := congrFun (congrFun hc i) j
        rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have hz : ∀ x : F, x * -1 = 1 * x → x = 0 := fun x hx => by
      have : (2 : F) * x = 0 := by linear_combination -hx
      exact (mul_eq_zero.mp this).resolve_left h2
    have hz' : ∀ x : F, x * 1 = -1 * x → x = 0 := fun x hx => by
      have : (2 : F) * x = 0 := by linear_combination hx
      exact (mul_eq_zero.mp this).resolve_left h2
    have g01 : G 0 1 = 0 := hz _ (by simpa using hent 0 1)
    have g02 : G 0 2 = 0 := hz _ (by simpa using hent 0 2)
    have g10 : G 1 0 = 0 := hz' _ (by simpa using hent 1 0)
    have g20 : G 2 0 = 0 := hz' _ (by simpa using hent 2 0)
    set A : Matrix (Fin 2) (Fin 2) F := !![G 1 1, G 1 2; G 2 1, G 2 2] with hA
    have u : ∀ i j, ∑ k, G k i ^ 3 * G k j = (1 : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
      rw [← hU, Matrix.mul_apply]
      rfl
    have hAU : (A.map (· ^ 3))ᵀ * A = 1 := by
      have u11 := u 1 1
      have u12 := u 1 2
      have u21 := u 2 1
      have u22 := u 2 2
      simp only [Fin.sum_univ_three, g01, g02, one_apply_eq,
        one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
        one_apply_ne (show (2 : Fin 3) ≠ 1 by decide)] at u11 u12 u21 u22
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination u11 | linear_combination u12 | linear_combination u21 |
          linear_combination u22
    have hdetA : G 0 0 * A.det = 1 := by
      rw [← hdet, Matrix.det_fin_three, hA, Matrix.det_fin_two_of, g01, g02, g10, g20]
      ring
    have hG00 : G 0 0 = A.det⁻¹ := eq_inv_of_mul_eq_one_left hdetA
    refine ⟨⟨A, (A.map (· ^ 3))ᵀ, mul_eq_one_comm.mp hAU, hAU⟩, hAU, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk, hA, g01, g02, g10, g20, hG00]
  · rintro ⟨A, -, hGA⟩
    rw [hGA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_centralizer_tauLine_iff {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0])
    (g : StatedSU 3 3 F) :
    g ∈ Subgroup.centralizer {(tauLine h hF L₀ : StatedSU 3 3 F)} ↔
      ∃ A : GL (Fin 2) F, ((A : Matrix (Fin 2) (Fin 2) F).map (· ^ 3))ᵀ * A = 1 ∧
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blk A := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Units.ext_iff, Subgroup.coe_mul,
    Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_tauLine_e0 hL₀]
  exact commute_diag_iff hF g

theorem card_centralizer_tauLine {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) :
    Nat.card (Subgroup.centralizer {(tauLine h hF L₀ : StatedSU 3 3 F)}) = 96 := by
  rw [← card_unitary_two hF]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun A => ⟨blkSU hF A.1 A.2,
    (mem_centralizer_tauLine_iff hL₀ _).mpr ⟨A.1, A.2, rfl⟩⟩) ⟨?_, ?_⟩)
  · rintro ⟨A, hA⟩ ⟨B, hB⟩ hAB
    have hblk : blk (A : Matrix (Fin 2) (Fin 2) F) = blk (B : Matrix (Fin 2) (Fin 2) F) :=
      congrArg (fun g : Subgroup.centralizer {(tauLine h hF L₀ : StatedSU 3 3 F)} =>
        (((g : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hAB
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have := congrFun (congrFun hblk i.succ) j.succ
    fin_cases i <;> fin_cases j <;> simpa [blk] using this
  · rintro ⟨g, hg⟩
    obtain ⟨A, hA, hgA⟩ := (mem_centralizer_tauLine_iff hL₀ g).mp hg
    exact ⟨⟨A, hA⟩, Subtype.ext (Subtype.ext (Units.ext hgA.symm))⟩

theorem orth_e0_iff (M : NonisoLine F) {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) :
    (∀ x ∈ M.1, ∀ y ∈ L₀.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0) ↔
      M.1 ≤ perpZero F := by
  constructor
  · intro hM x hx
    have := hM x hx _ (e0_mem hL₀)
    rw [gramForm_e0_right] at this
    exact mem_perpZero.mpr ((pow_eq_zero_iff (by norm_num)).mp this)
  · intro hM x hx y hy
    rw [hL₀] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [gramForm_smul_right, gramForm_e0_right, mem_perpZero.mp (hM hx)]
    ring

theorem not_le_perpZero {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) :
    ¬ L₀.1 ≤ perpZero F := fun hle => by
  simpa using mem_perpZero.mp (hle (e0_mem hL₀))

theorem ncard_involutions_centralizer {L₀ : NonisoLine F} (hL₀ : L₀.1 = F ∙ ![1, 0, 0]) :
    {g : StatedSU 3 3 F | g ∈ Subgroup.centralizer {(tauLine h hF L₀ : StatedSU 3 3 F)} ∧
      orderOf g = 2}.ncard = 7 := by
  have : Finite (NonisoLine F) :=
    Nat.finite_of_card_ne_zero (by rw [card_nonisoLine hF]; norm_num)
  have hinj : Function.Injective fun M : NonisoLine F => (tauLine h hF M : StatedSU 3 3 F) :=
    fun M N hMN => tauLine_injective (Subtype.ext hMN)
  have hnot : L₀ ∉ {M : NonisoLine F | M.1 ≤ perpZero F} := not_le_perpZero hL₀
  have hset : {g : StatedSU 3 3 F | g ∈ Subgroup.centralizer
      {(tauLine h hF L₀ : StatedSU 3 3 F)} ∧ orderOf g = 2} =
      (fun M : NonisoLine F => (tauLine h hF M : StatedSU 3 3 F)) ''
        insert L₀ {M : NonisoLine F | M.1 ≤ perpZero F} := by
    ext g
    constructor
    · rintro ⟨hgC, hg2⟩
      obtain ⟨M, hM⟩ := tauLine_surjective (h := h) (hF := hF) ⟨g, hg2⟩
      have hMg : (tauLine h hF M : StatedSU 3 3 F) = g := congrArg Subtype.val hM
      refine ⟨M, ?_, hMg⟩
      by_cases hML : M = L₀
      · exact Or.inl hML
      · right
        rw [← hMg, Subgroup.mem_centralizer_singleton_iff] at hgC
        exact (orth_e0_iff M hL₀).mp ((tauLine_commute_iff hML).mp hgC)
    · rintro ⟨M, hM, rfl⟩
      refine ⟨?_, (tauLine h hF M).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hM with rfl | hM
      · rfl
      · have hML : M ≠ L₀ := by
          rintro rfl
          exact hnot hM
        exact (tauLine_commute_iff hML).mpr ((orth_e0_iff M hL₀).mpr hM)
  have h6 : Nat.card ↥{M : NonisoLine F | M.1 ≤ perpZero F} = 6 := card_lines_perp hF
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_insert_of_notMem hnot,
    ← Nat.card_coe_set_eq, h6]

end CFSG.LinearGroups.UnitaryThreeOverNine
