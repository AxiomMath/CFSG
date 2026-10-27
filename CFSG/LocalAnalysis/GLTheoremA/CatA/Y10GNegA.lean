module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNeg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNeg

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GU6
open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem iterate_form [Finite F] (β : ↥(StatedSU 6 (2 ^ 2) F) → ↥(StatedSU 6 (2 ^ 2) F))
    (A : GL (Fin 6) F) (φ : F ≃+* F)
    (hβ : ∀ x : ↥(StatedSU 6 (2 ^ 2) F),
      (((β x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        (A : Matrix (Fin 6) (Fin 6) F) * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map φ *
          ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
    (k : ℕ) :
    ∃ B C : Matrix (Fin 6) (Fin 6) F, B * C = 1 ∧ C * B = 1 ∧ ∀ x : ↥(StatedSU 6 (2 ^ 2) F),
      (((β^[k] x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        B * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map ((⇑φ)^[k]) * C := by
  induction k with
  | zero =>
    refine ⟨1, 1, one_mul 1, one_mul 1, fun x => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨B, C, hBC, hCB, hk⟩ := ih
    have hAinv : (A : Matrix (Fin 6) (Fin 6) F) * ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 :=
      Units.mul_inv A
    have hAinv' : ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (A : Matrix (Fin 6) (Fin 6) F) = 1 :=
      Units.inv_mul A
    have hmul : ∀ M N : Matrix (Fin 6) (Fin 6) F, (M * N).map φ = M.map φ * N.map φ :=
      fun M N => Matrix.map_mul (f := (φ : F →+* F))
    refine ⟨(A : Matrix (Fin 6) (Fin 6) F) * B.map φ,
      C.map φ * ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F), ?_, ?_, fun x => ?_⟩
    · have hBC' : B.map φ * C.map φ = 1 := by
        rw [← hmul, hBC, Matrix.map_one _ (map_zero φ) (map_one φ)]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ) (C.map φ), hBC', Matrix.one_mul, hAinv]
    · have hCB' : C.map φ * B.map φ = 1 := by
        rw [← hmul, hCB, Matrix.map_one _ (map_zero φ) (map_one φ)]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F),
        hAinv', Matrix.one_mul, hCB']
    · rw [Function.iterate_succ_apply', hβ, hk x]
      rw [hmul, hmul, Matrix.map_map]
      have hcomp : ((⇑φ) ∘ (⇑φ)^[k]) = (⇑φ)^[k + 1] := (Function.iterate_succ' _ _).symm
      rw [hcomp]
      simp only [Matrix.mul_assoc]


theorem phi_eq_id_of_iterate [Finite F] (hF : Nat.card F = (2 ^ 2) ^ 2)
    (β : ↥(StatedSU 6 (2 ^ 2) F) → ↥(StatedSU 6 (2 ^ 2) F)) (A : GL (Fin 6) F) (φ : F ≃+* F)
    (hβ : ∀ x : ↥(StatedSU 6 (2 ^ 2) F),
      (((β x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        (A : Matrix (Fin 6) (Fin 6) F) * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map φ *
          ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
    (h5 : ∀ x : ↥(StatedSU 6 (2 ^ 2) F), β^[5] x = x) : ∀ y : F, φ y = y := by
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  obtain ⟨ζ, hζ5, hζ1⟩ := exists_fifth_root_ne_one (F := F) hF16
  obtain ⟨B, C, hBC, hCB, hk⟩ := iterate_form β A φ hβ 5
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hζ0 : ζ ≠ 0 := by rintro rfl; norm_num at hζ5
  let τ : F ≃+* F := (φ : RingAut F) ^ 5
  have hτ : ∀ y, (⇑φ)^[5] y = τ y := fun y => (ringAut_pow_apply φ 5 y).symm
  let t : Fin 6 → F := ![ζ, ζ, ζ, 1, 1, ζ ^ 2]
  have ht : ∀ k, t k ≠ 0 := by
    intro k
    fin_cases k <;> simp [t, hζ0]
  have ht5 : ∀ k, t k ^ 5 = 1 := by
    intro k
    fin_cases k
    · show ζ ^ 5 = 1
      exact hζ5
    · show ζ ^ 5 = 1
      exact hζ5
    · show ζ ^ 5 = 1
      exact hζ5
    · show (1 : F) ^ 5 = 1
      exact one_pow 5
    · show (1 : F) ^ 5 = 1
      exact one_pow 5
    · show (ζ ^ 2) ^ 5 = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  have hdet : ∏ k, t k = 1 := by
    rw [Fin.prod_univ_six]
    simp only [t, Matrix.cons_val, Fin.isValue]
    have : ζ * ζ * ζ * 1 * 1 * ζ ^ 2 = ζ ^ 5 := by ring
    rw [this, hζ5]
  have hD : diagU t ht ∈ StatedSU 6 (2 ^ 2) F := diagU_mem_SU hF ht ht5 hdet
  let Dsu : ↥(StatedSU 6 (2 ^ 2) F) := ⟨diagU t ht, hD⟩
  have h1 := hk Dsu
  rw [h5 Dsu, diagU_val] at h1
  have hφ0 : (⇑φ)^[5] 0 = 0 := Function.iterate_fixed (map_zero φ) 5
  have htr := congrArg Matrix.trace h1
  rw [Matrix.trace_mul_cycle, hCB, Matrix.one_mul, Matrix.diagonal_map hφ0, Matrix.trace_diagonal,
    Matrix.trace_diagonal] at htr
  simp only [t, Function.comp_apply, Fin.sum_univ_six, Matrix.cons_val, Fin.isValue] at htr
  have h1' : (⇑φ)^[5] 1 = 1 := Function.iterate_fixed (map_one φ) 5
  simp only [hτ, map_pow, map_one] at htr
  have hu5 : (τ ζ) ^ 5 = 1 := by rw [← map_pow, hζ5, map_one]
  have hE : (τ ζ + ζ) * (τ ζ + ζ + 1) = 0 := by
    linear_combination (-1 : F) * htr + ((ζ ^ 2) + 2 * ζ - τ ζ + τ ζ * ζ) * h2
  have hcase : τ ζ = ζ := by
    rcases mul_eq_zero.1 hE with h | h
    · linear_combination h - ζ * h2
    · exfalso
      have hu : τ ζ = ζ + 1 := by linear_combination h - (ζ + 1) * h2
      rw [hu] at hu5
      have hΦ1 : (ζ + 1) ^ 4 + (ζ + 1) ^ 3 + (ζ + 1) ^ 2 + (ζ + 1) + 1 = 0 := by
        apply mul_left_cancel₀ hζ0
        linear_combination hu5
      have hΦ0 : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
        have hne : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
        apply mul_left_cancel₀ hne
        linear_combination hζ5
      have hz : ζ * (ζ + 1) = 0 := by
        linear_combination hΦ1 - hΦ0 - (2 * ζ ^ 3 + 4 * ζ ^ 2 + 4 * ζ + 2) * h2
      rcases mul_eq_zero.1 hz with h0 | h0
      · exact hζ0 h0
      · exact hζ1 (by linear_combination h0 - h2)
  have hfix : (⇑φ)^[5] ζ = ζ := by rw [hτ, hcase]
  have h5' : ∀ x, (⇑φ)^[5] x = x := iterate_five_eq_id hF16 φ hζ5 hζ1 hfix
  exact fun y => ringEquiv_eq_id_of_iterate_five hF16 φ h5' y


theorem conj_iterate_form [Finite F] (β : MulAut ↥(StatedSU 6 (2 ^ 2) F)) (A : GL (Fin 6) F)
    (hβ : ∀ x : ↥(StatedSU 6 (2 ^ 2) F),
      ((β x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) = A * ((x : GL (Fin 6) F)) * A⁻¹)
    (k : ℕ) (x : ↥(StatedSU 6 (2 ^ 2) F)) :
    ((((⇑β)^[k] x : ↥(StatedSU 6 (2 ^ 2) F))) : GL (Fin 6) F) =
      A ^ k * ((x : GL (Fin 6) F)) * (A ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', hβ, ih, pow_succ A k, _root_.mul_inv_rev]
    group


section Main


theorem i14NegPieceA_of_matrix (hM : U6SevenFree) : I14NegPieceA := by
  intro S _ _ p α J labK labJ hp hp2 hZ hK hJ hα hcomp hlab hp5
  subst hlab
  subst hp5
  intro hAlab
  obtain ⟨tg, rk, nn⟩ := labJ
  obtain ⟨h1, h2, h3⟩ := hAlab
  simp only at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨hQJ, hcardJ⟩ := label_A32_card hJ
  obtain ⟨-, hQS, -⟩ := hasLabel_model hK
  have hSimple : IsSimpleGroup S := by
    have e1 : (S ⧸ Subgroup.center S) ≃* (S ⧸ (⊥ : Subgroup S)) := QuotientGroup.quotientMulEquivOfEq hZ
    have hq : IsSimpleGroup (S ⧸ (⊥ : Subgroup S)) := e1.isSimpleGroup_congr.1 hQS.2
    exact (QuotientGroup.quotientBot : S ⧸ (⊥ : Subgroup S) ≃* S).isSimpleGroup_congr.1 hq
  obtain ⟨F, hFf, hDE, hCh, hFin, hF, ⟨Φ⟩⟩ := transport_twA52 hK hZ
  let β : MulAut ↥(StatedSU 6 (2 ^ 2) F) := Φ.symm.trans (α.trans Φ)
  have hβΦ : ∀ x, β x = Φ (α (Φ.symm x)) := fun x => rfl
  have hβiter : ∀ (k : ℕ) (x : ↥(StatedSU 6 (2 ^ 2) F)), (⇑β)^[k] x = Φ ((α ^ k) (Φ.symm x)) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, hβΦ, MulEquiv.symm_apply_apply, pow_succ' α k, MulAut.mul_apply]
  have h5β : ∀ x, (⇑β)^[5] x = x := by
    intro x
    rw [hβiter, hα, MulAut.one_apply, MulEquiv.apply_symm_apply]
  obtain ⟨A, hAuni, φ, hβform⟩ := transport_fix hF β
  have hφ : ∀ y : F, φ y = y := phi_eq_id_of_iterate hF β A φ hβform h5β
  have hφfun : (⇑φ) = id := funext hφ
  have hβGL : ∀ x : ↥(StatedSU 6 (2 ^ 2) F),
      ((β x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) = A * ((x : GL (Fin 6) F)) * A⁻¹ := by
    intro x
    apply Units.ext
    rw [hβform x, hφfun, Matrix.map_id, Units.val_mul, Units.val_mul]
  have hA5comm : ∀ x ∈ StatedSU 6 (2 ^ 2) F, (A ^ 5 : GL (Fin 6) F) * x = x * A ^ 5 := by
    intro x hx
    have h1 := conj_iterate_form β A hβGL 5 ⟨x, hx⟩
    rw [h5β] at h1
    have h1' : x = A ^ 5 * x * (A ^ 5)⁻¹ := h1
    calc (A ^ 5 : GL (Fin 6) F) * x = (A ^ 5 * x * (A ^ 5)⁻¹) * A ^ 5 := by group
      _ = x * A ^ 5 := by rw [← h1']
  obtain ⟨c5, hc5⟩ := commutant_scalar hF (A ^ 5) hA5comm
  have hA5mat : (A : Matrix (Fin 6) (Fin 6) F) ^ 5 = c5 • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hc5
  by_cases hAs : ∃ c : F, (A : Matrix (Fin 6) (Fin 6) F) = c • 1
  ·
    obtain ⟨c, hc⟩ := hAs
    have hcommA : ∀ g : GL (Fin 6) F, A * g = g * A := by
      intro g
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hc]
      simp [Matrix.smul_mul, Matrix.mul_smul]
    have hβid : ∀ x, β x = x := by
      intro x
      apply Subtype.ext
      rw [hβGL, hcommA, mul_assoc, mul_inv_cancel, mul_one]
    have hαid : ∀ s : S, α s = s := by
      intro s
      have h := hβid (Φ s)
      rw [hβΦ, MulEquiv.symm_apply_apply] at h
      exact Φ.injective h
    have hX : fixSubgroup α = ⊤ := by
      rw [eq_top_iff]
      intro s _
      rw [mem_fixSubgroup]
      exact hαid s
    have hsub := hcomp.2.1
    rw [hX] at hsub
    rcases subnormal_eq_top_of_top hSimple hsub rfl with hJbot | hJtop
    · subst hJbot
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (↥(⊥ : Subgroup S)))
      rw [hcardJ, Subgroup.card_bot] at h1
      have hdvd : 4 ^ 6 * (15 * 63 * 255) ∣ 1 := ⟨_, h1⟩
      norm_num at hdvd
    · subst hJtop
      have hcz : Subgroup.center ↥(⊤ : Subgroup S) = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        rw [Subgroup.mem_bot]
        have hzC : (z : S) ∈ Subgroup.center S := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := (Subgroup.mem_center_iff.1 hz) ⟨g, Subgroup.mem_top g⟩
          exact congrArg Subtype.val this
        rw [hZ, Subgroup.mem_bot] at hzC
        exact Subtype.ext hzC
      have hJcard : Nat.card ↥(⊤ : Subgroup S) = 4 ^ 6 * (15 * 63 * 255) := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (↥(⊤ : Subgroup S)))
        rw [hcz] at h1 hcardJ
        rw [hcardJ, Subgroup.card_bot, mul_one] at h1
        exact h1
      have h41 : 41 ∣ Nat.card ↥(⊤ : Subgroup S) := by
        rw [Nat.card_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).toEquiv,
          Nat.card_congr Φ.toEquiv, Nat.card_congr (projIso hF).toEquiv.symm,
          CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by norm_num) hF
            (by norm_num)]
        norm_num [Finset.prod_Icc_succ_top]
      rw [hJcard] at h41
      norm_num at h41
  ·
    have hpair : 7 ∣ Nat.card ↥J := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J), hcardJ]
      exact Dvd.dvd.mul_right (by norm_num) _
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 hpair
    have hsfix : α (y : S) = (y : S) := mem_fixSubgroup.1 (hcomp.1 y.2)
    have hβw : β (Φ (y : S)) = Φ (y : S) := by
      rw [hβΦ, MulEquiv.symm_apply_apply, hsfix]
    have hcomm : A * ((Φ (y : S) : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) =
        ((Φ (y : S) : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) * A := by
      have h1 := hβGL (Φ (y : S))
      rw [hβw] at h1
      calc A * ((Φ (y : S) : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F)
          = (A * ((Φ (y : S) : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) * A⁻¹) * A := by group
        _ = ((Φ (y : S) : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) * A := by rw [← h1]
    have hyS : orderOf (y : S) = 7 := by
      rw [Subgroup.orderOf_coe]
      exact hy
    have hord : orderOf ((Φ (y : S) : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) = 7 := by
      rw [Subgroup.orderOf_coe, ← hyS]
      exact orderOf_injective Φ.toMonoidHom Φ.injective (y : S)
    exact hM F hF A hAuni ⟨c5, hA5mat⟩ hAs _ (Φ (y : S)).2 hord hcomm

theorem i14NegPieceA_of_core (hcore : U6Core) : I14NegPieceA :=
  i14NegPieceA_of_matrix (u6SevenFree_of_core hcore)

theorem i14NegFactS_of_core (hcore : U6Core) (hB : I14NegPieceB) (hC : I14NegPieceC)
    (hD : I14NegPieceD) : I14NegFactS :=
  i14NegFactS_of_pieces (i14NegPieceA_of_core hcore) hB hC hD

end Main

end CFSG.LocalAnalysis.GLTheoremA.Y10GNeg
