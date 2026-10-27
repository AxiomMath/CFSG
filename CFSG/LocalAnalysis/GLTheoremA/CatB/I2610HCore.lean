module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HJoint
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

private abbrev PU : Subgroup (GL (Fin 6) F4) := primeFormUnitary hF4 (idGram F4 6)

private abbrev GL6 : Type := GL (Fin 6) F4

private abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) F4

private theorem scalar_conj_left (Q : GL6) (c : F4ˣ) :
    Q⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) c * Q =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  rw [(commute_scalar c Q⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]

private theorem scalar_conj_right (Q : GL6) (c : F4ˣ) :
    Q * Matrix.GeneralLinearGroup.scalar (Fin 6) c * Q⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  rw [(commute_scalar c Q).eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem conj_pow_three (Q X : GL6) : (Q⁻¹ * X * Q) ^ 3 = Q⁻¹ * X ^ 3 * Q := by
  have h := conj_pow (a := Q⁻¹) (b := X) (i := 3)
  rwa [inv_inv] at h

private theorem conj_pow_three_PU (Q X : PU) : (Q⁻¹ * X * Q) ^ 3 = Q⁻¹ * X ^ 3 * Q := by
  have h := conj_pow (a := Q⁻¹) (b := X) (i := 3)
  rwa [inv_inv] at h

private theorem glaPComponent_conj (Q X Y : PU) {J : Subgroup M6}
    (hJ : GLAPComponent 3 (CenD (X : GL6) ⊓ CenD (Y : GL6)) J) :
    GLAPComponent 3
      (CenD ((Q⁻¹ * X * Q : PU) : GL6) ⊓ CenD ((Q⁻¹ * Y * Q : PU) : GL6))
      (J.map (conjM6 Q⁻¹).toMonoidHom) := by
  have h := glaPComponent_map_mulEquiv Nat.prime_three (conjM6 Q⁻¹) hJ
  rw [Subgroup.map_inf (CenD (X : GL6)) (CenD (Y : GL6)) _
    (conjM6 Q⁻¹).injective, map_CenD_conj, map_CenD_conj] at h
  simpa using h

private theorem card_pSimple_conj_eq (Q : PU) (J : Subgroup M6) :
    Nat.card (PSimple 3 J) =
      Nat.card (PSimple 3 (J.map (conjM6 Q⁻¹).toMonoidHom)) := by
  obtain ⟨e⟩ := pSimple_map_equiv 3 (conjM6 Q⁻¹) J
  exact (Nat.card_congr e.toEquiv).symm

private structure PairHyp (X Y : PU) where
  cube : X ^ 3 = 1
  ycube : ∃ c : F4ˣ, (Y : GL6) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  skew : ∃ t : F4ˣ, (X : GL6) * (Y : GL6) =
    Matrix.GeneralLinearGroup.scalar (Fin 6) t * ((Y : GL6) * (X : GL6))
  ns : ¬ ∃ c : F4ˣ, (X : GL6) = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  indep : ∀ (k : ℕ) (c : F4ˣ), (Y : GL6) ≠
    Matrix.GeneralLinearGroup.scalar (Fin 6) c * (X : GL6) ^ k

private theorem conj_hyp (Q : PU) {X Y : PU} (h : PairHyp X Y) :
    PairHyp (Q⁻¹ * X * Q) (Q⁻¹ * Y * Q) := by
  have hcoeX : ((Q⁻¹ * X * Q : PU) : GL6) = (Q : GL6)⁻¹ * (X : GL6) * (Q : GL6) := rfl
  have hcoeY : ((Q⁻¹ * Y * Q : PU) : GL6) = (Q : GL6)⁻¹ * (Y : GL6) * (Q : GL6) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow_three_PU, h.cube, mul_one, inv_mul_cancel]
  · obtain ⟨c, hc⟩ := h.ycube
    refine ⟨c, ?_⟩
    rw [hcoeY, conj_pow_three, hc, scalar_conj_left]
  · obtain ⟨t, ht⟩ := h.skew
    refine ⟨t, ?_⟩
    rw [hcoeX, hcoeY]
    calc (Q : GL6)⁻¹ * (X : GL6) * (Q : GL6) * ((Q : GL6)⁻¹ * (Y : GL6) * (Q : GL6))
        = (Q : GL6)⁻¹ * ((X : GL6) * (Y : GL6)) * (Q : GL6) := by group
      _ = (Q : GL6)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 6) t *
            ((Y : GL6) * (X : GL6))) * (Q : GL6) := by rw [ht]
      _ = ((Q : GL6)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) t * (Q : GL6)) *
            (((Q : GL6)⁻¹ * (Y : GL6) * (Q : GL6)) *
              ((Q : GL6)⁻¹ * (X : GL6) * (Q : GL6))) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) t *
            (((Q : GL6)⁻¹ * (Y : GL6) * (Q : GL6)) *
              ((Q : GL6)⁻¹ * (X : GL6) * (Q : GL6))) := by rw [scalar_conj_left]
  · intro hcon
    obtain ⟨c, hc⟩ := hcon
    apply h.ns
    refine ⟨c, ?_⟩
    rw [hcoeX] at hc
    calc (X : GL6) = (Q : GL6) * ((Q : GL6)⁻¹ * (X : GL6) * (Q : GL6)) * (Q : GL6)⁻¹ := by
          group
      _ = (Q : GL6) * Matrix.GeneralLinearGroup.scalar (Fin 6) c * (Q : GL6)⁻¹ := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c := scalar_conj_right Q c
  · intro k c hcon
    rw [hcoeX, hcoeY] at hcon
    refine h.indep k c ?_
    calc (Y : GL6) = (Q : GL6) * ((Q : GL6)⁻¹ * (Y : GL6) * (Q : GL6)) * (Q : GL6)⁻¹ := by
          group
      _ = (Q : GL6) * (Matrix.GeneralLinearGroup.scalar (Fin 6) c *
            ((Q : GL6)⁻¹ * (X : GL6) * (Q : GL6)) ^ k) * (Q : GL6)⁻¹ := by rw [hcon]
      _ = ((Q : GL6) * Matrix.GeneralLinearGroup.scalar (Fin 6) c * (Q : GL6)⁻¹) *
            ((Q : GL6) * ((Q : GL6)⁻¹ * (X : GL6) * (Q : GL6)) * (Q : GL6)⁻¹) ^ k := by
          rw [conj_pow]
          group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (X : GL6) ^ k := by
          rw [scalar_conj_right,
            show (Q : GL6) * ((Q : GL6)⁻¹ * (X : GL6) * (Q : GL6)) * (Q : GL6)⁻¹ =
              (X : GL6) from by group]

private theorem card_pSimple_of_pair_diag (X Y : PU) {d₁ : Fin 6 → F4}
    (hX : ((X : GL6) : Mat6) = Matrix.diagonal d₁) (h : PairHyp X Y) {J : Subgroup M6}
    (hJ : GLAPComponent 3 (CenD (X : GL6) ⊓ CenD (Y : GL6)) J) :
    Nat.card (PSimple 3 J) = 25920 := by
  classical
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  have hd₁3 : ∀ i, d₁ i ^ 3 = 1 := by
    have hmat : ((X : GL6) : Mat6) ^ 3 = 1 := by
      have h1 : (X : GL6) ^ 3 = 1 := by
        simpa using congrArg (fun g : PU => (g : GL6)) h.cube
      simpa using congrArg (fun g : GL6 => (g : Mat6)) h1
    rw [hX, Matrix.diagonal_pow] at hmat
    intro i
    have := congrFun (congrFun hmat i) i
    simpa using this
  have hns : ¬ ∀ i, d₁ i = d₁ 0 := by
    intro hconst
    apply h.ns
    have h0 : d₁ 0 ≠ 0 := by
      intro hzero
      have h3 := hd₁3 0
      rw [hzero] at h3
      simpa using h3
    refine ⟨Units.mk0 (d₁ 0) h0, ?_⟩
    apply Units.ext
    rw [hX, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      exact hconst i
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  have hbig : ∃ c : F4, 4 ≤ Fintype.card (Blk d₁ c) := by
    by_contra hc
    push Not at hc
    exact hJne (eq_bot_of_perfect_of_small hX (fun c => by have := hc c; omega)
      (hJ.1.trans inf_le_left) hperf)
  obtain ⟨c, hc4⟩ := hbig
  have hc5 : Fintype.card (Blk d₁ c) ≤ 5 := card_blk_le_five d₁ hns c
  have hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d₁ c') ≤ 2 := by
    intro c' hc'
    have h := card_blk_add_le d₁ (Ne.symm hc')
    omega
  have hc0 : c ≠ 0 := by
    obtain ⟨i⟩ := Fintype.card_pos_iff.1 (by omega : 0 < Fintype.card (Blk d₁ c))
    rw [← i.2]
    intro hzero
    have h3 := hd₁3 i.1
    rw [hzero] at h3
    simpa using h3
  have hJK : J ≤ (embSU d₁ c).range :=
    le_range_embSU d₁ c hX (fun c' hc' => by have := hsmall c' hc'; omega)
      (hJ.1.trans inf_le_left) hperf
  obtain ⟨t, ht⟩ := h.skew
  by_cases ht1 : t = 1
  ·
    have hcomm : (X : GL6) * (Y : GL6) = (Y : GL6) * (X : GL6) := by
      rw [ht1] at ht
      simpa using ht
    have hMD : ((Y : GL6) : Mat6) * Matrix.diagonal d₁ =
        Matrix.diagonal d₁ * ((Y : GL6) : Mat6) := by
      have h1 := congrArg (fun g : GL6 => (g : Mat6)) hcomm
      rw [Units.val_mul, Units.val_mul, hX] at h1
      exact h1.symm
    obtain ⟨μ, hμ⟩ := h.ycube
    have hμ0 : (μ : F4) ≠ 0 := μ.ne_zero
    have hM3 : ((Y : GL6) : Mat6) ^ 3 = (μ : F4) • (1 : Mat6) := by
      have h1 := congrArg (fun g : GL6 => (g : Mat6)) hμ
      rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at h1
      exact h1
    have ho : ¬ 3 ∣ Fintype.card (Blk d₁ c) := by
      have h45 : Fintype.card (Blk d₁ c) = 4 ∨ Fintype.card (Blk d₁ c) = 5 := by omega
      rintro hdvd
      rcases h45 with h4 | h5
      · rw [h4] at hdvd; norm_num at hdvd
      · rw [h5] at hdvd; norm_num at hdvd
    have hμ1 : (μ : F4) = 1 :=
      eq_one_of_cube_of_commute_diagonal (n := 6) (d := d₁) (c := c) ho hMD hμ0 hM3
    have hY3one : Y ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      have h1 := congrArg (fun g : GL6 => (g : Mat6)) hμ
      rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, hμ1, Matrix.diagonal_one] at h1
      simpa using h1
    have hcommPu : X * Y = Y * X := by
      apply Subtype.ext
      exact hcomm
    have hcommG : ∀ x ∈ Subgroup.closure ({X, Y} : Set PU),
        ∀ y ∈ Subgroup.closure ({X, Y} : Set PU), x * y = y * x := by
      have hcent : Subgroup.closure ({X, Y} : Set PU) ≤
          Subgroup.centralizer ({X, Y} : Set PU) := by
        rw [Subgroup.closure_le]
        intro z hz
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        change z ∈ Subgroup.centralizer ({X, Y} : Set PU)
        rw [Subgroup.mem_centralizer_iff]
        rcases hz with hzX | hzY
        · rw [hzX]
          intro w hw
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with hwX | hwY
          · rw [hwX]
          · rw [hwY]
            exact hcommPu.symm
        · rw [hzY]
          intro w hw
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with hwX | hwY
          · rw [hwX]
            exact hcommPu
          · rw [hwY]
      have hcent' : Subgroup.closure ({X, Y} : Set PU) ≤
          Subgroup.centralizer (Subgroup.closure ({X, Y} : Set PU)) := by
        rw [Subgroup.centralizer_closure]
        exact hcent
      intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.1 (hcent' hx) y hy).symm
    have hpowG : ∀ x ∈ Subgroup.closure ({X, Y} : Set PU), x ^ 3 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction'' with
      | mem z hz =>
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact h.cube
          · exact hY3one
      | inv_mem z hz =>
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · rw [inv_pow, h.cube, inv_one]
          · rw [inv_pow, hY3one, inv_one]
      | one => exact one_pow 3
      | mul a b ha hb ha3 hb3 =>
          rw [Commute.mul_pow (hcommG a ha b hb) 3, ha3, hb3, one_mul]
    obtain ⟨P₂, hP₂⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m hF4
      F4_omega_primitive (by norm_num) (Subgroup.closure ({X, Y} : Set PU)) hcommG hpowG
    have hXcl : X ∈ Subgroup.closure ({X, Y} : Set PU) := Subgroup.subset_closure (by simp)
    have hYcl : Y ∈ Subgroup.closure ({X, Y} : Set PU) := Subgroup.subset_closure (by simp)
    set D₁ : GL6 := ((P₂⁻¹ * X * P₂ : PU) : GL6) with hD₁def
    set D₂ : GL6 := ((P₂⁻¹ * Y * P₂ : PU) : GL6) with hD₂def
    have hD₁diag : (D₁ : Mat6).IsDiag := hP₂ X hXcl
    have hD₂diag : (D₂ : Mat6).IsDiag := hP₂ Y hYcl
    set e₁ : Fin 6 → F4 := fun i => (D₁ : Mat6) i i with he₁def
    set e₂ : Fin 6 → F4 := fun i => (D₂ : Mat6) i i with he₂def
    have hD₁ : (D₁ : Mat6) = Matrix.diagonal e₁ := hD₁diag.diagonal_diag.symm
    have hD₂ : (D₂ : Mat6) = Matrix.diagonal e₂ := hD₂diag.diagonal_diag.symm
    have h₂ : PairHyp (P₂⁻¹ * X * P₂) (P₂⁻¹ * Y * P₂) := conj_hyp P₂ h
    have hJ₂ : GLAPComponent 3 (CenD D₁ ⊓ CenD D₂)
        (J.map (conjM6 P₂⁻¹).toMonoidHom) := glaPComponent_conj P₂ X Y hJ
    have hD₁3 : D₁ ^ 3 = 1 := by
      have h1 : (((P₂⁻¹ * X * P₂ : PU)) : GL6) ^ 3 = 1 := by
        simpa using congrArg (fun g : PU => (g : GL6)) h₂.cube
      exact h1
    have hY2cube : (P₂⁻¹ * Y * P₂) ^ 3 = 1 := by
      rw [conj_pow_three_PU, hY3one, mul_one, inv_mul_cancel]
    have hD₂3 : D₂ ^ 3 = 1 := by
      have h1 : (((P₂⁻¹ * Y * P₂ : PU)) : GL6) ^ 3 = 1 := by
        simpa using congrArg (fun g : PU => (g : GL6)) hY2cube
      exact h1
    have he₁3 : ∀ i, e₁ i ^ 3 = 1 := by
      have hmat : (D₁ : Mat6) ^ 3 = 1 := by
        simpa using congrArg (fun g : GL6 => (g : Mat6)) hD₁3
      rw [hD₁, Matrix.diagonal_pow] at hmat
      intro i
      have := congrFun (congrFun hmat i) i
      simpa using this
    have he₂3 : ∀ i, e₂ i ^ 3 = 1 := by
      have hmat : (D₂ : Mat6) ^ 3 = 1 := by
        simpa using congrArg (fun g : GL6 => (g : Mat6)) hD₂3
      rw [hD₂, Matrix.diagonal_pow] at hmat
      intro i
      have := congrFun (congrFun hmat i) i
      simpa using this
    have hns₁ : ¬ ∀ i, e₁ i = e₁ 0 := by
      intro hconst
      apply h₂.ns
      have h0 : e₁ 0 ≠ 0 := by
        intro hzero
        have h3 := he₁3 0
        rw [hzero] at h3
        simpa using h3
      refine ⟨Units.mk0 (e₁ 0) h0, ?_⟩
      change D₁ = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (e₁ 0) h0)
      apply Units.ext
      rw [hD₁, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        exact hconst i
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
    have hindep : ∀ (k : ℕ) (c : F4), ¬ ∀ i, e₂ i = c * e₁ i ^ k := by
      intro k c hk
      have hc : c ≠ 0 := by
        intro hzero
        have h1 := hk 0
        rw [hzero, zero_mul] at h1
        have h2 := he₂3 0
        rw [h1] at h2
        simpa using h2
      refine h₂.indep k (Units.mk0 c hc) ?_
      change D₂ = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc) * D₁ ^ k
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
        Units.val_mk0, hD₂, hD₁, Matrix.scalar_apply, Matrix.diagonal_pow,
        Matrix.diagonal_mul_diagonal]
      rw [show e₂ = fun i => c * (e₁ ^ k) i from funext fun i => hk i]
    have hcard : Nat.card (PSimple 3 (J.map (conjM6 P₂⁻¹).toMonoidHom)) = 25920 :=
      card_pSimple_of_diag_pair (D₁ := D₁) (D₂ := D₂) (d₁ := e₁) (d₂ := e₂)
        hD₁ hD₂ he₁3 he₂3 hns₁ hindep hJ₂
    calc Nat.card (PSimple 3 J)
        = Nat.card (PSimple 3 (J.map (conjM6 P₂⁻¹).toMonoidHom)) := card_pSimple_conj_eq P₂ J
      _ = 25920 := hcard
  ·
    exfalso
    have htne : (t : F4) ≠ 1 := fun h1 => ht1 (Units.ext h1)
    have htval : ((t⁻¹ : F4ˣ) : F4) * (t : F4) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have htinv : ((t⁻¹ : F4ˣ) : F4) ≠ 1 := by
      intro h1
      rw [h1, one_mul] at htval
      exact htne htval
    have hDYD : Matrix.diagonal d₁ * ((Y : GL6) : Mat6) =
        (t : F4) • (((Y : GL6) : Mat6) * Matrix.diagonal d₁) := by
      have h1 : ((X : GL6) : Mat6) * ((Y : GL6) : Mat6) =
          Matrix.scalar (Fin 6) (t : F4) * (((Y : GL6) : Mat6) * ((X : GL6) : Mat6)) := by
        simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] using
          congrArg (fun g : GL6 => (g : Mat6)) ht
      rw [hX, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at h1
      exact h1
    have hMD : ((Y : GL6) : Mat6) * Matrix.diagonal d₁ =
        ((t⁻¹ : F4ˣ) : F4) • (Matrix.diagonal d₁ * ((Y : GL6) : Mat6)) := by
      calc ((Y : GL6) : Mat6) * Matrix.diagonal d₁
          = (1 : F4) • (((Y : GL6) : Mat6) * Matrix.diagonal d₁) := (one_smul _ _).symm
        _ = (((t⁻¹ : F4ˣ) : F4) * (t : F4)) •
              (((Y : GL6) : Mat6) * Matrix.diagonal d₁) := by rw [htval]
        _ = ((t⁻¹ : F4ˣ) : F4) •
              ((t : F4) • (((Y : GL6) : Mat6) * Matrix.diagonal d₁)) := by rw [smul_smul]
        _ = ((t⁻¹ : F4ˣ) : F4) • (Matrix.diagonal d₁ * ((Y : GL6) : Mat6)) := by
              rw [← hDYD]
    have hIsUnit : IsUnit ((Y : GL6) : Mat6) := ⟨(Y : GL6), rfl⟩
    have hbot : J = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall J).2 fun u hu => ?_
      obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 (hJK hu)
      have hg : ∀ i j, ¬ (d₁ i = c ∧ d₁ j = c) →
          ((u : GL6) : Mat6) i j = (1 : Mat6) i j := by
        intro i j hij
        have h1 : ((u : GL6) : Mat6) =
            extMat d₁ c (Matrix.reindex (Fintype.equivFin (Blk d₁ c)).symm
              (Fintype.equivFin (Blk d₁ c)).symm
              (((A : GL (Fin (Fintype.card (Blk d₁ c))) F4)) :
                Matrix (Fin (Fintype.card (Blk d₁ c))) (Fin (Fintype.card (Blk d₁ c))) F4)) := by
          rw [← hA]
          exact mM6_embSU (d := d₁) (c := c) A
        rw [h1, extMat_apply]
        simp only [dif_neg hij]
      have hgM : ((u : GL6) : Mat6) * ((Y : GL6) : Mat6) =
          ((Y : GL6) : Mat6) * ((u : GL6) : Mat6) := by
        have hmem : u ∈ CenD (Y : GL6) := (Subgroup.mem_inf.1 (hJ.1 hu)).2
        have h1 := mem_CenD.1 hmem
        simpa using congrArg (fun g : GL6 => (g : Mat6)) h1
      have hone : ((u : GL6) : Mat6) = 1 :=
        eq_one_of_skew_commute hc0 htinv hIsUnit hMD hg hgM
      apply Subtype.ext
      apply Units.ext
      simpa using hone
    exact hJne hbot

theorem card_pSimple_of_pair (X Y : primeFormUnitary hF4 (idGram F4 6)) (hX3 : X ^ 3 = 1)
    (hY3 : ∃ c : F4ˣ, (Y : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hXY : ∃ t : F4ˣ, (X : GL (Fin 6) F4) * (Y : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) t * ((Y : GL (Fin 6) F4) * (X : GL (Fin 6) F4)))
    (hXs : ¬ ∃ c : F4ˣ, (X : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hYX : ∀ (k : ℕ) (c : F4ˣ), (Y : GL (Fin 6) F4) ≠
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * (X : GL (Fin 6) F4) ^ k)
    {J : Subgroup M6}
    (hJ : GLAPComponent 3 (CenD (X : GL (Fin 6) F4) ⊓ CenD (Y : GL (Fin 6) F4)) J) :
    Nat.card (PSimple 3 J) = 25920 := by
  obtain ⟨P, d₁, hd₁⟩ := exists_diag6 X hX3
  have h : PairHyp X Y := ⟨hX3, hY3, hXY, hXs, hYX⟩
  have h₁ : PairHyp (P⁻¹ * X * P) (P⁻¹ * Y * P) := conj_hyp P h
  have hJ₁ : GLAPComponent 3
      (CenD ((P⁻¹ * X * P : PU) : GL (Fin 6) F4) ⊓
        CenD ((P⁻¹ * Y * P : PU) : GL (Fin 6) F4))
      (J.map (conjM6 P⁻¹).toMonoidHom) := glaPComponent_conj P X Y hJ
  have hmain : Nat.card (PSimple 3 (J.map (conjM6 P⁻¹).toMonoidHom)) = 25920 :=
    card_pSimple_of_pair_diag (P⁻¹ * X * P) (P⁻¹ * Y * P) hd₁ h₁ hJ₁
  rw [card_pSimple_conj_eq P J]
  exact hmain

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
