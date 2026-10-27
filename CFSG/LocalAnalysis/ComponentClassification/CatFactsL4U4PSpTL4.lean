module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpJL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OddBlock

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace PSpL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks StabL TBlocks HBlocks
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB Subgroup
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def bdHom (P : GL (Fin 4) F) :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 4) F where
  toFun x := ⟨(P : Matrix (Fin 4) (Fin 4) F) *
      bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F), by
    rw [det_mul, det_mul, det_bd, x.1.2, x.2.2, mul_one, mul_one, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one]⟩
  map_one' := by
    apply Subtype.ext
    change (P : Matrix (Fin 4) (Fin 4) F) * bd 1 1 * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1
    rw [bd_one, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' x y := by
    apply Subtype.ext
    change (P : Matrix (Fin 4) (Fin 4) F) * bd ((x.1 * y.1 : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) ((x.2 * y.2 : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) =
      ((P : Matrix (Fin 4) (Fin 4) F) * bd (x.1 : Matrix (Fin 2) (Fin 2) F)
        (x.2 : Matrix (Fin 2) (Fin 2) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) *
      ((P : Matrix (Fin 4) (Fin 4) F) * bd (y.1 : Matrix (Fin 2) (Fin 2) F)
        (y.2 : Matrix (Fin 2) (Fin 2) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F))
    have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← bd_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) (P : Matrix (Fin 4) (Fin 4) F), hPP,
      Matrix.one_mul]

theorem coe_bdHom (P : GL (Fin 4) F)
    (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * bd (x.1 : Matrix (Fin 2) (Fin 2) F)
        (x.2 : Matrix (Fin 2) (Fin 2) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := rfl

@[expose] def slU (c : F) : SpecialLinearGroup (Fin 2) F := ⟨uu c, det_uu c⟩

@[expose] def slL (c : F) : SpecialLinearGroup (Fin 2) F := ⟨ll c, det_ll c⟩

@[expose] def bdGens : Set (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :=
  {(slU 1, 1), (slL 1, 1), (1, slU 1), (1, slL 1)}

theorem trace_inv_SL2 (x : SpecialLinearGroup (Fin 2) F) :
    ((x⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (x : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

theorem trace_bdHom (P : GL (Fin 4) F)
    (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace =
      (x.1 : Matrix (Fin 2) (Fin 2) F).trace + (x.2 : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [coe_bdHom, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul, trace_bd]

theorem trace_bdGens (P : GL (Fin 4) F) {x : SpecialLinearGroup (Fin 2) F ×
    SpecialLinearGroup (Fin 2) F} (hx : x ∈ bdGens) :
    ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace = 4 ∧
      ((bdHom P x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace = 4 := by
  have h1 : ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 2 := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one, Fintype.card_fin]
    norm_num
  rw [trace_bdHom, trace_bdHom, Prod.fst_inv, Prod.snd_inv, trace_inv_SL2, trace_inv_SL2]
  rcases hx with rfl | rfl | rfl | rfl
  all_goals
    simp only [slU, slL, h1]
    refine ⟨?_, ?_⟩
  all_goals first
    | (change (uu (1 : F)).trace + 2 = 4; rw [trace_uu]; norm_num)
    | (change 2 + (uu (1 : F)).trace = 4; rw [trace_uu]; norm_num)

theorem bdHom_comm (P : GL (Fin 4) F) {X : Matrix (Fin 4) (Fin 4) F}
    (hXP : X * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F))
    (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X =
      X * ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hX : X = (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := by
    rw [← hXP, Matrix.mul_assoc, hPP', Matrix.mul_one]
  rw [coe_bdHom, hX]
  calc (P : Matrix (Fin 4) (Fin 4) F) * bd (x.1 : Matrix (Fin 2) (Fin 2) F)
        (x.2 : Matrix (Fin 2) (Fin 2) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) *
        ((P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) =
      (P : Matrix (Fin 4) (Fin 4) F) * (bd (x.1 : Matrix (Fin 2) (Fin 2) F)
        (x.2 : Matrix (Fin 2) (Fin 2) F) * X1 (1 : F)) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) (P : Matrix (Fin 4) (Fin 4) F),
          hPP, Matrix.one_mul]
    _ = (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) *
        ((P : Matrix (Fin 4) (Fin 4) F) * bd (x.1 : Matrix (Fin 2) (Fin 2) F)
          (x.2 : Matrix (Fin 2) (Fin 2) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) := by
        rw [bd_comm_X1]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) (P : Matrix (Fin 4) (Fin 4) F),
          hPP, Matrix.one_mul]

theorem conj_comm_bd (P : GL (Fin 4) F) {M : Matrix (Fin 4) (Fin 4) F}
    {x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F}
    (h : M * ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * M) :
    ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M * P) *
        bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) =
      bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M * P) := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [coe_bdHom] at h
  calc ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M * P) *
        bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) =
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (M * ((P : Matrix (Fin 4) (Fin 4) F) *
        bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F))) * P := by
        simp only [Matrix.mul_assoc]
        rw [hPP, Matrix.mul_one]
    _ = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (((P : Matrix (Fin 4) (Fin 4) F) *
        bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) * M) * P := by rw [h]
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) (P : Matrix (Fin 4) (Fin 4) F),
          hPP, Matrix.one_mul]

theorem conj_inv_bd (P : GL (Fin 4) F) {M : Matrix (Fin 4) (Fin 4) F}
    {x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F}
    (h : ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * M *
      ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = M) :
    bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ) *
          (bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F))ᵀ =
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPPt : (P : Matrix (Fin 4) (Fin 4) F)ᵀ * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  rw [coe_bdHom, Matrix.transpose_mul, Matrix.transpose_mul] at h
  have e : ∀ Y : Matrix (Fin 4) (Fin 4) F, (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) *
      ((P : Matrix (Fin 4) (Fin 4) F) * Y * (P : Matrix (Fin 4) (Fin 4) F)ᵀ) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPPt,
      Matrix.mul_one]
  have h' : (P : Matrix (Fin 4) (Fin 4) F) * (bd (x.1 : Matrix (Fin 2) (Fin 2) F)
      (x.2 : Matrix (Fin 2) (Fin 2) F) * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ) *
          (bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F))ᵀ) *
      (P : Matrix (Fin 4) (Fin 4) F)ᵀ = M := by
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc]
  rw [← e (bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
    ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ) *
      (bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F))ᵀ), h']

variable [Fintype F]

theorem inner_or_alt_t (hF : Fintype.card F % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) (P : GL (Fin 4) F) (X : SpecialLinearGroup (Fin 4) F)
    (hXP : (X : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F))
    (ε : MulAut (projectiveSL 4 F)) (hε2 : ε ^ 2 = 1)
    (hfix : ∀ x ∈ bdGens, ε (proj 4 F (bdHom P x)) = proj 4 F (bdHom P x)) :
    ε = 1 ∨ ε = MulAut.conj (proj 4 F X) ∨
      ∃ A : GL (Fin 4) F, (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A ∧
        ε = conjAut 4 F A * dualAut 4 F := by
  classical
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmem : ∀ x, x ∈ ({(slU 1, 1), (slL 1, 1), (1, slU 1), (1, slL 1)} :
      Set (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)) → x ∈ bdGens :=
    fun x hx => hx
  have g1 : ((slU (1 : F), (1 : SpecialLinearGroup (Fin 2) F)) :
      SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens :=
    hmem _ (Set.mem_insert _ _)
  have g2 : ((slL (1 : F), (1 : SpecialLinearGroup (Fin 2) F)) :
      SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens :=
    hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have g3 : (((1 : SpecialLinearGroup (Fin 2) F), slU (1 : F)) :
      SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens :=
    hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have g4 : (((1 : SpecialLinearGroup (Fin 2) F), slL (1 : F)) :
      SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens :=
    hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _))))
  have c1 : ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Matrix.SpecialLinearGroup.coe_one
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, e, he, rfl⟩ := hgen ε
  have hσ := fieldAut_eq_one_of_pow hp hK (odd_of_card_mod_four hF hK) A σ he (m := 0)
    (by simpa using hε2)
  subst hσ
  simp only [map_one, mul_one] at hfix hε2 ⊢
  interval_cases e
  · simp only [pow_zero, mul_one] at hfix hε2 ⊢
    have hc : ∀ x ∈ bdGens, (A : Matrix (Fin 4) (Fin 4) F) *
        ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A :=
      fun x hx => comm_of_conjAut_fix hF A (trace_bdGens P hx).1 (hfix x hx)
    obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) F,
        M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * A * P := ⟨_, rfl⟩
    have k1 := conj_comm_bd P (hc _ g1)
    have k2 := conj_comm_bd P (hc _ g2)
    have k3 := conj_comm_bd P (hc _ g3)
    have k4 := conj_comm_bd P (hc _ g4)
    rw [← hA'] at k1 k2 k3 k4
    simp only [c1] at k1 k2 k3 k4
    have hA'eq := eq_of_comm_bd k1 k2 k3 k4
    set x := A' 0 0 with hx
    set y := A' 2 2 with hy
    have hAeq : (A : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * A' *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := by
      rw [hA', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul, Matrix.mul_assoc,
        hPP', Matrix.mul_one]
    have hA2 : conjAut 4 F (A * A) * fieldAut 4 F 1 = 1 := by
      rw [map_one, mul_one, map_mul, ← sq, hε2]
    obtain ⟨-, c, hcA⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hA2
    have hA'2 : A' * A' = (c : F) • 1 := by
      have e1 : ((A * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (c : F) • 1 := by
        rw [← hcA, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
        rfl
      rw [Units.val_mul] at e1
      rw [hA']
      calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * A * P * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * A * P)
          = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * ((A : Matrix (Fin 4) (Fin 4) F) * A) * P := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) F), hPP', Matrix.one_mul]
        _ = (c : F) • 1 := by
            rw [e1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    rw [hA'eq, bd_mul] at hA'2
    have ex := congrFun (congrFun hA'2 0) 0
    have ey := congrFun (congrFun hA'2 2) 2
    simp [bd, Matrix.smul_apply] at ex ey
    have hxy : (y - x) * (y + x) = 0 := by linear_combination ey - ex
    have hx0 : x ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hAeq
      rw [det_mul, det_mul, hA'eq, det_bd, h0] at this
      simp at this
      exact (GeneralLinearGroup.det A).ne_zero (by rw [GeneralLinearGroup.val_det_apply]; exact this)
    rcases mul_eq_zero.1 hxy with h | h
    · left
      have hyx : y = x := sub_eq_zero.1 h
      have hAs : A = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 x hx0) := by
        apply Units.ext
        rw [hAeq, hA'eq, hyx, GeneralLinearGroup.coe_scalar, Units.val_mk0]
        have : bd (x • (1 : Matrix (Fin 2) (Fin 2) F)) (x • 1) = x • 1 := by
          rw [show (x • (1 : Matrix (Fin 2) (Fin 2) F)) = x • 1 from rfl]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [bd]
        rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP',
          Matrix.smul_one_eq_diagonal]
        rfl
      rw [hAs, conjAut_scalar]
    · right; left
      have hyx : y = -x := by linear_combination h
      have hAs : A = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 x hx0) *
          SpecialLinearGroup.toGL X := by
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, hAeq, hA'eq, hyx]
        have hXv : ((SpecialLinearGroup.toGL X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
            (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := by
          change (X : Matrix (Fin 4) (Fin 4) F) = _
          rw [← hXP, Matrix.mul_assoc, hPP', Matrix.mul_one]
        rw [hXv]
        have : bd (x • (1 : Matrix (Fin 2) (Fin 2) F)) ((-x) • 1) = x • X1 (1 : F) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [bd, X1]
        rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      rw [hAs, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  · right; right
    simp only [pow_one] at hfix ⊢
    refine ⟨A, ?_, rfl⟩
    have hi : ∀ x ∈ bdGens, ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        A * ((bdHom P x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = A := by
      intro x hx
      apply invariant_of_conjAut_dual_fix hF A (trace_bdGens P hx).1 _ (hfix x hx)
      rw [← map_inv]
      exact (trace_bdGens P hx).2
    obtain ⟨A'', hA''⟩ : ∃ M : Matrix (Fin 4) (Fin 4) F,
        M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * A * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ :=
      ⟨_, rfl⟩
    have k1 := conj_inv_bd P (hi _ g1)
    have k2 := conj_inv_bd P (hi _ g2)
    have k3 := conj_inv_bd P (hi _ g3)
    have k4 := conj_inv_bd P (hi _ g4)
    rw [← hA''] at k1 k2 k3 k4
    simp only [c1] at k1 k2 k3 k4
    have hA''eq := eq_of_inv_bd k1 k2 k3 k4
    have hPPt : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)ᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
    have hAeq : (A : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * A'' *
        (P : Matrix (Fin 4) (Fin 4) F)ᵀ := by
      rw [hA'', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul, Matrix.mul_assoc,
        hPPt, Matrix.mul_one]
    rw [hAeq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA''eq,
      transpose_bJ, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]

theorem exists_odd_lift (hF : Fintype.card F % 4 = 3) {X Y : SpecialLinearGroup (Fin 4) F}
    (hY : proj 4 F Y ∈ centralizer {proj 4 F X}) (hodd : Odd (orderOf (proj 4 F Y))) :
    ∃ Y' : SpecialLinearGroup (Fin 4) F, proj 4 F Y' = proj 4 F Y ∧
      Y' ^ orderOf (proj 4 F Y) = 1 ∧ Y' * X = X * Y' := by
  classical
  have hcen : scalars 4 F ≤ center (SpecialLinearGroup (Fin 4) F) := scalars_le_center 4 F
  set m := orderOf (proj 4 F Y) with hm
  have hsq : ∀ s ∈ scalars 4 F, s ^ 2 = 1 := by
    intro s hs
    obtain ⟨c, hc4, hc⟩ := mem_scalars.1 hs
    have hc4' : (c : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
    have hc2 : (c : F) * c = 1 := by
      rcases eq_one_or_eq_neg_one_of_pow_four hF hc4' with h | h <;> rw [h] <;> ring
    rw [sq]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, ← map_mul, hc2, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  set z := Y * X * Y⁻¹ * X⁻¹ with hz
  have hzs : z ∈ scalars 4 F := by
    rw [hz, ← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv,
      mem_centralizer_singleton_iff.mp hY]
    group
  have hYX : Y * X * Y⁻¹ = z * X := by rw [hz]; group
  have hYm : Y ^ m ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_pow, hm, pow_orderOf_eq_one]
  have hzm : z ^ m = 1 := by
    have e1 := pow_conj_eq (hcen hzs) hYX m
    rw [← mem_center_iff.mp (hcen hYm) X, mul_inv_cancel_right] at e1
    have e2 := congrArg (· * X⁻¹) e1
    simp only [mul_inv_cancel, mul_inv_cancel_right] at e2
    exact e2.symm
  have hz1 : z = 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, pow_succ, pow_mul, hsq z hzs, one_pow, one_mul] at hzm
    exact hzm
  set s := Y ^ m with hs
  refine ⟨Y * s, ?_, ?_, ?_⟩
  · rw [map_mul, (proj_eq_one_iff).2 hYm, mul_one]
  · obtain ⟨t, ht⟩ := hodd
    have hsY : Commute Y s := Commute.self_pow Y m
    rw [hsY.mul_pow, ← hs, ← pow_succ', ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul,
      hsq s hYm, one_pow]
  · rw [hz1, one_mul] at hYX
    have hYX' : Y * X = X * Y := by
      calc Y * X = Y * X * Y⁻¹ * Y := by group
        _ = X * Y := by rw [hYX]
    rw [mul_assoc, ← mem_center_iff.mp (hcen hYm) X, ← mul_assoc, hYX', mul_assoc]

omit [Fintype F] in
theorem exists_blockDet (P : GL (Fin 4) F) (X : SpecialLinearGroup (Fin 4) F)
    (hXP : (X : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F)) (h2 : (2 : F) ≠ 0) :
    ∃ δ : centralizer ({X} : Set (SpecialLinearGroup (Fin 4) F)) →* Fˣ,
      ∀ Y : centralizer ({X} : Set (SpecialLinearGroup (Fin 4) F)), δ Y = 1 →
        (Y : SpecialLinearGroup (Fin 4) F) ∈ (bdHom P).range := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set cP : SpecialLinearGroup (Fin 4) F → Matrix (Fin 4) (Fin 4) F := fun Y =>
    (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * Y * P with hcP
  have hcPmul : ∀ Y Z : SpecialLinearGroup (Fin 4) F, cP (Y * Z) = cP Y * cP Z := by
    intro Y Z
    simp only [hcP, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) F), hPP', Matrix.one_mul]
  have hBD : ∀ Y ∈ centralizer ({X} : Set (SpecialLinearGroup (Fin 4) F)), IsBD (cP Y) := by
    intro Y hY
    rw [mem_centralizer_singleton_iff] at hY
    have hYm := congrArg (fun Z : SpecialLinearGroup (Fin 4) F => cP Z) hY
    rw [hcPmul, hcPmul] at hYm
    have hX1 : cP X = X1 (1 : F) := by
      simp only [hcP]
      rw [Matrix.mul_assoc, hXP, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    rw [hX1] at hYm
    exact isBD_of_comm_X1 h2 one_ne_zero hYm
  let β : centralizer ({X} : Set (SpecialLinearGroup (Fin 4) F)) →* Matrix (Fin 2) (Fin 2) F :=
    { toFun := fun Y => ul (cP Y)
      map_one' := by
        change ul (cP 1) = 1
        simp only [hcP, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hPP, ul_one]
      map_mul' := fun Y Z => by
        change ul (cP ((Y : SpecialLinearGroup (Fin 4) F) * Z)) = ul (cP Y) * ul (cP Z)
        rw [hcPmul, ul_mul (hBD _ Y.2) (hBD _ Z.2)] }
  refine ⟨(Matrix.detMonoidHom.comp β).toHomUnits, fun Y hY => ?_⟩
  have hdu : (ul (cP Y)).det = 1 := by
    have := congrArg Units.val hY
    simpa [β] using this
  have hd : (cP Y).det = 1 := by
    simp only [hcP]
    rw [det_mul, det_mul, mul_right_comm, ← det_mul, hPP, det_one, one_mul]
    exact (Y : SpecialLinearGroup (Fin 4) F).2
  have hdl : (lr (cP Y)).det = 1 := by
    rw [det_of_isBD (hBD _ Y.2), hdu, one_mul] at hd
    exact hd
  refine ⟨(⟨ul (cP Y), hdu⟩, ⟨lr (cP Y), hdl⟩), ?_⟩
  apply Subtype.ext
  change (P : Matrix (Fin 4) (Fin 4) F) * bd (ul (cP Y)) (lr (cP Y)) *
    (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = _
  rw [← eq_bd (hBD _ Y.2)]
  simp only [hcP]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul, Matrix.mul_assoc, hPP',
    Matrix.mul_one]

theorem centralizerCore516_le_t (hF : Fintype.card F % 4 = 3) (P : GL (Fin 4) F)
    (X : SpecialLinearGroup (Fin 4) F)
    (hXP : (X : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F)) :
    centralizerCore516 (Fintype.card F) (proj 4 F X) ≤ ((proj 4 F).comp (bdHom P)).range := by
  classical
  have h2 := two_ne_zero_of_card_mod_four hF
  set CX := centralizer ({X} : Set (SpecialLinearGroup (Fin 4) F)) with hCX
  obtain ⟨δ, hδ⟩ := exists_blockDet P X hXP h2
  have hrange : ((proj 4 F).comp (bdHom P)).range = (bdHom P).range.map (proj 4 F) := by
    rw [MonoidHom.range_comp]
  unfold centralizerCore516
  split_ifs with hq3
  · rw [closure_le]
    rintro y ⟨hy, hyo⟩
    obtain ⟨Y, rfl⟩ := proj_surjective 4 F y
    obtain ⟨Y', hY'p, hY'm, hY'X⟩ := exists_odd_lift hF hy hyo
    have hY'C : Y' ∈ CX := by rw [hCX, mem_centralizer_singleton_iff]; exact hY'X
    have h1 : δ ⟨Y', hY'C⟩ ^ orderOf (proj 4 F Y) = 1 := by
      rw [← map_pow]
      have : (⟨Y', hY'C⟩ : CX) ^ orderOf (proj 4 F Y) = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, hY'm]
        rfl)
      rw [this, map_one]
    have h22 : δ ⟨Y', hY'C⟩ ^ 2 = 1 := by
      have := pow_card_eq_one (x := δ ⟨Y', hY'C⟩)
      rwa [Fintype.card_units, hq3] at this
    have hg : Nat.gcd (orderOf (proj 4 F Y)) 2 = 1 := Nat.coprime_two_right.2 hyo
    have h1' := pow_gcd_eq_one.2 ⟨h1, h22⟩
    rw [hg, pow_one] at h1'
    rw [hrange, ← hY'p]
    exact mem_map_of_mem _ (hδ ⟨Y', hY'C⟩ h1')
  · refine (Quasithin.perfectCore_le_derivedSeriesOf _ 2).trans ?_
    have hC1 : ⁅centralizer {proj 4 F X}, centralizer {proj 4 F X}⁆ ≤ CX.map (proj 4 F) := by
      rw [commutator_le]
      intro u hu v hv
      obtain ⟨U, rfl⟩ := proj_surjective 4 F u
      obtain ⟨V, rfl⟩ := proj_surjective 4 F v
      refine ⟨⁅U, V⁆, ?_, by rw [map_commutatorElement]⟩
      have hsc : scalars 4 F ≤ center (SpecialLinearGroup (Fin 4) F) := scalars_le_center 4 F
      have hmem : ∀ Z : SpecialLinearGroup (Fin 4) F,
          proj 4 F Z ∈ centralizer {proj 4 F X} → Z * X * Z⁻¹ * X⁻¹ ∈ scalars 4 F := by
        intro Z hZ
        rw [mem_centralizer_singleton_iff] at hZ
        rw [← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hZ]
        group
      rw [SetLike.mem_coe, hCX, mem_centralizer_singleton_iff]
      exact commutator_comm_of_comm_mod hsc (hmem U hu) (hmem V hv)
    have hC2 : ⁅CX, CX⁆ ≤ (bdHom P).range := by
      rw [commutator_le]
      intro a ha b hb
      have : δ ⁅(⟨a, ha⟩ : CX), ⟨b, hb⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      exact hδ _ this
    rw [Quasithin.derivedSeriesOf_succ, Quasithin.derivedSeriesOf_succ,
      Quasithin.derivedSeriesOf_zero, hrange]
    calc ⁅⁅centralizer {proj 4 F X}, centralizer {proj 4 F X}⁆,
          ⁅centralizer {proj 4 F X}, centralizer {proj 4 F X}⁆⁆ ≤
        ⁅CX.map (proj 4 F), CX.map (proj 4 F)⁆ := commutator_mono hC1 hC1
      _ = (⁅CX, CX⁆).map (proj 4 F) := (map_commutator _ _ _).symm
      _ ≤ (bdHom P).range.map (proj 4 F) := map_mono hC2

omit [Fintype F] in
theorem slU_pow (c : F) (n : ℕ) : slU c ^ n = slU (n * c) := by
  induction n with
  | zero =>
    apply Subtype.ext
    rw [pow_zero, Nat.cast_zero, zero_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slU, uu]
  | succ n ih =>
    rw [pow_succ, ih]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slU, uu, Matrix.mul_apply, Fin.sum_univ_two]
    ring

omit [Fintype F] in
theorem slL_pow (c : F) (n : ℕ) : slL c ^ n = slL (n * c) := by
  induction n with
  | zero =>
    apply Subtype.ext
    rw [pow_zero, Nat.cast_zero, zero_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slL, ll]
  | succ n ih =>
    rw [pow_succ, ih]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slL, ll, Matrix.mul_apply, Fin.sum_univ_two]
    ring

omit [Fintype F] in
theorem slU_zero : slU (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slU, uu]

omit [Fintype F] in
theorem slL_zero : slL (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slL, ll]

theorem commutator_top_prod (h4 : 4 ≤ Fintype.card F) :
    ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)), ⊤⁆ =
      (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)) := by
  classical
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ]; exact h4)
  have hP := CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  have hc : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)), ⊤⁆ =
      (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
    rw [← commutator_def]
    exact hP.commutator_eq_top
  rw [← top_prod_top, commutator_prod_prod, hc]

theorem innerPSpAt_t_L4 (hF : Fintype.card F % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) (X : SpecialLinearGroup (Fin 4) F)
    (hXX : (X : Matrix (Fin 4) (Fin 4) F) * X = 1) (hX1 : proj 4 F X ≠ 1) :
    InnerPSpAt (p ^ f) p f (proj 4 F X) := by
  classical
  have hq : p ^ f = Fintype.card F := by rw [← hK, Nat.card_eq_fintype_card]
  rw [hq]
  have h2 := two_ne_zero_of_card_mod_four hF
  have hX1' : (X : Matrix (Fin 4) (Fin 4) F) ≠ 1 := fun h => hX1 (by
    rw [proj_eq_one_iff, mem_scalars]
    exact ⟨1, one_pow _, by rw [h, Units.val_one, map_one]⟩)
  have hXm1 : (X : Matrix (Fin 4) (Fin 4) F) ≠ -1 := fun h => hX1 (by
    rw [proj_eq_one_iff, mem_scalars]
    exact ⟨-1, by norm_num, by rw [h, Units.val_neg, Units.val_one, map_neg, map_one]⟩)
  obtain ⟨P, hXP⟩ := exists_frame_t2_L4 h2 hXX X.2 hX1' hXm1
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set φ := (proj 4 F).comp (bdHom P) with hφ
  have hSC : φ.range ≤ centralizer {proj 4 F X} := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff, hφ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (bdHom_comm P hXP x)
  have hNS := centralizerCore516_le_t hF P X hXP
  have hker : ∀ x ∈ φ.ker, x.1 ∈ center (SpecialLinearGroup (Fin 2) F) ∧
      x.2 ∈ center (SpecialLinearGroup (Fin 2) F) := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hx
    obtain ⟨c, -, hc⟩ := hx
    rw [coe_bdHom] at hc
    have hbd : bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) =
        bd ((c : F) • 1) ((c : F) • 1) := by
      calc bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) =
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * ((P : Matrix (Fin 4) (Fin 4) F) *
            bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) *
              (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) := by
            simp only [← Matrix.mul_assoc]
            rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
        _ = bd ((c : F) • 1) ((c : F) • 1) := by
            rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
              Matrix.mul_one, Matrix.smul_mul, hPP]
            ext i j
            fin_cases i <;> fin_cases j <;> simp [bd]
    have e1 : (x.1 : Matrix (Fin 2) (Fin 2) F) = (c : F) • 1 := by
      have := congrArg ul hbd
      rwa [ul_bd, ul_bd] at this
    have e2 : (x.2 : Matrix (Fin 2) (Fin 2) F) = (c : F) • 1 := by
      have := congrArg lr hbd
      rwa [lr_bd, lr_bd] at this
    have hc2 : (c : F) ^ 2 = 1 := by
      have := x.1.2
      rw [e1, det_smul, det_one, mul_one, Fintype.card_fin] at this
      exact this
    refine ⟨Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by rw [Fintype.card_fin]; exact hc2,
      ?_⟩, Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by rw [Fintype.card_fin]; exact hc2,
      ?_⟩⟩
    · rw [e1, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    · rw [e2, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.card_eq_fintype_card] at hK
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0] at hK; omega
    · have : 2 ∣ Fintype.card F := hK ▸ dvd_pow_self 2 h0.ne'
      omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero, Nat.card_eq_fintype_card] at hK; omega
    · exact h0
  have hoddpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  have hgN : ∀ x ∈ bdGens, proj 4 F (bdHom P x) ∈
      centralizerCore516 (Fintype.card F) (proj 4 F X) := by
    intro x hx
    unfold centralizerCore516
    split_ifs with hq3
    · refine subset_closure ⟨hSC ⟨x, rfl⟩, ?_⟩
      have h3 : (3 : F) = 0 := by
        have := FiniteField.cast_card_eq_zero F
        rw [hq3] at this
        exact_mod_cast this
      have hx3 : x ^ 3 = 1 := by
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [Prod.pow_def, slU_pow, slL_pow, h3, slU_zero, slL_zero]
      have : proj 4 F (bdHom P x) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hx3, map_one, map_one]
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one this)
    · have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
        rw [MonoidHom.range_eq_map, ← map_commutator,
          commutator_top_prod (by have := Fintype.card_pos (α := F); omega)]
      exact Quasithin.le_perfectCore_of_perfect hSC hperf ⟨x, rfl⟩
  refine ⟨pPrimeCore_centralizerCore516_eq_bot hSC hNS
    (fun R hRS hR hodd => eq_bot_of_odd_block hoddpp φ hker R hRS hR hodd),
    fun ε hε2 hε1 hεℓ _ hεN => ?_⟩
  rcases inner_or_alt_t hF hp hK P X hXP ε hε2 (fun x hx => hεN _ (hgN x hx)) with
    h | h | ⟨A, hA, rfl⟩
  · exact absurd h hε1
  · exact absurd h hεℓ
  · exact exists_psp_of_alt_L4 hF hp hK A hA

end PSpL

end CFSG.ComponentClassification.CatFactsL4U4
