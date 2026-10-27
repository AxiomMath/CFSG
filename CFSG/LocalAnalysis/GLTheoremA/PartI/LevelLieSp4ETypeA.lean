module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4ECent
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

@[expose] def mat (x : ↥(StatedSp 2 K)) : Matrix Ix Ix K := ((x : GL Ix K) : Matrix Ix Ix K)

theorem mat_mul (x y : ↥(StatedSp 2 K)) : mat (x * y) = mat x * mat y := rfl

theorem mat_one : mat (1 : ↥(StatedSp 2 K)) = 1 := rfl

theorem mem_mat (x : ↥(StatedSp 2 K)) : (mat x)ᵀ * JJ K * mat x = JJ K :=
  mem_statedSp_iff.1 x.2

theorem planeMat_pair_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    planeMat ![A, 1] * planeMat ![B, 1] = planeMat ![A * B, 1] := by
  rw [planeMat_mul]
  congr 1
  funext k
  fin_cases k <;> simp

theorem planeMat_one_pair : planeMat ![(1 : Matrix (Fin 2) (Fin 2) K), 1] = 1 := by
  rw [planeMat_one]
  congr 1
  funext k
  fin_cases k <;> rfl

@[expose] def iotaU (X : GL (Fin 2) K) : GL Ix K :=
  ⟨planeMat ![(X : Matrix (Fin 2) (Fin 2) K), 1],
    planeMat ![((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), 1],
    by rw [planeMat_pair_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, planeMat_one_pair],
    by rw [planeMat_pair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, planeMat_one_pair]⟩

theorem iotaU_mem {X : GL (Fin 2) K} (hX : X ∈ StatedSL 2 K) : iotaU X ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff]
  show (planeMat ![(X : Matrix (Fin 2) (Fin 2) K), 1])ᵀ * JJ K *
    planeMat ![(X : Matrix (Fin 2) (Fin 2) K), 1] = JJ K
  rw [planeMat_symp_iff]
  intro k
  fin_cases k
  · exact (J2_symp_iff _).2 (mem_statedSL_iff.1 hX)
  · simp

@[expose] def iotaH : ↥(StatedSL 2 K) →* ↥(StatedSp 2 K) where
  toFun X := ⟨iotaU (X : GL (Fin 2) K), iotaU_mem X.2⟩
  map_one' := Subtype.ext (Units.ext (by
    show planeMat ![((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), 1] = 1
    rw [Units.val_one, planeMat_one_pair]))
  map_mul' X Y := by
    apply Subtype.ext
    apply Units.ext
    show planeMat ![((X : GL (Fin 2) K) * (Y : GL (Fin 2) K)).val, 1] =
      planeMat ![(X : GL (Fin 2) K).val, 1] * planeMat ![(Y : GL (Fin 2) K).val, 1]
    rw [planeMat_pair_mul, Units.val_mul]

theorem iotaH_injective : Function.Injective (iotaH (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have h := congrArg (fun y : ↥(StatedSp 2 K) => ((y : GL Ix K) : Matrix Ix Ix K)) hX
  change planeMat ![(X : GL (Fin 2) K).val, 1] = ((1 : GL Ix K) : Matrix Ix Ix K) at h
  rw [Units.val_one, planeMat_one] at h
  have h0 := congrFun (planeMat_inj h) 0
  apply Subtype.ext
  apply Units.ext
  simpa using h0

@[expose] def D0 (K : Type) [Field K] [CharP K 2] : Subgroup ↥(StatedSp 2 K) :=
  (iotaH (K := K)).range

theorem D0_mem_iff (x : ↥(StatedSp 2 K)) : x ∈ D0 K ↔ ∃ X : ↥(StatedSL 2 K), iotaH X = x :=
  MonoidHom.mem_range

section Centralizer

variable {c : K}

theorem planeMat_symp_det {M : Fin 2 → Matrix (Fin 2) (Fin 2) K}
    (h : (planeMat M)ᵀ * JJ K * planeMat M = JJ K) (k : Fin 2) : (M k).det = 1 :=
  (J2_symp_iff _).1 ((planeMat_symp_iff M).1 h k)

theorem comm_T_of_mem (hc : c ≠ 0) {B x : ↥(StatedSp 2 K)} (hB : mat B = planeMat ![1, Tmat c])
    (hx : x ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))) :
    mat x * planeMat ![1, Tmat c] = planeMat ![1, Tmat c] * mat x := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have h := congrArg mat hx
  rw [mat_mul, mat_mul, hB] at h
  exact h

theorem block_eq (hc : c ≠ 0) {B x : ↥(StatedSp 2 K)} (hB : mat B = planeMat ![1, Tmat c])
    (hx : x ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))) :
    planeMat (fun k => blk (mat x) k) = mat x :=
  planeMat_blk (mat x) (cross_zero hc (comm_T_of_mem hc hB hx))

theorem blk_det_eq_one (hc : c ≠ 0) {B x : ↥(StatedSp 2 K)} (hB : mat B = planeMat ![1, Tmat c])
    (hx : x ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))) (k : Fin 2) :
    (blk (mat x) k).det = 1 := by
  apply planeMat_symp_det (M := fun k => blk (mat x) k) _ k
  rw [block_eq hc hB hx]
  exact mem_mat x

theorem blk_one_comm (hc : c ≠ 0) {B x : ↥(StatedSp 2 K)} (hB : mat B = planeMat ![1, Tmat c])
    (hx : x ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))) :
    blk (mat x) 1 * Tmat c = Tmat c * blk (mat x) 1 := by
  have h := comm_T_of_mem hc hB hx
  rw [← block_eq hc hB hx, planeMat_mul, planeMat_mul] at h
  have := congrFun (planeMat_inj h) 1
  simpa using this

theorem comm_of_Tmat (hc : c ≠ 0) {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : Y * Tmat c = Tmat c * Y)
    (hY' : Y' * Tmat c = Tmat c * Y') : Y * Y' = Y' * Y := by
  obtain ⟨p, q, hp⟩ : ∃ p q : K, Y = p • 1 + q • Tmat c := ⟨_, _, commutant_form hc Y hY⟩
  obtain ⟨p', q', hp'⟩ : ∃ p q : K, Y' = p • 1 + q • Tmat c := ⟨_, _, commutant_form hc Y' hY'⟩
  subst hp hp'
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
    smul_add]
  module

theorem planeMat_comm_block {Mg Mh Mc : Fin 2 → Matrix (Fin 2) (Fin 2) K}
    (h : planeMat Mc * planeMat Mh * planeMat Mg = planeMat Mg * planeMat Mh) :
    Mc 1 * (Mh 1 * Mg 1) = Mg 1 * Mh 1 := by
  rw [planeMat_mul, planeMat_mul, planeMat_mul] at h
  have h1 := congrFun (planeMat_inj h) 1
  simpa [mul_assoc] using h1

theorem eq_one_of_cancel {Yc M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (h : Yc * M = M) : Yc = 1 := by
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  have hinv := Matrix.mul_nonsing_inv M hu
  calc Yc = Yc * (M * M⁻¹) := by rw [hinv, mul_one]
    _ = (Yc * M) * M⁻¹ := by rw [mul_assoc]
    _ = M * M⁻¹ := by rw [h]
    _ = 1 := hinv

theorem comm_mem_D0 (hc : c ≠ 0) {B g h : ↥(StatedSp 2 K)} (hB : mat B = planeMat ![1, Tmat c])
    (hg : g ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K)))
    (hh : h ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))) :
    ⁅g, h⁆ ∈ D0 K := by
  have hcomm : ⁅g, h⁆ ∈ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K)) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have key : ⁅g, h⁆ * h * g = g * h := by
    rw [commutatorElement_def]
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one]
  have hkey : mat ⁅g, h⁆ * mat h * mat g = mat g * mat h := by
    have := congrArg mat key
    simpa only [mat_mul] using this
  have hgb := block_eq hc hB hg
  have hhb := block_eq hc hB hh
  have hcb := block_eq hc hB hcomm
  rw [← hcb, ← hhb, ← hgb] at hkey
  have hYc := planeMat_comm_block hkey
  have hYgh : blk (mat g) 1 * blk (mat h) 1 = blk (mat h) 1 * blk (mat g) 1 :=
    comm_of_Tmat hc (blk_one_comm hc hB hg) (blk_one_comm hc hB hh)
  have hdetM : (blk (mat h) 1 * blk (mat g) 1).det = 1 := by
    rw [Matrix.det_mul, blk_det_eq_one hc hB hh 1, blk_det_eq_one hc hB hg 1, mul_one]
  rw [hYgh] at hYc
  have hY1 : blk (mat ⁅g, h⁆) 1 = 1 := eq_one_of_cancel hdetM hYc
  have hmat : mat ⁅g, h⁆ = planeMat ![blk (mat ⁅g, h⁆) 0, 1] := by
    calc mat ⁅g, h⁆ = planeMat (fun k => blk (mat ⁅g, h⁆) k) := hcb.symm
      _ = planeMat ![blk (mat ⁅g, h⁆) 0, 1] := by
        congr 1
        funext k
        fin_cases k
        · rfl
        · exact hY1
  have hdet0 : (blk (mat ⁅g, h⁆) 0).det = 1 := blk_det_eq_one hc hB hcomm 0
  have hne : (blk (mat ⁅g, h⁆) 0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hmemSL : Matrix.GeneralLinearGroup.mkOfDetNeZero (blk (mat ⁅g, h⁆) 0) hne ∈ StatedSL 2 K := by
    rw [mem_statedSL_iff]
    exact hdet0
  rw [D0_mem_iff]
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (blk (mat ⁅g, h⁆) 0) hne, hmemSL⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hmat.symm

theorem D0_le_centralizer (hc : c ≠ 0) {B : ↥(StatedSp 2 K)} (hB : mat B = planeMat ![1, Tmat c]) :
    D0 K ≤ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K)) := by
  intro x hx
  obtain ⟨X, rfl⟩ := (D0_mem_iff _).1 hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  show mat (iotaH X) * mat B = mat B * mat (iotaH X)
  have hmat : mat (iotaH X) = planeMat ![((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), 1] := rfl
  rw [hmat, hB, planeMat_mul, planeMat_mul]
  congr 1
  funext k
  fin_cases k <;> simp

theorem components_eq_D0 [Finite K] (hc : c ≠ 0) {B : ↥(StatedSp 2 K)}
    (hB : mat B = planeMat ![1, Tmat c])
    [IsSimpleGroup ↥(D0 K)] {I : Subgroup ↥(StatedSp 2 K)}
    (hI : GLAPComponent 3 (Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))) I) : I = D0 K := by
  have hIC : I ≤ Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K)) := hI.1
  have hID : I ≤ D0 K := by
    calc I = ⁅I, I⁆ := (glaPComponent_perfect hI).symm
      _ ≤ ⁅Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K)),
            Subgroup.centralizer ({B} : Set ↥(StatedSp 2 K))⁆ := Subgroup.commutator_mono hIC hIC
      _ ≤ D0 K := by
        rw [Subgroup.commutator_le]
        intro g hg h hh
        exact comm_mem_D0 hc hB hg hh
  have hsub : CFSG.Open.IsSubnormal (I ⊓ D0 K) (D0 K) :=
    hI.2.1.inf_of_le (D0_le_centralizer hc hB)
  rw [inf_eq_left.2 hID] at hsub
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub inferInstance with h | h
  · exact absurd h (glaPComponent_ne_bot' hI)
  · exact h

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
