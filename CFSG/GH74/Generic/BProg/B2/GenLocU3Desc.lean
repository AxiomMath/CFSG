module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.GH74.Generic.BProg.B2.GenLocL3NFLin
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU3Desc

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.Generic.BProg.B2

variable {p f : ℕ} {F : Type} [Field F]

theorem exists_mul_map_eq_self (h : UnitaryFieldData p f F) (hq : 3 ≤ p ^ f)
    (A : Matrix (Fin 3) (Fin 3) F) (hA : A * A.map h.bar = 1) :
    ∃ H : GL (Fin 3) F, A * (H : Matrix (Fin 3) (Fin 3) F).map h.bar = H := by
  classical
  have : Finite F := h.finite
  by_contra hno
  push Not at hno
  have hsing : ∀ z : F, (z • (1 : Matrix (Fin 3) (Fin 3) F) + h.bar z • A).det = 0 := by
    intro z
    by_contra hz
    set Hz : Matrix (Fin 3) (Fin 3) F := z • (1 : Matrix (Fin 3) (Fin 3) F) + h.bar z • A with hHz
    apply hno (Matrix.GeneralLinearGroup.mkOfDetNeZero Hz hz)
    have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero Hz hz : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Hz := rfl
    rw [hcoe]
    have hm : Hz.map h.bar =
        h.bar z • (1 : Matrix (Fin 3) (Fin 3) F) + z • A.map h.bar := by
      rw [hHz]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
        h.bar_bar]
      simp [Matrix.one_apply]
    rw [hm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hA, Matrix.mul_one, hHz]
    abel
  set χ := A.charpoly with hχ
  have hroot : ∀ u : (Units.map h.normHom).ker, -((u : Fˣ) : F) ∈ χ.roots.toFinset := by
    intro u
    have hu : h.norm ((u : Fˣ) : F) = 1 := (h.mem_ker_normUnits).1 u.2
    obtain ⟨r, hr, hru⟩ := h.exists_div_bar_eq hu
    have hr' : h.bar r ≠ 0 := (h.bar_eq_zero_iff).not.mpr hr
    have hrr : r = ((u : Fˣ) : F) * h.bar r := by
      rw [← hru]; field_simp
    have h1 := hsing r
    have h2 : (r • (1 : Matrix (Fin 3) (Fin 3) F) + h.bar r • A) =
        h.bar r • (((u : Fˣ) : F) • (1 : Matrix (Fin 3) (Fin 3) F) + A) := by
      have h7 : h.bar r * ((u : Fˣ) : F) = r := (mul_comm _ _).trans hrr.symm
      rw [smul_add, smul_smul, h7]
    rw [h2, Matrix.det_smul] at h1
    have h3 : (((u : Fˣ) : F) • (1 : Matrix (Fin 3) (Fin 3) F) + A).det = 0 := by
      rcases mul_eq_zero.1 h1 with h4 | h4
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h4) hr'
      · exact h4
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero,
      Polynomial.IsRoot, Matrix.eval_charpoly]
    have h5 : (Matrix.scalar (Fin 3) (-((u : Fˣ) : F)) - A) =
        -(((u : Fˣ) : F) • (1 : Matrix (Fin 3) (Fin 3) F) + A) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> ring
    rw [h5, Matrix.det_neg, h3, mul_zero]
  have hinj : Function.Injective (fun u : (Units.map h.normHom).ker => (⟨-((u : Fˣ) : F), hroot u⟩ : ↥χ.roots.toFinset)) := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    have h2 : ((a : Fˣ) : F) = ((b : Fˣ) : F) := neg_inj.1 h1
    exact Subtype.ext (Units.ext h2)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [(h.card_ker_normUnits_and_surjective).1, Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  have h6 : χ.roots.toFinset.card ≤ 3 := by
    calc χ.roots.toFinset.card ≤ Multiset.card χ.roots := Multiset.toFinset_card_le _
      _ ≤ χ.natDegree := Polynomial.card_roots' χ
      _ = 3 := by rw [hχ, Matrix.charpoly_natDegree_eq_dim]; simp
  omega


theorem transpose_eq_of_unitary (h : UnitaryFieldData p f F) (A : Matrix (Fin 3) (Fin 3) F)
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = 1) : Aᵀ = A := by
  have h1 : (A.map h.bar)ᵀ = A.map h.bar := by
    calc (A.map h.bar)ᵀ = (A.map h.bar)ᵀ * (A * A.map h.bar) := by rw [hAA, Matrix.mul_one]
      _ = ((A.map h.bar)ᵀ * A) * A.map h.bar := by rw [Matrix.mul_assoc]
      _ = A.map h.bar := by rw [hAu, Matrix.one_mul]
  have h2 : (A.map h.bar).map h.bar = A := by
    ext i j; simp [h.bar_bar]
  calc Aᵀ = ((A.map h.bar).map h.bar)ᵀ := by rw [h2]
    _ = ((A.map h.bar)ᵀ).map h.bar := by rw [Matrix.transpose_map]
    _ = A := by rw [h1, h2]

theorem two_ne_zero' (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  have := h.charP
  intro h0
  have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff F p] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 h1)

theorem map_bar_bar (h : UnitaryFieldData p f F) (A : Matrix (Fin 3) (Fin 3) F) :
    (A.map h.bar).map h.bar = A := by
  ext i j; simp [h.bar_bar]

theorem exists_unitary_frame (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ f)
    (A : GL (Fin 3) F)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    {ι : Type} [Finite ι] (R : ι → GL (Fin 3) F)
    (hRu : ∀ i, (((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1)
    (hsq : ∀ i, R i * R i = 1) (hcomm : ∀ i j, R i * R j = R j * R i)
    (hAR : ∀ i, (A : Matrix (Fin 3) (Fin 3) F) *
      ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
      ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) :
    ∃ C : GL (Fin 3) F,
      ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      (∀ i, ∃ D : Matrix (Fin 3) (Fin 3) F, D.IsDiag ∧
        ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * C = C * D) ∧
      ∃ D : Matrix (Fin 3) (Fin 3) F, D.IsDiag ∧
        (A : Matrix (Fin 3) (Fin 3) F) * (C : Matrix (Fin 3) (Fin 3) F).map h.bar = C * D := by
  classical
  have : Finite F := h.finite
  have h2 : (2 : F) ≠ 0 := two_ne_zero' h hp2
  set Am : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hAm
  obtain ⟨H₀, hH₀⟩ := exists_mul_map_eq_self h hq Am hAA
  set Hm : Matrix (Fin 3) (Fin 3) F := (H₀ : Matrix (Fin 3) (Fin 3) F) with hHm
  have hsymm : Amᵀ = Am := transpose_eq_of_unitary h Am hAu hAA
  have hX : Hmᵀ * Hm.map h.bar = (Hm.map h.bar)ᵀ * Hm := by
    have h1 : Hmᵀ = (Hm.map h.bar)ᵀ * Am := by
      conv_lhs => rw [← hH₀]
      rw [Matrix.transpose_mul, hsymm]
    rw [h1, Matrix.mul_assoc, hH₀]
  set S : Matrix (Fin 3) (Fin 3) F := (Hm.map h.bar)ᵀ * Hm with hS
  have hSbar : S.map h.bar = S := by
    have e1 : ((Hm.map h.bar)ᵀ).map h.bar = Hmᵀ := by rw [← Matrix.transpose_map, map_bar_bar]
    rw [hS, Matrix.map_mul, e1, hX]
  have hSsymm : Sᵀ = S := by
    rw [hS, Matrix.transpose_mul, Matrix.transpose_transpose, hX]
  have hSL : ∀ i j, S i j ∈ h.fixedField := fun i j =>
    h.mem_fixedField.2 (by simpa using congrFun (congrFun hSbar i) j)
  have hdetH : Hm.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit H₀)).ne_zero
  have hinvH : ((H₀⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Hm = 1 := by
    rw [hHm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set R' : ι → GL (Fin 3) F := fun i => H₀⁻¹ * R i * H₀ with hR'
  have hR'Hm : ∀ i, Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Hm := by
    intro i
    have : H₀ * R' i = R i * H₀ := by simp only [hR']; group
    have h1 := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) this
    simpa [Units.val_mul] using h1
  have hR'bar : ∀ i, ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
      ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro i
    have e1 : Hm.map h.bar * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
        ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar * Hm.map h.bar := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hR'Hm i]
    have e2 : Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
        Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      calc Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar
          = (Am * Hm.map h.bar) * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar := by
            rw [hH₀]
        _ = Am * (Hm.map h.bar * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar) := by
            rw [Matrix.mul_assoc]
        _ = Am * (((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar * Hm.map h.bar) := by
            rw [e1]
        _ = (Am * ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar) * Hm.map h.bar := by
            rw [Matrix.mul_assoc]
        _ = (((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Am) * Hm.map h.bar := by
            rw [hAR i]
        _ = ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Am * Hm.map h.bar) := by
            rw [Matrix.mul_assoc]
        _ = ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Hm := by rw [hH₀]
        _ = Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := (hR'Hm i).symm
    have e3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F =>
      ((H₀⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M) e2
    simpa only [← Matrix.mul_assoc, hinvH, Matrix.one_mul] using e3
  have hRL : ∀ i a b, ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) a b ∈ h.fixedField :=
    fun i a b => h.mem_fixedField.2 (by simpa using congrFun (congrFun (hR'bar i) a) b)
  have hcomm' : ∀ i j, R' i * R' j = R' j * R' i := by
    intro i j
    calc R' i * R' j = H₀⁻¹ * (R i * R j) * H₀ := by simp only [hR']; group
      _ = H₀⁻¹ * (R j * R i) * H₀ := by rw [hcomm i j]
      _ = R' j * R' i := by simp only [hR']; group
  have hsq' : ∀ i, R' i * R' i = 1 := by
    intro i
    calc R' i * R' i = H₀⁻¹ * (R i * R i) * H₀ := by simp only [hR']; group
      _ = 1 := by rw [hsq i]; group
  have hiso' : ∀ i, ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * S *
      ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = S := by
    intro i
    have e1 : Hm.map h.bar * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
        ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar * Hm.map h.bar := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hR'Hm i]
    have hT : ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
        (((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ := by rw [hR'bar i]
    calc ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * S *
          ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        = (((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * ((Hm.map h.bar)ᵀ * Hm) *
          ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [hT]
      _ = (Hm.map h.bar * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
          (Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar * Hm.map h.bar)ᵀ *
          (((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Hm) := by rw [e1, hR'Hm i]
      _ = (Hm.map h.bar)ᵀ * ((((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
          ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * Hm := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = S := by rw [hRu i, Matrix.mul_one]
  obtain ⟨C₀, hC₀L, hdiag, hTdiag⟩ := GenLocL3NFLin.exists_orth_conj_diag_sub h.fixedField h2 S
    hSsymm hSL R' hRL hcomm' hsq' hiso'

  set T : Matrix (Fin 3) (Fin 3) F := (C₀ : Matrix (Fin 3) (Fin 3) F)ᵀ * S * (C₀ : Matrix (Fin 3) (Fin 3) F) with hT
  have hC₀bar : (C₀ : Matrix (Fin 3) (Fin 3) F).map h.bar = C₀ := by
    ext i j
    exact h.mem_fixedField.1 (hC₀L i j)
  have hTbar : T.map h.bar = T := by
    rw [hT, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hC₀bar, hSbar]
  have hc : ∀ i, T i i ∈ h.fixedField := fun i =>
    h.mem_fixedField.2 (by simpa using congrFun (congrFun hTbar i) i)
  have hdetS : S.det ≠ 0 := by
    rw [hS, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((h.bar_eq_zero_iff).not.mpr hdetH) hdetH
  have hdetC₀ : (C₀ : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit C₀)).ne_zero
  have hdetT : T.det ≠ 0 := by
    rw [hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetC₀ hdetS) hdetC₀
  obtain ⟨c, hcT⟩ : ∃ c : Fin 3 → F, Matrix.diagonal c = T := ⟨_, hTdiag.diagonal_diag⟩
  have hci : ∀ i, c i = T i i := fun i => by rw [← hcT]; simp
  have hcL : ∀ i, c i ∈ h.fixedField := fun i => by rw [hci]; exact hc i
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    have := hdetT
    rw [← hcT, Matrix.det_diagonal] at this
    exact (Finset.prod_ne_zero_iff.1 this) i (Finset.mem_univ i)
  have hex : ∀ i, ∃ d : F, h.norm d = (c i)⁻¹ := fun i => by
    obtain ⟨d, hd⟩ := h.normHom_surjective ⟨(c i)⁻¹, h.fixedField.inv_mem (hcL i)⟩
    exact ⟨d, by simpa using congrArg Subtype.val hd⟩
  choose d hd using hex
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    have h1 := hd i
    rw [h0] at h1
    simp only [UnitaryFieldData.norm, map_zero, mul_zero] at h1
    exact hc0 i (inv_eq_zero.1 h1.symm)
  set Dd : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal d with hDd
  have hdetD : Dd.det ≠ 0 := by
    rw [hDd, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd0 i
  set Cm : Matrix (Fin 3) (Fin 3) F := Hm * (C₀ : Matrix (Fin 3) (Fin 3) F) * Dd with hCm
  have hdetC : Cm.det ≠ 0 := by
    rw [hCm, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hdetH hdetC₀) hdetD
  have hCbar : Cm.map h.bar = Hm.map h.bar * (C₀ : Matrix (Fin 3) (Fin 3) F) *
      Matrix.diagonal (fun i => h.bar (d i)) := by
    rw [hCm, Matrix.map_mul, Matrix.map_mul, hC₀bar, hDd, Matrix.diagonal_map (map_zero _)]
  have hCu : (Cm.map h.bar)ᵀ * Cm = 1 := by
    have hDt : (Matrix.diagonal (fun i => h.bar (d i)))ᵀ = Matrix.diagonal (fun i => h.bar (d i)) :=
      Matrix.diagonal_transpose _
    calc (Cm.map h.bar)ᵀ * Cm
        = Matrix.diagonal (fun i => h.bar (d i)) * ((C₀ : Matrix (Fin 3) (Fin 3) F)ᵀ *
            ((Hm.map h.bar)ᵀ * Hm) * (C₀ : Matrix (Fin 3) (Fin 3) F)) * Dd := by
          rw [hCbar, hCm]
          simp only [Matrix.transpose_mul, hDt, Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => h.bar (d i)) * T * Dd := by rw [hT, hS]
      _ = 1 := by
          rw [← hcT, hDd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
            ← Matrix.diagonal_one]
          congr 1
          ext i
          have h1 := hd i
          simp only [UnitaryFieldData.norm] at h1
          calc h.bar (d i) * c i * d i = c i * (d i * h.bar (d i)) := by ring
            _ = 1 := by rw [h1]; exact mul_inv_cancel₀ (hc0 i)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hdetC, hCu, fun i => ?_, ?_⟩
  · refine ⟨((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdiag i, ?_⟩
    have hE : ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.diagonal (fun j => ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j) :=
      ((hdiag i).diagonal_diag).symm
    have hC₀E : (C₀ : Matrix (Fin 3) (Fin 3) F) *
        ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * C₀ := by
      have : C₀ * (C₀⁻¹ * R' i * C₀) = R' i * C₀ := by group
      have h1 := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) this
      simpa [Units.val_mul] using h1
    have hcomm2 : Dd * ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Dd := by
      rw [hE, hDd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      ext j
      ring
    show ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Cm = Cm * _
    calc ((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Cm
        = (((R i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Hm) * (C₀ : Matrix (Fin 3) (Fin 3) F) * Dd := by
          rw [hCm]; simp only [Matrix.mul_assoc]
      _ = (Hm * ((R' i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * (C₀ : Matrix (Fin 3) (Fin 3) F) * Dd := by
          rw [hR'Hm i]
      _ = Hm * ((C₀ : Matrix (Fin 3) (Fin 3) F) *
          ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * Dd := by
          rw [hC₀E, Matrix.mul_assoc Hm]
      _ = Hm * (C₀ : Matrix (Fin 3) (Fin 3) F) * (((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * Dd) := by simp only [Matrix.mul_assoc]
      _ = Hm * (C₀ : Matrix (Fin 3) (Fin 3) F) * (Dd * ((C₀⁻¹ * R' i * C₀ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)) := by rw [hcomm2]
      _ = Cm * _ := by rw [hCm]; simp only [Matrix.mul_assoc]
  · refine ⟨Matrix.diagonal (fun i => (d i)⁻¹ * h.bar (d i)), Matrix.isDiag_diagonal _, ?_⟩
    show Am * Cm.map h.bar = Cm * _
    rw [hCbar, hCm, ← Matrix.mul_assoc Am, ← Matrix.mul_assoc Am, hH₀, hDd,
      Matrix.mul_assoc _ (Matrix.diagonal d), Matrix.diagonal_mul_diagonal]
    congr 2
    ext i : 1
    rw [mul_inv_cancel_left₀ (hd0 i)]

end CFSG.GH74.Generic.BProg.B2.GenLocU3Desc
