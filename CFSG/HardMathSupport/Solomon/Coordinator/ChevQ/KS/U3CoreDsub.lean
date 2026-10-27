module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreModel
public import Certificates.Certificate36922
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F CFSG.RankThree.PartTwo.Sec19.U38F
  CFSG.RankThree.PartTwo.Sec19 Matrix

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section D

variable {F : Type} [Field F]

@[expose] noncomputable def Dsub (h : UnitaryFieldData 2 3 F) (σ : F ≃+* F) :
    Subgroup (MulAut (unitarySU 2 3 F 3)) :=
  (suConj h).range ⊓ Subgroup.centralizer ({suField h σ} : Set (MulAut (unitarySU 2 3 F 3)))

theorem u38RCheck_parts :
    KSU38R.expCheck () = true ∧ KSU38R.noV4Check () = true ∧ KSU38R.repCheck () = true ∧
      KSU38R.e0Check () = true ∧ KSU38R.regCheck () = true ∧ KSU38R.dCheck () = true := by
  have h := Certificates.certificate36922
  simp only [KSU38R.u38RCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem exists_map_eq_smul_of_commute (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F}
    {W : unitaryIsom3 h} (hc : suConj h W * suField h σ = suField h σ * suConj h W) :
    ∃ c : F, ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      c • ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have := h.finite
  have hconj : suConj h ⟨glAut σ (W : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ W.2⟩ =
      suConj h W := by
    rw [← suField_mul_suConj_mul_inv, ← hc, mul_inv_cancel_right]
  have hker : suConj h (W⁻¹ * ⟨glAut σ (W : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ W.2⟩) = 1 := by
    rw [map_mul, map_inv, hconj, inv_mul_cancel]
  obtain ⟨lam, hlam⟩ := scalar_of_suConj_eq_one h hker
  refine ⟨lam, ?_⟩
  have e : glAut σ (W : GL (Fin 3) F) = (W : GL (Fin 3) F) *
      ((W : GL (Fin 3) F)⁻¹ * glAut σ (W : GL (Fin 3) F)) := by group
  have hl2 : ((((W : GL (Fin 3) F)⁻¹ * glAut σ (W : GL (Fin 3) F) : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F) = lam • 1 := hlam
  rw [← coe_glAut, e, Units.val_mul, hl2, Matrix.mul_smul, Matrix.mul_one]

theorem toMat_mpow (ι : Q8 →+* F) (Ym : M3 Q8) (n : ℕ) :
    toMat ι (KSU38R.mpow Ym n) = (toMat ι Ym) ^ n := by
  induction n with
  | zero => simp [KSU38R.mpow, toMat_one]
  | succ n ih => rw [KSU38R.mpow, toMat_mul, ih, pow_succ']

theorem suConj_pow_eq_one_of_scalar (h : UnitaryFieldData 2 3 F) (Y : unitaryIsom3 h) (n : ℕ)
    {c : F} (hY : ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ n = c • 1) :
    suConj h Y ^ n = 1 := by
  rw [← map_pow]
  apply suConj_eq_one_of_scalar_u38 h (c := c)
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  exact hY

theorem exists_toIsom_of_commute (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {ι : Q8 →+* F} (hωι : IsPrimitiveRoot (ι w0) 3)
    {W : unitaryIsom3 h} (hc : suConj h W * suField h σ = suField h σ * suConj h W) :
    ∃ (Ym : M3 Q8) (hu : unitaryOk Ym = true), entriesL4 Ym = true ∧
      suConj h W = suConj h (toIsom h ι Ym hu) := by
  obtain ⟨b, Ym, hb, hYe, hYu, hWb⟩ :=
    exists_gu2_decomp h hσ hωι (exists_map_eq_smul_of_commute h hc)
  refine ⟨Ym, hYu, hYe, ?_⟩
  set Y' := toIsom h ι Ym hYu with hY'
  have hY'm : (((Y' : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι Ym :=
    coe_toIsom h ι Ym hYu
  rw [← hY'm] at hWb
  have hmat : (((Y'⁻¹ * W : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      b • 1 := by
    have h1 : (((Y'⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((Y' : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    calc (((Y'⁻¹ * W : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        = (((Y'⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
            rw [Subgroup.coe_mul, Units.val_mul]
      _ = (((Y'⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (b • (((Y' : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
            rw [hWb]
      _ = b • ((((Y'⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((Y' : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
            rw [Matrix.mul_smul]
      _ = b • 1 := by rw [h1]
  have h1 : suConj h (Y'⁻¹ * W) = 1 := suConj_eq_one_of_scalar_u38 h hmat
  rw [map_mul, map_inv] at h1
  exact (inv_mul_eq_one.1 h1).symm

theorem pow_twelve_eq_one_of_mem_Dsub
    (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {d : MulAut (unitarySU 2 3 F 3)} (hd : d ∈ Dsub h σ) : d ^ 12 = 1 := by
  obtain ⟨⟨W, hW⟩, hdc⟩ := hd
  have hdc' : d ∈ Subgroup.centralizer ({suField h σ} : Set (MulAut (unitarySU 2 3 F 3))) := hdc
  rw [Subgroup.mem_centralizer_singleton_iff] at hdc'
  have hc : suConj h W * suField h σ = suField h σ * suConj h W := by rw [hW]; exact hdc'
  obtain ⟨ι, hι, hωι, hσω⟩ := exists_model38 h hσ
  obtain ⟨Ym, hu, he, hWd⟩ := exists_toIsom_of_commute h hσ hωι hc
  have hexp : forallUnitary (fun A => isScalar (KSU38R.mpow A 12)) = true :=
    (u38RCheck_parts).1
  have hscal : isScalar (KSU38R.mpow Ym 12) = true := forallUnitary_sound hexp he hu
  have hm := toMat_scalar_of_isScalar ι hscal
  rw [← hW, hWd]
  apply suConj_pow_eq_one_of_scalar h _ 12 (c := ι (KSU38R.mpow Ym 12).a00)
  rw [coe_toIsom, ← toMat_mpow]
  exact hm

theorem exists_toIsom_of_mem_Dsub (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {ι : Q8 →+* F} (hωι : IsPrimitiveRoot (ι w0) 3) {d : MulAut (unitarySU 2 3 F 3)}
    (hd : d ∈ Dsub h σ) :
    ∃ (Ym : M3 Q8) (hu : unitaryOk Ym = true), entriesL4 Ym = true ∧
      d = suConj h (toIsom h ι Ym hu) := by
  obtain ⟨⟨W, hW⟩, hdc⟩ := hd
  have hdc' : d ∈ Subgroup.centralizer ({suField h σ} : Set (MulAut (unitarySU 2 3 F 3))) := hdc
  rw [Subgroup.mem_centralizer_singleton_iff] at hdc'
  have hc : suConj h W * suField h σ = suField h σ * suConj h W := by rw [hW]; exact hdc'
  obtain ⟨Ym, hu, he, hWd⟩ := exists_toIsom_of_commute h hσ hωι hc
  exact ⟨Ym, hu, he, by rw [← hW, hWd]⟩

theorem suConj_toIsom_eq_one_iff (h : UnitaryFieldData 2 3 F) {ι : Q8 →+* F} (hι : Function.Surjective ι)
    (Ym : M3 Q8) (hu : unitaryOk Ym = true) :
    suConj h (toIsom h ι Ym hu) = 1 ↔ isScalar Ym = true := by
  constructor
  · intro h1
    obtain ⟨c, hc⟩ := scalar_of_suConj_eq_one h h1
    rw [coe_toIsom] at hc
    exact isScalar_of_toMat ι hc
  · intro h1
    exact suConj_eq_one_of_scalar_u38 h (c := ι Ym.a00) (by rw [coe_toIsom]; exact toMat_scalar_of_isScalar ι h1)

theorem suConj_toIsom_pow_eq_one_iff (h : UnitaryFieldData 2 3 F) {ι : Q8 →+* F}
    (hι : Function.Surjective ι) (Ym : M3 Q8) (hu : unitaryOk Ym = true) (n : ℕ) :
    suConj h (toIsom h ι Ym hu) ^ n = 1 ↔ isScalar (KSU38R.mpow Ym n) = true := by
  constructor
  · intro h1
    rw [← map_pow] at h1
    obtain ⟨c, hc⟩ := scalar_of_suConj_eq_one h h1
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_toIsom, ← toMat_mpow] at hc
    exact isScalar_of_toMat ι hc
  · intro h1
    apply suConj_pow_eq_one_of_scalar h _ n (c := ι (KSU38R.mpow Ym n).a00)
    rw [coe_toIsom, ← toMat_mpow]
    exact toMat_scalar_of_isScalar ι h1

theorem suConj_eq_of_matrix_eq_smul (h : UnitaryFieldData 2 3 F) {P Q : unitaryIsom3 h} {c : F}
    (hPQ : ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c • ((Q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : suConj h P = suConj h Q := by
  have h1 : suConj h (Q⁻¹ * P) = 1 := by
    apply suConj_eq_one_of_scalar_u38 h (c := c)
    rw [Subgroup.coe_mul, Units.val_mul, hPQ, Matrix.mul_smul]
    have : (((Q⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((Q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    rw [this]
  rw [map_mul, map_inv] at h1
  exact (inv_mul_eq_one.1 h1).symm

theorem exists_matrix_eq_smul_of_suConj_eq (h : UnitaryFieldData 2 3 F) {P Q : unitaryIsom3 h}
    (hPQ : suConj h P = suConj h Q) :
    ∃ c : F, ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c • ((Q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : suConj h (Q⁻¹ * P) = 1 := by rw [map_mul, map_inv, hPQ, inv_mul_cancel]
  obtain ⟨c, hc⟩ := scalar_of_suConj_eq_one h h1
  refine ⟨c, ?_⟩
  have hP : (P : GL (Fin 3) F) = (Q : GL (Fin 3) F) * ((Q⁻¹ * P : unitaryIsom3 h) : GL (Fin 3) F) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hP, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one]

theorem suConj_toIsom_comm_iff (h : UnitaryFieldData 2 3 F) {ι : Q8 →+* F}
    (hι : Function.Surjective ι) (Um Vm : M3 Q8) (hU : unitaryOk Um = true)
    (hV : unitaryOk Vm = true) :
    suConj h (toIsom h ι Um hU) * suConj h (toIsom h ι Vm hV) =
      suConj h (toIsom h ι Vm hV) * suConj h (toIsom h ι Um hU) ↔
        KSU38R.commMod Um Vm = true := by
  set U' := toIsom h ι Um hU with hU'
  set V' := toIsom h ι Vm hV with hV'
  have hmU : ((U' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι Um := coe_toIsom h ι Um hU
  have hmV : ((V' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι Vm := coe_toIsom h ι Vm hV
  have hUV : (((U' * V' : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      toMat ι (Um * Vm) := by
    rw [Subgroup.coe_mul, Units.val_mul, hmU, hmV, toMat_mul]
  have hVU : (((V' * U' : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      toMat ι (Vm * Um) := by
    rw [Subgroup.coe_mul, Units.val_mul, hmU, hmV, toMat_mul]
  constructor
  · intro hc
    have h1 : suConj h (U' * V') = suConj h (V' * U') := by rw [map_mul, map_mul, hc]
    obtain ⟨c, hcc⟩ := exists_matrix_eq_smul_of_suConj_eq h h1
    obtain ⟨l, rfl⟩ := hι c
    rw [hUV, hVU, ← toMat_smul] at hcc
    have := toMat_inj ι hcc
    exact decide_eq_true ⟨l, this⟩
  · intro hcm
    obtain ⟨l, hl⟩ := of_decide_eq_true hcm
    have h1 : suConj h (U' * V') = suConj h (V' * U') := by
      apply suConj_eq_of_matrix_eq_smul h (c := ι l)
      rw [hUV, hVU, ← toMat_smul, hl]
    rw [map_mul, map_mul] at h1
    exact h1

theorem propto_of_commMod_of_isInvol {U V : M3 Q8}
    (hUe : entriesL4 U = true) (hUu : unitaryOk U = true) (hVe : entriesL4 V = true)
    (hVu : unitaryOk V = true) (hIU : KSU38R.isInvol U = true) (hIV : KSU38R.isInvol V = true)
    (hcm : KSU38R.commMod U V = true) : KSU38R.propto U V = true := by
  have h := (u38RCheck_parts).2.1
  simp only [KSU38R.noV4Check, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hU := forallUnitary_sound h1 hUe hUu
  have hV := forallUnitary_sound h1 hVe hVu
  simp only [hIU, hIV, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hU hV
  have h3 := (List.all_eq_true.1 ((List.all_eq_true.1 h2) U hU)) V hV
  simpa [hcm] using h3

theorem eq_of_commute_involutions_of_mem_Dsub
    (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {u v : MulAut (unitarySU 2 3 F 3)} (hu : u ∈ Dsub h σ) (hv : v ∈ Dsub h σ) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (huv : u * v = v * u) : u = 1 ∨ v = 1 ∨ u = v := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  by_cases hv1 : v = 1
  · exact Or.inr (Or.inl hv1)
  right; right
  obtain ⟨ι, hι, hωι, hσω⟩ := exists_model38 h hσ
  obtain ⟨Um, hUu, hUe, hUd⟩ := exists_toIsom_of_mem_Dsub h hσ hωι hu
  obtain ⟨Vm, hVu, hVe, hVd⟩ := exists_toIsom_of_mem_Dsub h hσ hωι hv
  subst hUd
  subst hVd
  have hUns : isScalar Um = false := by
    by_contra hcon
    exact hu1 ((suConj_toIsom_eq_one_iff h hι Um hUu).2 (Bool.eq_true_of_not_eq_false hcon))
  have hVns : isScalar Vm = false := by
    by_contra hcon
    exact hv1 ((suConj_toIsom_eq_one_iff h hι Vm hVu).2 (Bool.eq_true_of_not_eq_false hcon))
  have hsq : ∀ (Xm : M3 Q8) (hX : unitaryOk Xm = true),
      suConj h (toIsom h ι Xm hX) ^ 2 = 1 → isScalar (Xm * Xm) = true := by
    intro Xm hX hX2
    rw [← map_pow] at hX2
    obtain ⟨c, hc⟩ := scalar_of_suConj_eq_one h hX2
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_toIsom, pow_two, ← toMat_mul] at hc
    exact isScalar_of_toMat ι hc
  have hUsq := hsq Um hUu hu2
  have hVsq := hsq Vm hVu hv2
  have hIU : KSU38R.isInvol Um = true := by simp [KSU38R.isInvol, hUns, hUsq]
  have hIV : KSU38R.isInvol Vm = true := by simp [KSU38R.isInvol, hVns, hVsq]
  have hcm : KSU38R.commMod Um Vm = true := (suConj_toIsom_comm_iff h hι Um Vm hUu hVu).1 huv
  obtain ⟨l, hl⟩ := of_decide_eq_true
    (propto_of_commMod_of_isInvol hUe hUu hVe hVu hIU hIV hcm)
  apply suConj_eq_of_matrix_eq_smul h (c := ι l)
  rw [coe_toIsom, coe_toIsom, ← toMat_smul, hl]

end D

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
