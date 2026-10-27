module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
import all CFSG.Fischer.F4
public import CFSG.Fischer.TransvectionPointsBase

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

@[expose] def fvec (φ : F4 ≃+* F4) (x : W) : W := fun i => φ (x i)

theorem fvec_apply (φ : F4 ≃+* F4) (x : W) (i : Fin 6) : fvec φ x i = φ (x i) := rfl

theorem fvec_add (φ : F4 ≃+* F4) (x y : W) : fvec φ (x + y) = fvec φ x + fvec φ y := by
  funext i
  simp [fvec]

theorem fvec_smul (φ : F4 ≃+* F4) (c : F4) (x : W) : fvec φ (c • x) = φ c • fvec φ x := by
  funext i
  simp [fvec]

theorem fvec_zero (φ : F4 ≃+* F4) : fvec φ 0 = 0 := by
  funext i
  simp [fvec]

theorem fvec_symm_fvec (φ : F4 ≃+* F4) (x : W) : fvec φ.symm (fvec φ x) = x := by
  funext i
  simp [fvec]

theorem fvec_fvec_symm (φ : F4 ≃+* F4) (x : W) : fvec φ (fvec φ.symm x) = x := by
  funext i
  simp [fvec]

theorem fvec_ne_zero (φ : F4 ≃+* F4) {x : W} (hx : x ≠ 0) : fvec φ x ≠ 0 := by
  intro h
  apply hx
  rw [← fvec_symm_fvec φ x, h, fvec_zero]

theorem hermStd_fvec (φ : F4 ≃+* F4) (x y : W) :
    hermStd (fvec φ x) (fvec φ y) = φ (hermStd x y) := by
  simp only [hermStd, fvec, map_sum, map_mul, map_pow]

theorem map_mulVec_fvec (φ : F4 ≃+* F4) (M : Matrix (Fin 6) (Fin 6) F4) (x : W) :
    (M.map φ) *ᵥ fvec φ x = fvec φ (M *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (φ : F4 →+* F4) M x i).symm

theorem cube_eq_one : ∀ c : F4, c ≠ 0 → c * c * c = 1 := by decide

theorem inv_mulVec_mulVec' (g : GL (Fin 6) F4) (x : W) :
    ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) F4) *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

@[expose] def semiVec (A : GU0) (φ : F4 ≃+* F4) (w : W) : W :=
  ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fvec φ w

theorem semiVec_add (A : GU0) (φ : F4 ≃+* F4) (x y : W) :
    semiVec A φ (x + y) = semiVec A φ x + semiVec A φ y := by
  rw [semiVec, fvec_add, mulVec_add]
  rfl

theorem semiVec_smul (A : GU0) (φ : F4 ≃+* F4) (c : F4) (x : W) :
    semiVec A φ (c • x) = φ c • semiVec A φ x := by
  rw [semiVec, fvec_smul, mulVec_smul]
  rfl

theorem semiVec_ne_zero (A : GU0) (φ : F4 ≃+* F4) {w : W} (hw : w ≠ 0) : semiVec A φ w ≠ 0 :=
  mulVec_ne_zero _ (fvec_ne_zero φ hw)

theorem hermStd_semiVec (A : GU0) (φ : F4 ≃+* F4) (x y : W) :
    hermStd (semiVec A φ x) (semiVec A φ y) = φ (hermStd x y) := by
  rw [semiVec, semiVec, hermStd_mulVec, hermStd_fvec]

theorem semiVec_iso (A : GU0) (φ : F4 ≃+* F4) {w : W} (hw : hermStd w w = 0) :
    hermStd (semiVec A φ w) (semiVec A φ w) = 0 := by
  rw [hermStd_semiVec, hw, map_zero]

theorem glAut_mem_GU0 (φ : F4 ≃+* F4) {g : GL (Fin 6) F4} (hg : g ∈ GU0) : glAut φ g ∈ GU0 := by
  intro x y
  rw [coe_glAut]
  rw [← fvec_fvec_symm φ x, ← fvec_fvec_symm φ y, map_mulVec_fvec, map_mulVec_fvec,
    herm_eq_std, herm_eq_std, hermStd_fvec, hermStd_fvec, ← herm_eq_std, ← herm_eq_std, hg]

@[expose] def semiConj (A : GU0) (φ : F4 ≃+* F4) (g : GU0) : GU0 :=
  A * ⟨glAut φ g, glAut_mem_GU0 φ g.2⟩ * A⁻¹

theorem coe_semiConj (A : GU0) (φ : F4 ≃+* F4) (g : GU0) :
    ((semiConj A φ g : GU0) : GL (Fin 6) F4) =
      (A : GL (Fin 6) F4) * glAut φ (g : GL (Fin 6) F4) * (A : GL (Fin 6) F4)⁻¹ := rfl

theorem semiConj_mulVec_semiVec (A : GU0) (φ : F4 ≃+* F4) (g : GU0) (x : W) :
    ((semiConj A φ g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ semiVec A φ x =
      semiVec A φ (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x) := by
  rw [coe_semiConj, Units.val_mul, Units.val_mul, semiVec, ← mulVec_mulVec, ← mulVec_mulVec,
    inv_mulVec_mulVec', coe_glAut, map_mulVec_fvec]
  rfl

section Perm


theorem fvec_uVec_ne_zero (φ : F4 ≃+* F4) (p : Fin 693) : fvec φ (uVec p) ≠ 0 :=
  fvec_ne_zero φ (uVec_ne_zero ptsFacts p.2)

theorem fvec_uVec_iso (φ : F4 ≃+* F4) (p : Fin 693) :
    hermStd (fvec φ (uVec p)) (fvec φ (uVec p)) = 0 := by
  rw [hermStd_fvec, uVec_iso ptsFacts p.2, map_zero]

@[expose] def ptOf (w : W) (hw : w ≠ 0) (hiso : hermStd w w = 0) : Fin 693 :=
  ⟨ptIdx w, ptIdx_lt ptsFacts hw hiso⟩

theorem ptOf_val (w : W) (hw : w ≠ 0) (hiso : hermStd w w = 0) :
    (ptOf w hw hiso).val = ptIdx w := rfl

theorem ptOf_smul {c : F4} (hc : c ≠ 0) (w : W) (hw : w ≠ 0) (hiso : hermStd w w = 0)
    (hw' : c • w ≠ 0) (hiso' : hermStd (c • w) (c • w) = 0) :
    ptOf (c • w) hw' hiso' = ptOf w hw hiso :=
  Fin.ext (ptIdx_smul hc w)

theorem ptOf_uVec (p : Fin 693) :
    ptOf (uVec p) (uVec_ne_zero ptsFacts p.2) (uVec_iso ptsFacts p.2) = p :=
  Fin.ext (ptIdx_uVec ptsFacts p.2)

theorem uVec_ptOf (w : W) (hw : w ≠ 0) (hiso : hermStd w w = 0) :
    ∃ c : F4, c ≠ 0 ∧ uVec (ptOf w hw hiso) = c • w := by
  rw [ptOf_val, uVec_ptIdx ptsFacts hw hiso]
  exact normV_eq_smul hw

theorem ptOf_eq_ptOf_iff {v w : W} (hv : v ≠ 0) (hviso : hermStd v v = 0) (hw : w ≠ 0)
    (hwiso : hermStd w w = 0) :
    ptOf v hv hviso = ptOf w hw hwiso ↔ ∃ c : F4, c ≠ 0 ∧ w = c • v := by
  constructor
  · intro h
    obtain ⟨a, ha, hav⟩ := uVec_ptOf v hv hviso
    obtain ⟨b, hb, hbw⟩ := uVec_ptOf w hw hwiso
    rw [h, hbw] at hav
    refine ⟨b⁻¹ * a, mul_ne_zero (inv_ne_zero hb) ha, ?_⟩
    rw [mul_smul, ← hav, smul_smul, inv_mul_cancel₀ hb, one_smul]
  · rintro ⟨c, hc, rfl⟩
    exact (ptOf_smul hc v hv hviso hw hwiso).symm

@[expose] def fieldPerm (φ : F4 ≃+* F4) : Equiv.Perm (Fin 693) where
  toFun p := ptOf (fvec φ (uVec p)) (fvec_uVec_ne_zero φ p) (fvec_uVec_iso φ p)
  invFun p := ptOf (fvec φ.symm (uVec p)) (fvec_uVec_ne_zero φ.symm p) (fvec_uVec_iso φ.symm p)
  left_inv p := by
    obtain ⟨c, hc, hcv⟩ := uVec_ptOf _ (fvec_uVec_ne_zero φ p) (fvec_uVec_iso φ p)
    apply Fin.ext
    rw [ptOf_val, hcv, fvec_smul, fvec_symm_fvec, ptIdx_smul ((map_ne_zero _).2 hc),
      ptIdx_uVec ptsFacts p.2]
  right_inv p := by
    obtain ⟨c, hc, hcv⟩ := uVec_ptOf _ (fvec_uVec_ne_zero φ.symm p) (fvec_uVec_iso φ.symm p)
    apply Fin.ext
    rw [ptOf_val, hcv, fvec_smul, fvec_fvec_symm, ptIdx_smul ((map_ne_zero _).2 hc),
      ptIdx_uVec ptsFacts p.2]

@[expose] noncomputable def semiPerm (A : GU0) (φ : F4 ≃+* F4) : Equiv.Perm (Fin 693) :=
  piGU A * fieldPerm φ

theorem semiPerm_ptOf (A : GU0) (φ : F4 ≃+* F4) (w : W) (hw : w ≠ 0) (hiso : hermStd w w = 0) :
    semiPerm A φ (ptOf w hw hiso) =
      ptOf (semiVec A φ w) (semiVec_ne_zero A φ hw) (semiVec_iso A φ hiso) := by
  apply Fin.ext
  obtain ⟨c, hc, hcw⟩ := uVec_ptOf w hw hiso
  have hf := fvec_uVec_ne_zero φ (ptOf w hw hiso)
  have hfi := fvec_uVec_iso φ (ptOf w hw hiso)
  obtain ⟨d, hd, hdv⟩ := uVec_ptOf _ hf hfi
  change (A • fieldPerm φ (ptOf w hw hiso)).val = _
  rw [smul_val]
  change ptIdx (_ *ᵥ uVec (ptOf (fvec φ (uVec (ptOf w hw hiso))) hf hfi)) = _
  rw [hdv, hcw, fvec_smul, smul_smul, mulVec_smul,
    ptIdx_smul (mul_ne_zero hd ((map_ne_zero _).2 hc)), ptOf_val]
  rfl

theorem semiPerm_uVec (A : GU0) (φ : F4 ≃+* F4) (p : Fin 693) :
    semiPerm A φ p = ptOf (semiVec A φ (uVec p)) (semiVec_ne_zero A φ (uVec_ne_zero ptsFacts p.2))
      (semiVec_iso A φ (uVec_iso ptsFacts p.2)) := by
  have h := semiPerm_ptOf A φ (uVec p) (uVec_ne_zero ptsFacts p.2) (uVec_iso ptsFacts p.2)
  rwa [ptOf_uVec] at h

theorem semiPerm_val (A : GU0) (φ : F4 ≃+* F4) (p : Fin 693) :
    (semiPerm A φ p).val = ptIdx (semiVec A φ (uVec p)) := by
  rw [semiPerm_uVec, ptOf_val]

theorem uVec_semiPerm (A : GU0) (φ : F4 ≃+* F4) (p : Fin 693) :
    ∃ c : F4, c ≠ 0 ∧ uVec (semiPerm A φ p) = c • semiVec A φ (uVec p) := by
  rw [semiPerm_uVec]
  exact uVec_ptOf _ _ _

theorem semiPerm_orth (A : GU0) (φ : F4 ≃+* F4) (p q : Fin 693) :
    hermStd (uVec (semiPerm A φ p)) (uVec (semiPerm A φ q)) = 0 ↔
      hermStd (uVec p) (uVec q) = 0 := by
  obtain ⟨c, hc, hcp⟩ := uVec_semiPerm A φ p
  obtain ⟨d, hd, hdq⟩ := uVec_semiPerm A φ q
  rw [hcp, hdq, hermStd_smul_left, hermStd_smul_right, hermStd_semiVec]
  constructor
  · intro h
    have h1 : φ (hermStd (uVec p) (uVec q)) = 0 := by
      rcases mul_eq_zero.1 h with h2 | h2
      · exact absurd h2 hc
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 (pow_ne_zero 2 hd)
      · exact h3
    exact (map_eq_zero_iff φ φ.injective).1 h1
  · intro h
    rw [h, map_zero, mul_zero, mul_zero]

theorem conj_semiPerm (A : GU0) (φ : F4 ≃+* F4) (g : GU0) :
    semiPerm A φ * piGU g * (semiPerm A φ)⁻¹ = piGU (semiConj A φ g) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext p
  have hg0 := mulVec_ne_zero (g : GL (Fin 6) F4) (uVec_ne_zero ptsFacts p.2)
  have hgi : hermStd (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p) = 0 := by
    rw [hermStd_mulVec]; exact uVec_iso ptsFacts p.2
  have h1 : piGU g p = ptOf _ hg0 hgi := Fin.ext (smul_val g p)
  rw [Equiv.Perm.mul_apply, h1, semiPerm_ptOf, ptOf_val, Equiv.Perm.mul_apply]
  change _ = ((semiConj A φ g) • (semiPerm A φ p)).val
  rw [smul_val]
  obtain ⟨c, hc, hcv⟩ := uVec_semiPerm A φ p
  rw [hcv, mulVec_smul, semiConj_mulVec_semiVec, ptIdx_smul hc]

theorem semiPerm_tvP (A : GU0) (φ : F4 ≃+* F4) (p : Fin 693) :
    semiPerm A φ * tvP p * (semiPerm A φ)⁻¹ = tvP (semiPerm A φ p) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext q
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hval : ∀ (r s : Fin 693), (tvP r s).val =
      ptIdx (uVec s + hermStd (uVec s) (uVec r) • uVec r) := by
    intro r s
    rw [tvP, piSU_apply]
    change ptIdx (tvM (uVec r) *ᵥ uVec s) = _
    rw [tvM_mulVec]
  have hpi := uVec_iso ptsFacts p.2
  have hw0 : tvM (uVec p) *ᵥ uVec q ≠ 0 := by
    have := mulVec_ne_zero (tvGL (uVec p) hpi) (uVec_ne_zero ptsFacts q.2)
    rwa [tvGL_val] at this
  have hwi : hermStd (tvM (uVec p) *ᵥ uVec q) (tvM (uVec p) *ᵥ uVec q) = 0 := by
    have := isIsom_tvM hpi (uVec q) (uVec q)
    rw [herm_eq_std, herm_eq_std] at this
    rw [this]
    exact uVec_iso ptsFacts q.2
  have htv : tvP p q = ptOf _ hw0 hwi := by
    apply Fin.ext
    rw [tvP, piSU_apply, ptOf_val]
    rfl
  rw [htv, semiPerm_ptOf, ptOf_val, hval, tvM_mulVec]
  obtain ⟨c, hc, hcp⟩ := uVec_semiPerm A φ q
  obtain ⟨d, hd, hdp⟩ := uVec_semiPerm A φ p
  rw [hcp, hdp, semiVec_add, semiVec_smul, hermStd_smul_left, hermStd_smul_right,
    hermStd_semiVec, smul_smul]
  have e : c * (d ^ 2 * φ (hermStd (uVec q) (uVec p))) * d =
      c * (φ (hermStd (uVec q) (uVec p))) := by
    calc c * (d ^ 2 * φ (hermStd (uVec q) (uVec p))) * d
        = c * ((d * d * d) * φ (hermStd (uVec q) (uVec p))) := by ring
      _ = c * (φ (hermStd (uVec q) (uVec p))) := by rw [cube_eq_one d hd, one_mul]
  rw [e, ← smul_smul, ← smul_add, ptIdx_smul hc]

end Perm

end CFSG.LargeExtraspecial.SMod20.Aut
