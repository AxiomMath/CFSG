module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Y9
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Frame

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] noncomputable def deltaGU : GU →* GF64ˣ :=
  (powMonoidHom 3).comp (Matrix.GeneralLinearGroup.det.comp GU.subtype)

theorem coe_deltaGU (h : GU) :
    ((deltaGU h : GF64ˣ) : GF64) =
      ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det ^ 3 := by
  simp [deltaGU]

theorem deltaGU_cube (h : GU) : deltaGU h ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_deltaGU, ← pow_mul, Units.val_one]
  exact det_pow_nine_of_mem_GU h.2

theorem deltaGU_eq_one_of_suConj_eq_one {h : GU} (hh : suConj hU h = 1) : deltaGU h = 1 := by
  obtain ⟨c, hc⟩ := (suConj_eq_one_iff h).1 hh
  have hGU : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ GU := by
    rw [hc]
    exact h.2
  have h9 := pow_nine_of_scalar_mem_GU hGU
  apply Units.ext
  rw [coe_deltaGU, ← hc, det_scalar_three, ← pow_mul, Units.val_one]
  exact h9

theorem scalar_mem_GU {c : GF64ˣ} (hc : (c : GF64) ^ 9 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ GU := by
  have h : (c : GF64) * hU.bar c = 1 := by
    rw [bar_apply_eq, barC_eq_pow]
    calc (c : GF64) * (c : GF64) ^ 8 = (c : GF64) ^ 9 := by ring
      _ = 1 := hc
  change (((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) GF64) :
    Matrix (Fin 3) (Fin 3) GF64).map hU.bar)ᵀ *
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) GF64) :
        Matrix (Fin 3) (Fin 3) GF64) = 1
  rw [coe_scalar_eq_smul]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.mul_apply] <;>
    exact (mul_comm _ _).trans h

theorem exists_cube_root {d : GF64} (hd : d ^ 3 = 1) : ∃ c : GF64, c ^ 3 = d := by
  obtain ⟨k, -, hk⟩ := det_cases d hd
  exact ⟨zeta ^ k, by rw [hk, ← pow_mul, mul_comm]⟩

theorem exists_conj_of_delta_eq_one (h : GU) (hδ : deltaGU h = 1) :
    ∃ g : SU, suConj hU h = MulAut.conj g := by
  have hd : ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det ^ 3 = 1 := by
    have := congrArg (fun u : GF64ˣ => (u : GF64)) hδ
    simpa [coe_deltaGU] using this
  obtain ⟨c, hc⟩ := exists_cube_root hd
  have hd0 : ((h : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det ≠ 0 :=
    ((h : GL (Fin 3) GF64).isUnit.map
      (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) GF64 →* GF64)).ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hd0
    rw [← hc]
    norm_num
  have hc9 : c ^ 9 = 1 := by
    calc c ^ 9 = (c ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hc, hd]
  set cu : GF64ˣ := Units.mk0 c hc0 with hcu
  have hscGU : Matrix.GeneralLinearGroup.scalar (Fin 3) cu ∈ GU := scalar_mem_GU hc9
  set sc : GU := ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) cu, hscGU⟩ with hsc
  set A : GU := h * sc⁻¹ with hA
  have hAcoe : (A : GL (Fin 3) GF64) = (h : GL (Fin 3) GF64) *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) cu)⁻¹ := rfl
  have hdetA : ((A : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64).det = 1 := by
    rw [hAcoe, Units.val_mul, Matrix.det_mul, ← map_inv, det_scalar_three]
    have hcu3 : ((cu⁻¹ : GF64ˣ) : GF64) ^ 3 = (((h : GL (Fin 3) GF64) :
        Matrix (Fin 3) (Fin 3) GF64).det)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, inv_pow, hcu, Units.val_mk0, hc]
    rw [hcu3]
    exact mul_inv_cancel₀ hd0
  have hAsu : (A : GL (Fin 3) GF64) ∈ SU := (mem_unitarySU_iff hU).2 ⟨hdetA, A.2⟩
  refine ⟨⟨A, hAsu⟩, ?_⟩
  have hsc1 : suConj hU sc = 1 := (suConj_eq_one_iff sc).2 ⟨cu, rfl⟩
  have hhA : h = A * sc := by rw [hA]; group
  rw [mulAut_conj_eq_suConj', hhA, map_mul, hsc1, mul_one]

theorem ker_rangeRestrict_le_ker_delta :
    (suConj hU).rangeRestrict.ker ≤ (deltaGU).ker := by
  rw [MonoidHom.ker_rangeRestrict]
  intro h hh
  exact deltaGU_eq_one_of_suConj_eq_one (MonoidHom.mem_ker.1 hh)

@[expose] noncomputable def deltaRange : (suConj hU).range →* GF64ˣ :=
  (suConj hU).rangeRestrict.liftOfSurjective (suConj hU).rangeRestrict_surjective
    ⟨deltaGU, ker_rangeRestrict_le_ker_delta⟩

theorem deltaRange_suConj (h : GU) :
    deltaRange ⟨suConj hU h, ⟨h, rfl⟩⟩ = deltaGU h :=
  MonoidHom.liftOfRightInverse_comp_apply (suConj hU).rangeRestrict _
    (Function.rightInverse_surjInv (suConj hU).rangeRestrict_surjective)
    ⟨deltaGU, ker_rangeRestrict_le_ker_delta⟩ h

@[expose] noncomputable def deltaOn {X : Type*} [Group X] (act : X →* MulAut SU) (E : Subgroup X)
    (hin : ∀ x ∈ E, act x ∈ (suConj hU).range) : E →* GF64ˣ :=
  deltaRange.comp ((act.comp E.subtype).codRestrict (suConj hU).range fun x => hin x x.2)

theorem deltaOn_eq {X : Type*} [Group X] {act : X →* MulAut SU} {E : Subgroup X}
    {hin : ∀ x ∈ E, act x ∈ (suConj hU).range} (x : E) (h : GU) (hx : act x = suConj hU h) :
    deltaOn act E hin x = deltaGU h := by
  rw [← deltaRange_suConj h]
  exact congrArg deltaRange (Subtype.ext hx)

end CFSG.AGLEmbedding.ChevOuter.U38
