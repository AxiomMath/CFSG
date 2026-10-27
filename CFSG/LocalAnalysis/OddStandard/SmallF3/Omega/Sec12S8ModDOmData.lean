module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDOmDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix Certificates.S8DFin CFSG.HardMathSupport.RichardWeiss.Proving

theorem s8dPom_bas : ∀ k : Fin 8, s8dPom (s8dBas k) = s8dQ k := by
  intro k
  rw [s8dPom_apply]
  revert k
  decide +kernel

theorem s8d_om_ext {f : S8A} {A B : Sec12SL}
    (h : ∀ k : Fin 8, s8dPom (s8dAp f (s8dBas k)) = (A : Sec12M) * s8dQ k * (B : Sec12M)ᵀ) :
    f = s8dOm (A, B) :=
  s8d_ext8 fun k => s8dPom.injective (by rw [h k, s8dAp_om, s8dPom_bas])

theorem s8dOm_injective : Function.Injective s8dOm := by
  refine (injective_iff_map_eq_one s8dOm).mpr fun AB hAB => ?_
  obtain ⟨A, B⟩ := AB
  by_contra hne
  have hne' : A ≠ 1 ∨ B ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (Prod.ext h.1 h.2)
  have hfix : ∀ M : Sec12M, (A : Sec12M) * M * (B : Sec12M)ᵀ = M := by
    intro M
    obtain ⟨p, rfl⟩ := s8dPom.surjective M
    rw [← s8dAp_om, hAB, s8dAp_one]
  have hle := sec12F4_fix_le A B hne'
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hfix), s8d_card_mat] at hle
  omega

theorem s8dAU_det : (!![0, 1; 1, 1] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  decide

theorem s8dAV_det : (!![Sec12F4.w, 0; 0, Sec12F4.w2] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  decide

theorem s8dAVF_det : (!![Sec12F4.w2, 0; 0, Sec12F4.w] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  decide

@[expose] def s8dAU : Sec12SL := ⟨!![0, 1; 1, 1], s8dAU_det⟩

@[expose] def s8dAV : Sec12SL := ⟨!![Sec12F4.w, 0; 0, Sec12F4.w2], s8dAV_det⟩

@[expose] def s8dAVF : Sec12SL := ⟨!![Sec12F4.w2, 0; 0, Sec12F4.w], s8dAVF_det⟩

theorem s8dDiag_U : s8dDiag altFiveUPerm = s8dOm (s8dAU, s8dAU) := by
  refine s8d_om_ext fun k => ?_
  rw [s8dPom_apply]
  revert k
  decide +kernel

theorem s8dDiag_V : s8dDiag altFiveVPerm = s8dOm (s8dAV, s8dAVF) := by
  refine s8d_om_ext fun k => ?_
  rw [s8dPom_apply]
  revert k
  decide +kernel

theorem s8dDiag_mem_range (a : ↥(alternatingGroup (Fin 5))) :
    s8dDiag (a : Equiv.Perm (Fin 5)) ∈ s8dOm.range := by
  let D : ↥(alternatingGroup (Fin 5)) →* S8A := s8dDiag.comp (alternatingGroup (Fin 5)).subtype
  have hcl : Subgroup.closure ({altFiveU, altFiveV} : Set ↥(alternatingGroup (Fin 5))) ≤
      s8dOm.range.comap D := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_comap.mpr (MonoidHom.mem_range.mpr ⟨_, s8dDiag_U.symm⟩)
    · exact Subgroup.mem_comap.mpr (MonoidHom.mem_range.mpr ⟨_, s8dDiag_V.symm⟩)
  rw [altFive_closure_pair_eq_top] at hcl
  exact hcl (Subgroup.mem_top a)

private theorem s8d_om1_codes : ∀ k : Fin 8,
    s8dPomH (s8dDec ((mk 183 203).ap (2 ^ (k : ℕ)))) = (s8dAg : Sec12M) * s8dQ k := by
  decide +kernel

private theorem s8d_om2_codes : ∀ k : Fin 8,
    s8dPomH (s8dDec ((mk 188 123).ap (2 ^ (k : ℕ)))) = s8dQ k * (s8dAgF : Sec12M)ᵀ := by
  decide +kernel

theorem s8d_om1_of {f : S8A} (hf : ∀ n, s8dAp f (s8dDec n) = s8dDec ((mk 183 203).ap n)) :
    f = s8dOm1 := by
  show f = s8dOm (s8dAg, 1)
  refine s8d_om_ext fun k => ?_
  have h := hf (2 ^ (k : ℕ))
  rw [s8dDec_bas k] at h
  rw [h, s8dPom_apply, s8d_om1_codes k, s8d_sl_coe_one, Matrix.transpose_one, Matrix.mul_one]

theorem s8d_om2_of {f : S8A} (hf : ∀ n, s8dAp f (s8dDec n) = s8dDec ((mk 188 123).ap n)) :
    f = s8dOm2 := by
  show f = s8dOm (1, s8dAgF)
  refine s8d_om_ext fun k => ?_
  have h := hf (2 ^ (k : ℕ))
  rw [s8dDec_bas k] at h
  rw [h, s8dPom_apply, s8d_om2_codes k, s8d_sl_coe_one, Matrix.one_mul]

end CFSG.OddStandard.SmallF3.Omega
