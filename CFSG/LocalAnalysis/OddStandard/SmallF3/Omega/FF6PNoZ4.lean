module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PNoZ4Aux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6p_z4_sq_cases (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q} (hz4 : z ^ 4 = 1) (hz2 : z ^ 2 ≠ 1)
    (hnorm : ∀ p ∈ ffP1p hQ fr,
      ffOmegaToSim hQ p * z * (ffOmegaToSim hQ p)⁻¹ ∈ Subgroup.zpowers z) :
    z ^ 2 = ffOmegaToSim hQ (ffZ0s hQ fr) ∨ z ^ 2 = ffTs fr ∨
      z ^ 2 = ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hz : ∀ p ∈ ffP1p hQ fr, z ^ 2 * ffOmegaToSim hQ p = ffOmegaToSim hQ p * z ^ 2 := by
    intro p hp
    have h := ffOutFF6PNoZ4_sq_conj hz2 hz4 (hnorm p hp)
    calc z ^ 2 * ffOmegaToSim hQ p
        = (ffOmegaToSim hQ p * z ^ 2 * (ffOmegaToSim hQ p)⁻¹) *
            ffOmegaToSim hQ p := by rw [h]
      _ = ffOmegaToSim hQ p * z ^ 2 := by group
  rcases ff6p_cent_P1 hQ h2 hπ fr hz with h1 | h2' | h3 | h4
  · exact (hz2 h1).elim
  · exact Or.inl h2'
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

theorem ff6p_z4_flip (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hz4 : z ^ 4 = 1) (hz2 : z ^ 2 ≠ 1)
    (hnorm : ∀ p ∈ ffP1p hQ fr,
      ffOmegaToSim hQ p * z * (ffOmegaToSim hQ p)⁻¹ ∈ Subgroup.zpowers z) :
    (∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) ∨
      ∀ (J : Finset (Fin 5)) (b : ↥(omegaProj hQ)), Even J.card →
        (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
        ((4 : Fin 5) ∉ J → z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) ∧
          ((4 : Fin 5) ∈ J → ffOmegaToSim hQ b * z * (ffOmegaToSim hQ b)⁻¹ = z * z ^ 2) := by
  classical
  have hdich : ∀ p ∈ ffP1p hQ fr,
      MulAut.conj (ffOmegaToSim hQ p) z = z ∨
        MulAut.conj (ffOmegaToSim hQ p) z = z * z ^ 2 := by
    intro p hp
    rw [MulAut.conj_apply]
    exact ffOutFF6PNoZ4_conj_cases hz4 hz2 (hnorm p hp)
  have hbex : ∀ (J : Finset (Fin 5)) (hJ : Even J.card),
      ∃ b : ↥(omegaProj hQ), b ∈ ffB1p hQ fr ∧
        (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) := by
    intro J hJ
    refine ⟨omegaToProj hQ ⟨fr.signChange (ffOpt J), ?_⟩, ?_, rfl⟩
    · exact ffB0p_le_omega hQ fr ((mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJ, rfl⟩)
    · exact (mem_ffB1p_iff hQ fr).mpr ⟨J, hJ, rfl⟩
  obtain ⟨b04, hb04mem, hb04c⟩ := hbex {0, 4} (by decide)
  have hzv : z * z ^ 2 ≠ z := fun h => hz2 (mul_left_cancel (by rw [h, mul_one]))
  let f : Finset (Fin 5) → Prop := fun J => ∀ b : ↥(omegaProj hQ),
    (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
    MulAut.conj (ffOmegaToSim hQ b) z = z * z ^ 2
  have hfE : ∀ (J : Finset (Fin 5)) (b : ↥(omegaProj hQ)),
      (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      (f J ↔ MulAut.conj (ffOmegaToSim hQ b) z = z * z ^ 2) := by
    intro J b hb
    constructor
    · intro hf; exact hf b hb
    · intro hFJ b' hb'
      have hbb : b' = b := Subtype.ext (by rw [hb', hb])
      rw [hbb]; exact hFJ
  have hprod : ∀ (J K : Finset (Fin 5)) (bJ bK bJK : ↥(omegaProj hQ)),
      (bJ : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      (bK : ProjOrth Q) = toProj Q (fr.signChange (ffOpt K)) →
      (bJK : ProjOrth Q) = toProj Q (fr.signChange (ffOpt (symmDiff J K))) →
      bJK = bJ * bK := by
    intro J K bJ bK bJK hJ hK hJK
    apply Subtype.ext
    rw [hJK, Subgroup.coe_mul, hJ, hK, ← map_mul, fr.signChange_mul, ffOpt_symmDiff]
  have hrel : ∀ (bJ bK : ↥(omegaProj hQ)), bJ ∈ ffB1p hQ fr → bK ∈ ffB1p hQ fr →
      (MulAut.conj (ffOmegaToSim hQ (bJ * bK)) z = z ↔
        (MulAut.conj (ffOmegaToSim hQ bJ) z = z ↔
          MulAut.conj (ffOmegaToSim hQ bK) z = z)) := by
    intro bJ bK hbJ hbK
    rw [map_mul]
    exact ffOutFF6PNoZ4_parity_mul hz2 hz4
      (hdich bJ (ffB1p_le_ffP1p hQ fr hbJ)) (hdich bK (ffB1p_le_ffP1p hQ fr hbK))
  have hE : ∀ (bJ bK : ↥(omegaProj hQ)), bJ ∈ ffB1p hQ fr → bK ∈ ffB1p hQ fr →
      (MulAut.conj (ffOmegaToSim hQ (bJ * bK)) z = z * z ^ 2 ↔
        ¬ (MulAut.conj (ffOmegaToSim hQ bJ) z = z * z ^ 2 ↔
          MulAut.conj (ffOmegaToSim hQ bK) z = z * z ^ 2)) := by
    intro bJ bK hbJ hbK
    have hN := hrel bJ bK hbJ hbK
    have d1 := hdich (bJ * bK) (ffB1p_le_ffP1p hQ fr (mul_mem hbJ hbK))
    have d2 := hdich bJ (ffB1p_le_ffP1p hQ fr hbJ)
    have d3 := hdich bK (ffB1p_le_ffP1p hQ fr hbK)
    rw [ffOutFF6PNoZ4_flip_iff_not hz2 d1, ffOutFF6PNoZ4_flip_iff_not hz2 d2,
      ffOutFF6PNoZ4_flip_iff_not hz2 d3, hN]
    exact not_congr not_iff_not.symm
  have h0 : ¬ f ∅ := by
    intro hf
    have h1 : ((1 : ↥(omegaProj hQ)) : ProjOrth Q) =
        toProj Q (fr.signChange (ffOpt (∅ : Finset (Fin 5)))) := by
      simp [ffOpt, fr.signChange_empty]
    have hE1 : MulAut.conj (ffOmegaToSim hQ (1 : ↥(omegaProj hQ))) z = z * z ^ 2 := hf 1 h1
    have hne1 : ¬ (MulAut.conj (ffOmegaToSim hQ (1 : ↥(omegaProj hQ))) z = z * z ^ 2) := by
      rw [map_one, map_one, MulAut.one_apply]
      exact fun h => hzv h.symm
    exact hne1 hE1
  have hF2 : ∀ (i : Fin 5), i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      ∀ (bi b0 : ↥(omegaProj hQ)), bi ∈ ffB1p hQ fr → b0 ∈ ffB1p hQ fr →
      (bi : ProjOrth Q) = toProj Q (fr.signChange (ffOpt {i, 4})) →
      (b0 : ProjOrth Q) = toProj Q (fr.signChange (ffOpt {0, 4})) →
      (MulAut.conj (ffOmegaToSim hQ bi) z = z * z ^ 2 ↔
        MulAut.conj (ffOmegaToSim hQ b0) z = z * z ^ 2) := by
    intro i hi bi b0 hbim hb0m hbic hb0c
    set σ : Equiv.Perm (Fin 5) := ffRot ^ i.val with hσdef
    have hσmem : σ ∈ ffD8p := by
      rw [hσdef]; exact pow_mem ffRot_mem_ffD8p i.val
    set hh : ↥(omegaProj hQ) :=
      omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ with hhhdef
    have hhmem : hh ∈ ffP1p hQ fr := by
      rw [mem_ffP1p_iff hQ fr]
      refine ⟨σ, hσmem, ∅, ⟨0, rfl⟩, ?_⟩
      rw [hhhdef]
      simp only [ffOpt, Finset.map_empty, fr.signChange_empty, mul_one]
      exact coe_omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩
    have hhh : (hh : ProjOrth Q) = toProj Q (ffHat fr σ) := by
      rw [hhhdef]; exact coe_omegaToProj hQ _
    have hconj : hh * b0 * hh⁻¹ = bi := by
      apply Subtype.ext
      have hσ4 : ffAct σ {0, 4} = {i, 4} := by
        rw [hσdef]; exact ffOutFF6PNoZ4_rot_act i hi
      calc ((hh * b0 * hh⁻¹ : ↥(omegaProj hQ)) : ProjOrth Q)
          = (hh : ProjOrth Q) * (b0 : ProjOrth Q) * (hh : ProjOrth Q)⁻¹ := by simp
        _ = toProj Q (ffHat fr σ) * toProj Q (fr.signChange (ffOpt {0, 4})) *
              (toProj Q (ffHat fr σ))⁻¹ := by rw [hhh, hb0c]
        _ = toProj Q (ffHat fr σ * fr.signChange (ffOpt {0, 4}) * (ffHat fr σ)⁻¹) := by
              simp only [← map_mul, ← map_inv]
        _ = toProj Q (fr.signChange (ffOpt (ffAct σ {0, 4}))) := by
              rw [ffHat_conj_signChange_ffOpt]
        _ = toProj Q (fr.signChange (ffOpt {i, 4})) := by rw [hσ4]
        _ = (bi : ProjOrth Q) := hbic.symm
    have hN : MulAut.conj (ffOmegaToSim hQ bi) z = z ↔
        MulAut.conj (ffOmegaToSim hQ b0) z = z := by
      have hpc := ffOutFF6PNoZ4_parity_conj (ffOmegaToSim hQ) (ffP1p hQ fr) hz2 hz4 hdich
        hhmem (ffB1p_le_ffP1p hQ fr hb0m)
      have hhι : ffOmegaToSim hQ (hh * b0 * hh⁻¹) = ffOmegaToSim hQ bi := by rw [hconj]
      rwa [hhι] at hpc
    exact (ffOutFF6PNoZ4_flip_iff_not hz2 (hdich bi (ffB1p_le_ffP1p hQ fr hbim))).trans
      ((not_congr hN).trans
        (ffOutFF6PNoZ4_flip_iff_not hz2 (hdich b0 (ffB1p_le_ffP1p hQ fr hb0m))).symm)
  have hbasis : ∀ i : Fin 5, i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      (f {i, 4} ↔ MulAut.conj (ffOmegaToSim hQ b04) z = z * z ^ 2) := by
    intro i hi
    obtain ⟨bi, hbimem, hbic⟩ :=
      hbex {i, 4} (ffOutFF6PNoZ4_even_pair i (ffOutFF6PNoZ4_ne_four i hi))
    rw [hfE {i, 4} bi hbic]
    exact hF2 i hi bi b04 hbimem hb04mem hbic hb04c
  have hstep : ∀ (J : Finset (Fin 5)) (i : Fin 5), Even J.card → i ∈ J → i ≠ 4 →
      (f (symmDiff J {i, 4}) ↔ ¬ (f J ↔ f {i, 4})) := by
    intro J i hJ hJi hi4
    obtain ⟨bJ, hbJmem, hbJc⟩ := hbex J hJ
    obtain ⟨bi, hbimem, hbic⟩ := hbex {i, 4} (ffOutFF6PNoZ4_even_pair i hi4)
    have heven : Even (symmDiff J {i, 4}).card :=
      (ffOutFF6PNoZ4_even_symmDiff J i hJ hJi hi4).1
    obtain ⟨bJK, hbJKmem, hbJKc⟩ := hbex (symmDiff J {i, 4}) heven
    rw [hfE _ bJK hbJKc, hfE _ bJ hbJc, hfE _ bi hbic]
    have hpe : bJK = bJ * bi := hprod J {i, 4} bJ bi bJK hbJc hbic hbJKc
    rw [hpe]
    exact hE bJ bi hbJmem hbimem
  have hmaster := ffOutFF6PNoZ4_master f h0 hbasis hstep
  by_cases hβ : MulAut.conj (ffOmegaToSim hQ b04) z = z * z ^ 2
  · right
    intro J b hJe hbJ
    have hbmem : b ∈ ffB1p hQ fr := (mem_ffB1p_iff hQ fr).mpr ⟨J, hJe, hbJ⟩
    have hEJ : MulAut.conj (ffOmegaToSim hQ b) z = z * z ^ 2 ↔ (4 : Fin 5) ∈ J := by
      rw [← hfE J b hbJ]
      exact (hmaster J hJe).trans ⟨fun h => h.1, fun h => ⟨h, hβ⟩⟩
    constructor
    · intro h4not
      have hEb : ¬ MulAut.conj (ffOmegaToSim hQ b) z = z * z ^ 2 := by
        rw [hEJ]; exact h4not
      have hNb : MulAut.conj (ffOmegaToSim hQ b) z = z := by
        by_contra hN
        exact hEb ((ffOutFF6PNoZ4_flip_iff_not hz2
          (hdich b (ffB1p_le_ffP1p hQ fr hbmem))).mpr hN)
      exact ffOutFF6PNoZ4_comm_of_conj hNb
    · intro h4in
      have hEb : MulAut.conj (ffOmegaToSim hQ b) z = z * z ^ 2 := hEJ.mpr h4in
      rw [MulAut.conj_apply] at hEb
      exact hEb
  · left
    intro b hb
    obtain ⟨J, hJe, hbJ⟩ := (mem_ffB1p_iff hQ fr).mp hb
    have hnfJ : ¬ f J := by
      rw [hmaster J hJe]
      exact fun h => hβ h.2
    have hEb : ¬ MulAut.conj (ffOmegaToSim hQ b) z = z * z ^ 2 :=
      (not_congr (hfE J b hbJ)).mp hnfJ
    have hNb : MulAut.conj (ffOmegaToSim hQ b) z = z := by
      by_contra hN
      exact hEb ((ffOutFF6PNoZ4_flip_iff_not hz2
        (hdich b (ffB1p_le_ffP1p hQ fr hb))).mpr hN)
    exact ffOutFF6PNoZ4_comm_of_conj hNb

end CFSG.OddStandard.SmallF3.Omega
