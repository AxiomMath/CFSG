module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4IU
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Max

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

theorem coreIU_alphaI {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {a : F} (ha : a ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup (StatedProj (StatedSp 2 F))}
    (h : PConfig (alphaI ha) p X) : False := by
  by_cases hpc : ringChar F = p
  · exact aI_defining hodd ha hpc h
  · exact aI_cross hodd ha hp2 hpc h

theorem congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) : MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem coreI_all {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) (A : gsp 2 F) (d : Fˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1)
    (hdm : (d : F) = -(multiplierUnit A : F)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (conjAut 2 F A) p X) : False := by
  have h2 := Ring.two_ne_zero hodd
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (-(d : F)) • formJ 2 F := by
    rw [multiplierUnit_spec, hdm, neg_neg]
  obtain ⟨g, hg⟩ := exists_frame_typeI h2 hd0 hA hAA
  set g' : gsp 2 F := ⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩ with hg'
  have hAg : A * g' = g' * aIgsp hd0 := by
    apply Subtype.ext
    apply Units.ext
    exact hg
  have hAeq : A = g' * aIgsp hd0 * g'⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hAg
  have hconj : conjAut 2 F A = MulAut.conj (proj 2 F g) * alphaI hd0 * (MulAut.conj (proj 2 F g))⁻¹ := by
    rw [hAeq, map_mul, map_mul, map_inv, alphaI]
    have : conjAut 2 F g' = MulAut.conj (proj 2 F g) := conjAut_statedSp g
    rw [this]
  have h' := PConfig.of_mulEquiv (MulAut.conj (proj 2 F g)⁻¹ : StatedProj (StatedSp 2 F) ≃*
    StatedProj (StatedSp 2 F)) h
  have key : MulAut.congr (MulAut.conj (proj 2 F g)⁻¹ : StatedProj (StatedSp 2 F) ≃*
      StatedProj (StatedSp 2 F)) (conjAut 2 F A) = alphaI hd0 := by
    rw [congr_eq_mul, hconj, map_inv]
    group
  rw [key] at h'
  exact coreIU_alphaI hodd hd0 hp2 h'

theorem coreI_thm : CoreI := by
  intro F _ _ hodd A d hAA hdm _ p _ hp2 X h
  exact coreI_all hodd A d hAA hdm hp2 h

theorem coreInner_thm : CoreInner := by
  intro F _ _ hodd u hu2 hu1 _ p _ hp2 X h
  have hoddc : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
  have hsimple := isSimpleGroup_psp4_of_odd hodd
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hoddc hord
  have h' := PConfig.of_mulEquiv (MulAut.conj g⁻¹ : StatedProj (StatedSp 2 F) ≃*
    StatedProj (StatedSp 2 F)) h
  have hcongr : MulAut.congr (MulAut.conj g⁻¹ : StatedProj (StatedSp 2 F) ≃*
      StatedProj (StatedSp 2 F)) (MulAut.conj u) = MulAut.conj (g⁻¹ * u * g) := by
    rw [congr_eq_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [hcongr] at h'
  rcases hg with hg | hg
  · rw [hg] at h'
    refine false_of_coatom_fixSub (nonabelian_psp4 hodd) ?_ h'
    rw [fixSub_conj]
    exact CFSG.GH74.GLS.Stage2.Local.P34.isCoatom_centralizer_u1 hoddc
  · rw [hg] at h'
    have hT2 : u2 F = proj 2 F (T2 F) := rfl
    rw [hT2, ← conjAut_statedSp (T2 F)] at h'
    refine coreI_all hodd ⟨(T2 F : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp (T2 F).2⟩ (-1) ?_ ?_ hp2 h'
    · rw [Units.val_neg, Units.val_one, neg_one_smul]
      exact T2_mul_T2
    · have hm : multiplierUnit (⟨(T2 F : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp (T2 F).2⟩ : gsp 2 F) = 1 :=
        multiplierUnit_eq _ (by simpa using symplectic_of_mem (T2 F))
      rw [hm]
      simp

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
