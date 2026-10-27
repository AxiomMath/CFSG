module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSNorm
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.Goldschmidt.BasicG
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoRho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.Walter.Bender1970.S3.Setup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffTs_mul_self (fr : PFrame Q (Option (Fin 5)) ffC) : ffTs fr * ffTs fr = 1 := by
  rw [ffTs, ← map_mul, ← map_mul, fr.signChange_mul_self, map_one, map_one]

theorem ffTs_ne_one (fr : PFrame Q (Option (Fin 5)) ffC) : ffTs fr ≠ 1 := by
  intro h
  have h1 : toProj Q (fr.signChange {none}) = toProj Q (fr.signChange ∅) := by
    apply projOrthToProjSim_injective (Q := Q)
    rw [← ffTs, fr.signChange_empty, map_one, map_one]
    exact h
  rcases (ff6p_toProj_signChange_eq_iff fr {none} ∅).mp h1 with h2 | h2
  · exact Finset.singleton_ne_empty none h2
  · have hcard : ({none} : Finset (Option (Fin 5))).card = 6 := by
      rw [h2, Finset.card_compl, Finset.card_empty, Fintype.card_option, Fintype.card_fin]
    rw [Finset.card_singleton] at hcard
    omega

theorem ffZ0s_mul_self (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffZ0s hQ fr * ffZ0s hQ fr = 1 := by
  apply Subtype.ext
  change (ffZ0s hQ fr : ProjOrth Q) * (ffZ0s hQ fr : ProjOrth Q) = 1
  rw [ffZ0s, coe_omegaToProj, ← map_mul, ffZ0p_mul_self, map_one]

theorem ffP1p_le_normalizer (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffP1p hQ fr ≤ Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (ffB1p_le_ffP1p hQ fr)).mp
    (ffB1p_normalE16 hQ hπ fr).2.2

theorem ff6p_mem_normalizer_of_N0 (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) {g : ↥(omegaGroup hQ)}
    (hg : (g : OGroup Q) ∈ ffN0p hQ fr) :
    omegaToProj hQ g ∈ Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [ffB1p, mem_ffStar_iff, mem_ffStar_iff]
  constructor
  · rintro ⟨a, ha, hae⟩
    refine ⟨g * a * g⁻¹, ?_, ?_⟩
    · have hgN : (g : OGroup Q) ∈ Subgroup.normalizer (ffB0p fr : Set (OGroup Q)) :=
        (Subgroup.mem_inf.mp hg).2
      exact (Subgroup.mem_normalizer_iff.mp hgN (a : OGroup Q)).mp ha
    · rw [map_mul, map_mul, map_inv, hae]
  · rintro ⟨a, ha, hae⟩
    refine ⟨g⁻¹ * a * g, ?_, ?_⟩
    · have hgN : (g : OGroup Q) ∈ Subgroup.normalizer (ffB0p fr : Set (OGroup Q)) :=
        (Subgroup.mem_inf.mp hg).2
      have hgi : (g : OGroup Q)⁻¹ ∈ Subgroup.normalizer (ffB0p fr : Set (OGroup Q)) :=
        (Subgroup.normalizer (ffB0p fr : Set (OGroup Q))).inv_mem hgN
      exact (Subgroup.mem_normalizer_iff.mp hgi (a : OGroup Q)).mp ha
    · rw [map_mul, map_mul, map_inv, hae]
      group

theorem ffTs_comm_normalizer (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hπ : piOrth Q ∉ omegaGroup hQ) (fr : PFrame Q (Option (Fin 5)) ffC) {n : ↥(omegaProj hQ)}
    (hn : n ∈ Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) :
    ffTs fr * ffOmegaToSim hQ n = ffOmegaToSim hQ n * ffTs fr := by
  obtain ⟨g, hgN0, rfl⟩ := ff6p_star_normalizer hQ h2 hπ fr hn
  have hcomm : fr.signChange {none} * (g : OGroup Q) = (g : OGroup Q) * fr.signChange {none} := by
    obtain ⟨σ, b, hb, hg_eq⟩ := (mem_ffN0p_iff hQ fr).mp hgN0
    obtain ⟨J, -, hbJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hb
    rw [hg_eq, hbJ]
    have hσ : ffHat fr σ * fr.signChange {none} = fr.signChange {none} * ffHat fr σ := by
      have hconj := ffHat_conj_signChange fr σ ({none} : Finset (Option (Fin 5)))
      have hmap : ({none} : Finset (Option (Fin 5))).map
          (Equiv.optionCongr σ).toEmbedding = {none} := by
        rw [Finset.map_singleton]
        rfl
      rw [hmap] at hconj
      calc ffHat fr σ * fr.signChange {none}
          = (ffHat fr σ * fr.signChange {none} * (ffHat fr σ)⁻¹) * ffHat fr σ := by group
        _ = fr.signChange {none} * ffHat fr σ := by rw [hconj]
    calc fr.signChange {none} * (ffHat fr σ * fr.signChange (ffOpt J))
        = (fr.signChange {none} * ffHat fr σ) * fr.signChange (ffOpt J) := by group
      _ = (ffHat fr σ * fr.signChange {none}) * fr.signChange (ffOpt J) := by rw [← hσ]
      _ = ffHat fr σ * (fr.signChange {none} * fr.signChange (ffOpt J)) := by group
      _ = ffHat fr σ * (fr.signChange (ffOpt J) * fr.signChange {none}) := by
            rw [fr.signChange_comm]
      _ = (ffHat fr σ * fr.signChange (ffOpt J)) * fr.signChange {none} := by group
  rw [ffOmegaToSim_apply, coe_omegaToProj, ffTs]
  simp only [← map_mul]
  rw [hcomm]

theorem ffTs_comm_ffZ0s (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hπ : piOrth Q ∉ omegaGroup hQ) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) = ffOmegaToSim hQ (ffZ0s hQ fr) * ffTs fr :=
  ffTs_comm_normalizer hQ h2 hπ fr (Subgroup.le_normalizer (ffZ0s_mem_ffB1p hQ fr))

theorem ff6p_cent_sim_cases (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hz : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) :
    (∃ b ∈ ffB1p hQ fr, z = ffOmegaToSim hQ b) ∨
      ∃ b ∈ ffB1p hQ fr, z = ffTs fr * ffOmegaToSim hQ b := by
  obtain ⟨K, hK⟩ := ff6p_star_cent_sim hQ h2 fr hz
  have key : ∀ K : Finset (Option (Fin 5)),
      (∃ b ∈ ffB1p hQ fr,
        projOrthToProjSim Q (toProj Q (fr.signChange K)) = ffOmegaToSim hQ b) ∨
      ∃ b ∈ ffB1p hQ fr,
        projOrthToProjSim Q (toProj Q (fr.signChange K)) =
          ffTs fr * ffOmegaToSim hQ b := by
    intro K
    have hKc : projOrthToProjSim Q (toProj Q (fr.signChange K)) =
        projOrthToProjSim Q (toProj Q (fr.signChange (if none ∈ K then Kᶜ else K))) := by
      by_cases h : none ∈ K
      · rw [if_pos h, ← ff6p_toProj_signChange_compl fr K]
      · rw [if_neg h]
    rw [hKc]
    have hnone : none ∉ (if none ∈ K then Kᶜ else K) := by
      by_cases h : none ∈ K
      · rw [if_pos h]; simp [h]
      · rw [if_neg h]; exact h
    obtain ⟨J, hJ⟩ := exists_ffOpt_of_none_notMem (K := if none ∈ K then Kᶜ else K) hnone
    rw [hJ]
    by_cases hJe : Even J.card
    · left
      have hb0 : fr.signChange (ffOpt J) ∈ ffB0p fr :=
        (mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJe, rfl⟩
      have hω : fr.signChange (ffOpt J) ∈ omegaGroup hQ := ffB0p_le_omega hQ fr hb0
      refine ⟨omegaToProj hQ ⟨fr.signChange (ffOpt J), hω⟩, ?_, ?_⟩
      · rw [ffB1p, mem_ffStar_iff]
        exact ⟨⟨fr.signChange (ffOpt J), hω⟩, hb0, rfl⟩
      · rw [ffOmegaToSim_apply, coe_omegaToProj]
    · right
      have hsymm : symmDiff ({none} : Finset (Option (Fin 5))) (insert none (ffOpt J)) =
          ffOpt J := by
        ext x
        cases x with
        | none => exact iff_of_false (by simp [Finset.mem_symmDiff]) (none_notMem_ffOpt J)
        | some i => simp [Finset.mem_symmDiff, mem_ffOpt_some]
      have hcompl : (insert none (ffOpt J))ᶜ = ffOpt Jᶜ := by
        ext x
        cases x with
        | none => simp [none_notMem_ffOpt]
        | some i => simp [mem_ffOpt_some]
      have ht : fr.signChange {none} * fr.signChange (insert none (ffOpt J)) =
          fr.signChange (ffOpt J) := by
        rw [fr.signChange_mul, hsymm]
      have hJcEven : Even (Jᶜ).card := by
        rw [Finset.card_compl, Fintype.card_fin]
        obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hJe
        have hle : J.card ≤ 5 := by simpa using Finset.card_le_univ J
        exact ⟨2 - k, by omega⟩
      have hb0 : fr.signChange (ffOpt Jᶜ) ∈ ffB0p fr :=
        (mem_ffB0p_iff_ffOpt fr).mpr ⟨Jᶜ, hJcEven, rfl⟩
      have hω : fr.signChange (ffOpt Jᶜ) ∈ omegaGroup hQ := ffB0p_le_omega hQ fr hb0
      refine ⟨omegaToProj hQ ⟨fr.signChange (ffOpt Jᶜ), hω⟩, ?_, ?_⟩
      · rw [ffB1p, mem_ffStar_iff]
        exact ⟨⟨fr.signChange (ffOpt Jᶜ), hω⟩, hb0, rfl⟩
      · rw [ffTs, ffOmegaToSim_apply, coe_omegaToProj]
        simp only [← map_mul]
        congr 1
        rw [map_mul, ← hcompl, ff6p_toProj_signChange_compl fr (insert none (ffOpt J)),
          ← map_mul, ht]
  rcases key K with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · exact Or.inl ⟨b, hb, hK.trans hzb⟩
  · exact Or.inr ⟨b, hb, hK.trans hzb⟩

private theorem ffOutFF6PSCent_comm_hat_eq_one (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {b : ↥(omegaProj hQ)} (hb : b ∈ ffB1p hQ fr)
    (hc : ∀ σ : Equiv.Perm (Fin 5),
      b * omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ =
        omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ * b) : b = 1 := by
  obtain ⟨J, hJe, hbJ⟩ := (mem_ffB1p_iff hQ fr).mp hb
  have hfix : ∀ σ : Equiv.Perm (Fin 5), ffAct σ J = J := by
    intro σ
    have h := congrArg (fun x : ↥(omegaProj hQ) => (x : ProjOrth Q)) (hc σ)
    simp only [Subgroup.coe_mul, coe_omegaToProj] at h
    rw [hbJ] at h
    have h2 : toProj Q (fr.signChange (ffOpt J)) =
        toProj Q (fr.signChange (ffOpt (ffAct σ J))) := by
      have h3 : toProj Q (fr.signChange (ffOpt J)) =
          toProj Q (ffHat fr σ * fr.signChange (ffOpt J) * (ffHat fr σ)⁻¹) := by
        rw [map_mul, map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
      calc toProj Q (fr.signChange (ffOpt J))
          = toProj Q (ffHat fr σ * fr.signChange (ffOpt J) * (ffHat fr σ)⁻¹) := h3
        _ = toProj Q (fr.signChange (ffOpt (ffAct σ J))) := by
              rw [ffHat_conj_signChange_ffOpt]
    rcases (ff6p_toProj_signChange_eq_iff fr (ffOpt J) (ffOpt (ffAct σ J))).mp h2 with h3 | h3
    · exact (ffOpt_injective h3).symm
    · exact absurd (h3 ▸ Finset.mem_compl.mpr (none_notMem_ffOpt (ffAct σ J)))
        (none_notMem_ffOpt J)
  have hJ : J = ∅ ∨ J = Finset.univ := by
    by_contra h
    rw [not_or] at h
    obtain ⟨hne, hne'⟩ := h
    have hnon : ∃ a : Fin 5, a ∈ J := by
      by_contra hcon
      push Not at hcon
      exact hne (Finset.eq_empty_iff_forall_notMem.mpr hcon)
    have hnot : ∃ c : Fin 5, c ∉ J := by
      by_contra hcon
      push Not at hcon
      exact hne' (Finset.eq_univ_iff_forall.mpr hcon)
    obtain ⟨a, ha⟩ := hnon
    obtain ⟨c, hc⟩ := hnot
    have hac : a ≠ c := fun h => hc (h ▸ ha)
    have hmem : c ∈ ffAct (Equiv.swap a c) J := by
      rw [ffAct, Finset.mem_map]
      exact ⟨a, ha, Equiv.swap_apply_left a c⟩
    rw [hfix (Equiv.swap a c)] at hmem
    exact hc hmem
  rcases hJ with hJ | hJ
  · apply Subtype.ext
    rw [hbJ, hJ, ffOpt, Finset.map_empty, fr.signChange_empty, map_one]
    rfl
  · exfalso
    rw [hJ, Finset.card_univ, Fintype.card_fin] at hJe
    exact (by decide : ¬ Even 5) hJe

theorem ff6p_cent_normalizer (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hπ : piOrth Q ∉ omegaGroup hQ) (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hz : ∀ n ∈ Subgroup.normalizer
        ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)),
      z * ffOmegaToSim hQ n = ffOmegaToSim hQ n * z) :
    z = 1 ∨ z = ffTs fr := by
  have hz' : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z :=
    fun b hb => hz b (Subgroup.le_normalizer hb)
  rcases ff6p_cent_sim_cases hQ h2 fr hz' with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · left
    have hcomm : ∀ σ : Equiv.Perm (Fin 5),
        b * omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ =
          omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ * b := by
      intro σ
      have hn : omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ ∈
          Subgroup.normalizer
            ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) :=
        ff6p_mem_normalizer_of_N0 hQ hπ fr (ffHat_mem_ffN0p hQ fr σ)
      apply ffOmegaToSim_injective hQ
      rw [map_mul, map_mul, ← hzb]
      exact hz _ hn
    rw [hzb, ffOutFF6PSCent_comm_hat_eq_one hQ fr hb hcomm, map_one]
  · right
    have hcomm : ∀ σ : Equiv.Perm (Fin 5),
        b * omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ =
          omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ * b := by
      intro σ
      let n : ↥(omegaProj hQ) := omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩
      have hn : n ∈ Subgroup.normalizer
          ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) :=
        ff6p_mem_normalizer_of_N0 hQ hπ fr (ffHat_mem_ffN0p hQ fr σ)
      have hb_eq : ffOmegaToSim hQ b = ffTs fr * z := by
        rw [hzb, ← mul_assoc, ffTs_mul_self, one_mul]
      apply ffOmegaToSim_injective hQ
      rw [map_mul, map_mul, hb_eq]
      calc (ffTs fr * z) * ffOmegaToSim hQ n
          = ffTs fr * (z * ffOmegaToSim hQ n) := by group
        _ = ffTs fr * (ffOmegaToSim hQ n * z) := by rw [hz n hn]
        _ = (ffTs fr * ffOmegaToSim hQ n) * z := by group
        _ = (ffOmegaToSim hQ n * ffTs fr) * z := by
              rw [ffTs_comm_normalizer hQ h2 hπ fr hn]
        _ = ffOmegaToSim hQ n * (ffTs fr * z) := by group
    rw [hzb, ffOutFF6PSCent_comm_hat_eq_one hQ fr hb hcomm, map_one, mul_one]

theorem ff6p_cent_P1 (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hπ : piOrth Q ∉ omegaGroup hQ) (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hz : ∀ p ∈ ffP1p hQ fr, z * ffOmegaToSim hQ p = ffOmegaToSim hQ p * z) :
    z = 1 ∨ z = ffOmegaToSim hQ (ffZ0s hQ fr) ∨ z = ffTs fr ∨
      z = ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) := by
  have hz' : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z :=
    fun b hb => hz b (ffB1p_le_ffP1p hQ fr hb)
  rcases ff6p_cent_sim_cases hQ h2 fr hz' with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · have hcomm : ∀ p ∈ ffP1p hQ fr, b * p = p * b := by
      intro p hp
      apply ffOmegaToSim_injective hQ
      rw [map_mul, map_mul, ← hzb]
      exact hz p hp
    rcases ffP1p_center hQ hπ fr (ffB1p_le_ffP1p hQ fr hb)
      (fun h hh => (hcomm h hh).symm) with hb1 | hbz
    · left; rw [hzb, hb1, map_one]
    · right; left; rw [hzb, hbz]
  · have hcomm : ∀ p ∈ ffP1p hQ fr, b * p = p * b := by
      intro p hp
      have hpN : p ∈ Subgroup.normalizer
          ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) :=
        ffP1p_le_normalizer hQ hπ fr hp
      have hb_eq : ffOmegaToSim hQ b = ffTs fr * z := by
        rw [hzb, ← mul_assoc, ffTs_mul_self, one_mul]
      apply ffOmegaToSim_injective hQ
      rw [map_mul, map_mul, hb_eq]
      calc (ffTs fr * z) * ffOmegaToSim hQ p
          = ffTs fr * (z * ffOmegaToSim hQ p) := by group
        _ = ffTs fr * (ffOmegaToSim hQ p * z) := by rw [hz p hp]
        _ = (ffTs fr * ffOmegaToSim hQ p) * z := by group
        _ = (ffOmegaToSim hQ p * ffTs fr) * z := by
              rw [ffTs_comm_normalizer hQ h2 hπ fr hpN]
        _ = ffOmegaToSim hQ p * (ffTs fr * z) := by group
    rcases ffP1p_center hQ hπ fr (ffB1p_le_ffP1p hQ fr hb)
      (fun h hh => (hcomm h hh).symm) with hb1 | hbz
    · right; right; left; rw [hzb, hb1, map_one, mul_one]
    · right; right; right; rw [hzb, hbz]

end CFSG.OddStandard.SmallF3.Omega
