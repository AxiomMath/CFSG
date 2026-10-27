module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIICensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIW
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.PSL3Four
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def gR : ℕ → Equiv.Perm (Fin 42)
  | 0 => g₁ | 1 => g₂ | 2 => g₃ | 3 => g₄ | 4 => g₅ | _ => g₆

theorem rep_l34GensR : ∀ j < l34GensR.size, Rep 42 l34GensR[j]! (gR j) := by
  intro j hj
  have hj' : j < 6 := hj
  interval_cases j
  · exact tabRep_g₁.2
  · exact tabRep_g₂.2
  · exact tabRep_g₃.2
  · exact tabRep_g₄.2
  · exact tabRep_g₅.2
  · exact tabRep_g₆.2

theorem rep_l34GensS : ∀ j < l34GensS.size, Rep 42 l34GensS[j]! (gR j) := by
  intro j hj
  have hj' : j < 3 := hj
  interval_cases j
  · exact tabRep_g₁.2
  · exact tabRep_g₂.2
  · exact tabRep_g₃.2

theorem closure_permsA_l34GensR : closure (permsA 42 l34GensR) = R := by
  rw [R]
  congr 1
  ext x
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [permOfArr_eq_of_rep (rep_l34GensR j hj)]
    have hj' : j < 6 := hj
    interval_cases j <;> simp [gR]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by decide, permOfArr_eq_of_rep (rep_l34GensR 0 (by decide))⟩
    · exact ⟨1, by decide, permOfArr_eq_of_rep (rep_l34GensR 1 (by decide))⟩
    · exact ⟨2, by decide, permOfArr_eq_of_rep (rep_l34GensR 2 (by decide))⟩
    · exact ⟨3, by decide, permOfArr_eq_of_rep (rep_l34GensR 3 (by decide))⟩
    · exact ⟨4, by decide, permOfArr_eq_of_rep (rep_l34GensR 4 (by decide))⟩
    · exact ⟨5, by decide, permOfArr_eq_of_rep (rep_l34GensR 5 (by decide))⟩

theorem closure_permsA_l34GensS : closure (permsA 42 l34GensS) = S := by
  rw [S]
  congr 1
  ext x
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [permOfArr_eq_of_rep (rep_l34GensS j hj)]
    have hj' : j < 3 := hj
    interval_cases j <;> simp [gR]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, permOfArr_eq_of_rep (rep_l34GensS 0 (by decide))⟩
    · exact ⟨1, by decide, permOfArr_eq_of_rep (rep_l34GensS 1 (by decide))⟩
    · exact ⟨2, by decide, permOfArr_eq_of_rep (rep_l34GensS 2 (by decide))⟩

theorem l34InS_iff (h : enumOK 42 l34GensS l34PS l34EnumS = true) {a : Array ℕ}
    {g : Equiv.Perm (Fin 42)} (ha : Rep 42 a g) : l34InS a = true ↔ g ∈ S := by
  rw [← closure_permsA_l34GensS]
  constructor
  · intro hin
    exact enumOK_mem_of_any l34PS_lt h ha hin
  · intro hg
    obtain ⟨i, hi, hr⟩ := enumOK_exists_rep l34PS_lt h hg
    have hmem : l34EnumS.pts[i]! ∈ l34EnumS.pts.toList := by
      rw [getElem!_pos l34EnumS.pts i hi]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
    rw [l34InS, memA, List.any_eq_true]
    exact ⟨l34EnumS.pts[i]!, hmem, (eqA_iff ha hr).2 rfl⟩

theorem l34SW_getElem! {i : ℕ} (hi : i < 3) : l34SW[i]! = l34GensS[i]! :=
  CFSG.EvenSmallLie.OmegaEight.pushWords_getElem! _ _
    (by simp [l34GensS, CFSG.PSL3Four.Native.gensS]; omega)

@[expose] noncomputable def l34QW : CFSG.Certificates.RawSchreierDatum 42 :=
  CFSG.Certificates.RawSchreierDatum.ofArrays 42 (by norm_num) l34SW 3 (by
    simp [l34SW, l34GensS, CFSG.PSL3Four.Native.gensS,
      CFSG.EvenSmallLie.OmegaEight.size_pushWords, l34DW])
    l34BaseWL (by decide) (CFSG.EvenSmallLie.OmegaEight.wordsOf 3 l34DW)

theorem l34QW_originalSubgroup : l34QW.originalSubgroup = S := by
  rw [l34QW, CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup,
    ← closure_permsA_l34GensS]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi3 : i < 3 := by simpa using hi
    refine ⟨i, by simpa [l34GensS, CFSG.PSL3Four.Native.gensS] using hi3, ?_⟩
    rw [l34SW_getElem! hi3]
  · rintro ⟨i, hi, rfl⟩
    have hi3 : i < 3 := by simpa [l34GensS, CFSG.PSL3Four.Native.gensS] using hi
    refine ⟨i, by simpa using hi3, ?_⟩
    rw [l34SW_getElem! hi3]

theorem l34InSW_iff (hch : CFSG.Certificates.Native.rawChainOK 42 (l34SW.extract 0 3) l34SW l34BaseW
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 3 l34DW) 4 = true)
    {a : Array ℕ} {g : Equiv.Perm (Fin 42)} (h : Rep 42 a g) : l34InSW a = true ↔ g ∈ S := by
  rw [← l34QW_originalSubgroup]
  exact CFSG.ComponentClassification.J2Cover.ofArrays_mem_iff (by norm_num) hch h

theorem l34AutModel : AutModel ↥S ↥R (S.subgroupOf R) := by
  obtain ⟨e, he, -⟩ := full_automorphism_action
  exact autModel_of_conj S_le_R (MulEquiv.refl ↥S) e he

theorem l34_yCensusII {sc sp : String}
    (h : l34CheckII sc sp = true) : YCensus (S.subgroupOf R) (· ≤ S.subgroupOf R) := by
  simp only [l34CheckII, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hE, hslp⟩, hc⟩, hgen⟩, hsize⟩ := h
  refine yCensusII_of_check_regs (k := 8) (m := 945) S_le_R S_normal l34PS_lt
    (fun a g ha => l34InS_iff hE ha) (fun r hr => ?_) hc hgen hsize
    (by rw [card_R]; norm_num) (by decide)
  obtain ⟨g, hg, hrep⟩ := rep_slpRegs hslp r hr
  exact ⟨g, closure_permsA_l34GensR ▸ hg, hrep⟩

theorem hypII_L34_of_check {sc sp : String}
    (hc : l34CheckII sc sp = true) : AS81.L34HypII := by
  intro A _ _ hA hL
  obtain ⟨e⟩ := nonempty_equiv_of_stated (A ⧸ center A) hL
  exact hypII_of_yCensus l34AutModel (l34_yCensusII hc) hA e

end CFSG.ComponentClassification.RankTwoL3Four.HypII
