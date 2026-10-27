module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.RankThree.PartTwo.Sec4.Hering432Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.AGLEmbedding CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
  CFSG.RankThree.PartTwo.Sec4

theorem isCoatom_normalizer_of_u33 {K : Type} [Group K] [Finite K]
    (hK : ∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid,
      q.card = 3 ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group))
    (A : Subgroup K) (hA : Nat.card A = 3)
    (hwc : ∀ g : K, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set K) →
      A.map (MulAut.conj g).toMonoidHom = A) :
    IsCoatom (Subgroup.normalizer (A : Set K)) := by
  obtain ⟨q, hv, hq3, he⟩ := hK
  have hp3 : q.p = 3 := (Nat.prime_three.pow_eq_iff.mp (by rw [← q.card_def]; exact hq3)).1
  have hU : IsUnitaryIndex q.p ⟨.twistedA 2 q, hv⟩ := ⟨q, rfl, rfl⟩
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hU he)
  rw [hp3] at hq hF hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := isSimpleGroup_psu J _ hF hfix hq
  haveI : IsSimpleGroup K := e.isSimpleGroup
  obtain ⟨P, hAP, hAC⟩ := Hering432.exists_sylow_le_center_of_weaklyClosed hA hwc
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e P S
  have hcoP : IsCoatom (Subgroup.normalizer ((P : Subgroup K) : Set K)) := by
    refine (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e') _).1 ?_
    rw [MulEquiv.coe_mapSubgroup, Subgroup.map_equiv_normalizer_eq, he', hS]
    exact UnitaryModel.isCoatom_normalizer_rootGroup J hJ hF hfix hq
  have hPN : (P : Subgroup K) ≤ Subgroup.normalizer (A : Set K) :=
    (Subgroup.le_centralizer_iff.mp hAC).trans (Subgroup.centralizer_le_normalizer _)
  have hle : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤ Subgroup.normalizer (A : Set K) := by
    intro g hg
    have hPg : (P : Subgroup K).map (MulAut.conj g).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hAg := hwc g ((Subgroup.map_mono hAP).trans (hPg.le.trans hPN))
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hAg
  have hne : Subgroup.normalizer (A : Set K) ≠ ⊤ := by
    intro htop
    have hnorm : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hnorm.eq_bot_or_eq_top with hbot | htopA
    · rw [hbot, Subgroup.card_bot] at hA
      omega
    · exact hcoP.1 (top_le_iff.mp (by rw [← htopA]; exact hAP.trans Subgroup.le_normalizer))
  rcases hcoP.le_iff.mp hle with h | h
  · exact absurd h hne
  · rw [h]
    exact hcoP

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
