module

public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements
public import CFSG.Assembly.CatalogTransport
import CFSG.LocalAnalysis.GL83PartI.I_19_1_6
import CFSG.LocalAnalysis.GLTheoremB.BaseCase
import CFSG.SignalizerFunctorTheorem.CatalogBridge.CyclicCatalog
import CFSG.RankThree.PartOne.TCB.Final
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open


theorem input19_1_6_proved : Input19_1_6 := by
  intro G _ _ hK p q hp hq _ H hH E hEH hE hrank
  obtain ⟨A, hAE, -, hAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt E
  have hE2 : p ^ 2 ≤ Nat.card E := by
    have h1 : p ^ 2 ≤ Nat.card A := hAcard ▸ Nat.pow_le_pow_right hp.pos hrank
    exact h1.trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAE))
  refine GL83.I_19_1_6_of_cyclic hp hq hEH hE hE2 ?_
  intro J hJ P hP
  have hsimple : IsSimpleGroup ↥J := hJ.2.1
  have hnonab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra h
    exact hJ.2.2 ⟨⟨fun a b => by_contra fun hab => h ⟨a, b, hab⟩⟩⟩
  have hKcat : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G :=
    CFSG.Assembly.KProper.of_catalogImp CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge hK
  have hHcat : CFSG.SectionRank.IsKGroupCat ↥H :=
    CFSG.ComponentClassification.UnbalancingLocal.kGroupOver_of_kProper
      (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => CFSG.ComponentClassification.UnbalancingLocal.catalog_of_abelian_simple
        S hcomm) hKcat H hH
  have hKH : GLAPPrimeCoreOf p H ≤ H := Subgroup.map_subtype_le _
  have hKcat' : CFSG.SectionRank.IsKGroupCat ↥(GLAPPrimeCoreOf p H) :=
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv (hHcat.subgroup ((GLAPPrimeCoreOf p H).subgroupOf H))
      (Subgroup.subgroupOfEquivOfLe hKH).symm
  have hQcat : CFSG.SectionRank.IsKGroupCat
      (↥(GLAPPrimeCoreOf p H) ⧸ CFSG.solvableRadical ↥(GLAPPrimeCoreOf p H)) :=
    hKcat'.quotient _
  have hJcat : CFSG.Blueprint.Catalog ↥J :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hQcat J (MonoidHom.id ↥J)
      Function.surjective_id
  have hpK : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p H) := not_dvd_card_glaPPrimeCoreOf hp H
  have hcop : Nat.Coprime p (Nat.card J) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpK (h.trans ?_)
    exact (Subgroup.card_subgroup_dvd_card J).trans (Subgroup.card_quotient_dvd_card _)
  exact CFSG.SignalizerFunctorTheorem.CatalogBridge.catalog_pSubgroupsCyclic
    CFSG.RankThree.PartOne.SPOR.sporadicHS_outer_le_two
    CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds hp hsimple hnonab hJcat
    hcop P hP

end CFSG.LocalAnalysis.GLTheoremB
