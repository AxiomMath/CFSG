module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutCoprime
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoUnitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryStabExpThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.CharacterTheory.Wreathed.SimpleOddIndexQuotient
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

theorem autMAt_unitary {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    AutMAt p N := by
  classical
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar Fact.out hO hN
  set K := CFSG.generalizedFitting X with hKdef
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hTsub : ((T : Subgroup ↥K).map K.subtype).subgroupOf K = (T : Subgroup ↥K) := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hnotle : ¬ K ≤ N :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    CFSG.AGLEmbedding.kFactUnitaryBorelMaximal ↥K p d hd ⟨e⟩ T
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    have h := normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN (p := p) (K := K) (Q := (T : Subgroup ↥K).map K.subtype)
      (by rw [hTmap]; exact hPK) (T.isPGroup'.map K.subtype)
      (by rw [hTmap]; exact inf_le_left.trans hPN) (Subgroup.map_subtype_le _)
    rwa [hTsub] at h
  have hne : N.subgroupOf K ≠ ⊤ := fun h => hnotle (Subgroup.subgroupOf_eq_top.1 h)
  have hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    (hle.eq_or_lt.resolve_right fun hlt => hne (hmax.2 _ hlt)).symm
  have hNle : N ≤ Subgroup.normalizer
      (((T : Subgroup ↥K).map K.subtype : Subgroup X) : Set X) :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.le_normalizer_of_subgroupOf_eq_normalizer
      hNK (by rw [hTmap]; exact inf_le_left.trans hPN)
  let ρ : X →* MulAut ↥K := MulAut.conjNormal (G := X) (H := K)
  have hρinj : Function.Injective ρ :=
    CFSG.Wreathed.SimpleOddIndexQuotient.conjNormal_injective_of_centralizer_eq_bot K hKC
  refine autMAt_of_card_le_nine hp5 ?_ (T.isPGroup'.map K.subtype) (by rw [hTmap]; exact hPK)
    (by rw [hTmap]; exact inf_le_left.trans hPN) hNle
    (SEFive.good_unitary hd hO hN e).2
  intro R hRN hexp
  have hstab : ∀ α ∈ R.map ρ, (T : Subgroup ↥K).map α.toMonoidHom = T := by
    intro α hα
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hα
    exact CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.map_conjNormal_eq_of_mem_normalizer
      (hNle (hRN hrR))
  have hexp' : ∀ α ∈ R.map ρ, α ^ 3 = 1 := by
    intro α hα
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hα
    rw [← map_pow, hexp r hrR, map_one]
  have hbound : Nat.card (R.map ρ) ≤ 9 :=
    CFSG.AGLEmbedding.UnitaryModel.card_le_nine_of_stabilizes_sylow (by omega : p ≠ 3) hd e T
      (R.map ρ) hstab hexp'
  have hcard : Nat.card (R.map ρ) = Nat.card R :=
    Subgroup.card_map_of_injective (K := R) hρinj
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
