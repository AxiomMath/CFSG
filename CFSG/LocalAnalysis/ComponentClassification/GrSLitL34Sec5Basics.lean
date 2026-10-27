module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Sec5Basics_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
      L34Sec5Setting G L t S T →
      pRank 2 ↥(S ⊓ coreActionKernel L) ≤ 2 ∧
        t ∈ centralizer (oddIn L : Set G) ∧
        ∀ s ∈ S ⊓ coreActionKernel L ⊓ centralizer (oddIn L : Set G), orderOf s = 2 → s = t := by
  intro G _ _ L t S T hset
  obtain ⟨huniq, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨hbase, hfam, -, -, -, -, -⟩ := hset
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, hX, hW8'⟩ := hfam
  have : IsSimpleGroup G := hsimple
  have hsC : ∀ s ∈ S, s ∈ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hZS s hs)
  refine ⟨?_, ?_, ?_⟩
  ·
    by_contra h
    push Not at h
    obtain ⟨F, hFQ, hF8⟩ := exists_eightGroup_of_three_le_pRank
      (Q := S ⊓ coreActionKernel L) (by omega)
    have hFS : F ≤ S := hFQ.trans inf_le_left
    have hFK : F ≤ coreActionKernel L := hFQ.trans inf_le_right
    have hWF := hW8' F hF8 (Or.inr hFK)
    have hFt : F ≤ centralizer ({t} : Set G) := fun f hf => hsC f (hFS hf)
    have hFN : F ≤ normalizer (L : Set G) := fun f hf => (mem_coreActionKernel.mp (hFK hf)).1
    have hbal : ∀ e ∈ F, e ≠ 1 →
        ⁅(pPrimeCore 2 L).map L.subtype ⊓ centralizer ({e} : Set G),
          (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map
            (L ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
        (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype :=
      fun e he he1 => commutator_oddCore_pLayer_le hS hU hheld hK hto hLt hLpt
        (hZS e (hFS he)).symm
        (centralizer_ne_top_of_not_mem_center (not_mem_center_of_ne_one hnonab he1))
    have hcom := oddCore_le_center_of_wGroup_eq_bot hLt hLpt hFt hF8.1.1 hF8.1.2
      (by rw [hF8.2]; norm_num) hFN (fun e he => conj_mem_oddIn_of_mem_coreActionKernel (hFK he))
      hWF hbal (Or.inr (by rw [hF8.2]))
    apply hX
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hcom _ ⟨x, hx, rfl⟩ g g.2).symm
  ·
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hLt (map_subtype_le _ hy))
  ·
    intro s hs hs2
    obtain ⟨⟨hsS, hsK⟩, hsX⟩ := mem_inf.mp hs |>.imp_left mem_inf.mp
    have hsp : IsPGroup 2 (zpowers s) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hs2, pow_one]
    have hsL := mem_centralizer_of_mem_coreActionKernel hLt hLpt (hsC s hsS) hsK hsp hsX
    exact huniq s (mem_inf.mpr ⟨hsS, hsL⟩) hs2

end CFSG.ComponentClassification.GrSLit.GrS5
