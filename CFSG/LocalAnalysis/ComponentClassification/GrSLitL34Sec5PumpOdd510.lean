module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5OTwoFam510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp510

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem oddIn_pumpUp_le_center_of_wGroup
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hbase : L34BaseSetting G) {c v : G} {K₁ F : Subgroup G} (hc2 : orderOf c = 2)
    (hK₁c : K₁ ≤ centralizer ({c} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({c} : Set G))))
    (hvo : orderOf v = 2) (hcv : c * v = v * c) (hK₁v : K₁ ≤ centralizer ({v} : Set G))
    (hT91 : (⨆ (g : G) (_ : conjugate K₁ g ≤ centralizer ({v} : Set G)), conjugate K₁ g) ≤
      oddIn (centralizer ({v} : Set G)) ⊔ K₁)
    (hF : IsEightGroup F) (hWF : wGroup F = ⊥) (hFK : F ≤ coreActionKernel K₁)
    (hFv : ∀ f ∈ F, f * v = v * f) :
    oddIn (pumpUp K₁ v) ≤ (center ↥K₁).map K₁.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have hv1 : v ≠ 1 := by
    rintro rfl
    simp at hvo
  have hvZ : v ∉ center G := not_mem_center_of_ne_one hnonab hv1
  have hgs := gsFixedLayer_eq_of_le hK₁c hK₁p hK₁v
  have hsup := sup_oddIn_pumpUp hK₁v hgs hT91
  have hPp := isPComponent_pumpUp hS hK hc2 hvo hcv hvZ hK₁c hK₁p hK₁v hT91
  have hPv : pumpUp K₁ v ≤ centralizer ({v} : Set G) := pumpUp_le_centralizer K₁ v
  have hperf : ⁅pumpUp K₁ v, pumpUp K₁ v⁆ = pumpUp K₁ v := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hPp
    have h2 : Group.IsPerfect ↥(pumpUp K₁ v) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPv).toMonoidHom)
        (subgroupOfEquivOfLe hPv).surjective
    exact (Subgroup.isPerfect_iff (H := pumpUp K₁ v)).mp h2
  by_contra hbad
  have hc := not_oddIn_le_center_pumpUp hsup hperf hbad
  have hFL : ∀ f ∈ F, f ∈ coreActionKernel (pumpUp K₁ v) := fun f hf =>
    mem_coreActionKernel_pumpUp hK₁c hK₁p hK₁v hsup (hFK hf) (hFv f hf)
  have hbal : ∀ e ∈ F, e ≠ 1 →
      ⁅(pPrimeCore 2 (pumpUp K₁ v)).map (pumpUp K₁ v).subtype ⊓ centralizer ({e} : Set G),
        (pLayer ↥(pumpUp K₁ v ⊓ centralizer ({e} : Set G)) 2).map
          (pumpUp K₁ v ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype :=
    fun e he he1 => commutator_oddCore_pLayer_le hS hU hheld hK hvo hPv hPp (hFv e he).symm
      (centralizer_ne_top_of_not_mem_center (not_mem_center_of_ne_one hnonab he1))
  have hcom := oddCore_le_center_of_wGroup_eq_bot hPv hPp
    (fun e he => mem_centralizer_singleton_iff.mpr (hFv e he)) hF.1.1 hF.1.2
    (by rw [hF.2]; norm_num) (fun e he => (mem_coreActionKernel.mp (hFL e he)).1)
    (fun e he => conj_mem_oddIn_of_mem_coreActionKernel (hFL e he)) hWF hbal
    (Or.inr (by rw [hF.2]))
  exact hc (oddIn_le_map_center hcom)

theorem oddIn_pumpUp_le_center_of_eight
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (hElem : L34ElementaryCenterSylowFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    {u b : G} {K₁ F : Subgroup G} (hu2 : orderOf u = 2)
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hbo : orderOf b = 2) (hub : u * b = b * u) (hK₁b : K₁ ≤ centralizer ({b} : Set G))
    (hT91 : (⨆ (g : G) (_ : conjugate K₁ g ≤ centralizer ({b} : Set G)), conjugate K₁ g) ≤
      oddIn (centralizer ({b} : Set G)) ⊔ K₁)
    (hF : IsEightGroup F) (hFP : F ≤ S ⊓ L ⊔ omegaOne (S ⊓ coreActionKernel L))
    (hFK : F ≤ coreActionKernel K₁) (hFb : ∀ f ∈ F, f * b = b * f) :
    oddIn (pumpUp K₁ b) ≤ (center ↥K₁).map K₁.subtype :=
  oddIn_pumpUp_le_center_of_wGroup hS hU hheld hset.1 hu2 hK₁u hK₁p hbo hub hK₁b hT91 hF
    (wGroup_eq_bot_of_le_sup_omegaOne hS hU hheld hSol hGW h58 hElem hset hF hFP) hFK hFb

end CFSG.ComponentClassification.GrSLit.GrS5
