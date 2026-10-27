module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubSec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubStar

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Hyp52

theorem sectionData_of_T_eq {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hS : SchreierFor Blueprint.Catalog) (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    {y : X} (hc : h.SecCond y) (hT : h.T = h.B ⊔ zpowers h.a) (hW : h.NoFusionW) :
    h.SectionData := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
    normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) with hC
  have hSC : h.subS y ≤ C := hc.subS_le
  have hS2 : IsPGroup 2 (h.subS y) :=
    (((B5a.isPGroup_S h).comap_subtype (K := h.secG0 y)).map (h.secMk y)).comap_subtype
  obtain ⟨R, hR⟩ := (hS2.comap_subtype (K := C)).exists_le_sylow
  set S' := (R : Subgroup ↥C).map C.subtype with hS'
  have hS'le : S' ≤ C := map_subtype_le _
  have hS'syl : ∃ R' : Sylow 2 ↥C, (R' : Subgroup ↥C) = S'.subgroupOf C :=
    ⟨R, (comap_map_eq_self_of_injective C.subtype_injective _).symm⟩
  have hSS' : h.subS y ≤ S' := fun z hz =>
    ⟨⟨z, hSC hz⟩, hR (show (⟨z, hSC hz⟩ : ↥C) ∈ (h.subS y).subgroupOf C from hz), rfl⟩
  have hS'2 : IsPGroup 2 S' := R.isPGroup'.map _
  exact hc.sectionData_of_sub S' hS'le hS'syl hSS'
    (fun E hE hEc => hc.isoCorr_subStar hCN hSa hW hT hS'le hS'2 hSS' E hE hEc)
    (hc.inf_normalizer_subB_eq hCN hSa hW hS'2 (hS'le.trans inf_le_left) hSS')

end Hyp52

end CFSG.ComponentClassification.GSThmB
