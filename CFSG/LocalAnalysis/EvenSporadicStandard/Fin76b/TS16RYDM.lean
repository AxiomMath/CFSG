module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYLabel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWLab

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def eDSub {G : Type} [Group G] {M D : Subgroup G} (hDM : D ≤ M)
    (eD : ↥D ≃* DihedralGroup 4) : ↥(D.subgroupOf M) ≃* DihedralGroup 4 :=
  (Subgroup.subgroupOfEquivOfLe hDM).trans eD

theorem coe_sElt_eDSub {G : Type} [Group G] {M D : Subgroup G} (hDM : D ≤ M)
    (eD : ↥D ≃* DihedralGroup 4) (i : ℕ) :
    (((sElt (eDSub hDM eD) i : ↥M)) : G) = sElt eD i := rfl

theorem DECtx.subgroupOf {G : Type} [Group G] {M D E : Subgroup G} {eD : ↥D ≃* DihedralGroup 4}
    {t : G} {eltE : ℕ → G} (h : W16.DECtx D E eD t eltE) (hDM : D ≤ M) (hEM : E ≤ M)
    (htM : t ∈ M) :
    ∃ elt' : ℕ → ↥M, W16.DECtx (D.subgroupOf M) (E.subgroupOf M) (eDSub hDM eD)
      (⟨t, htM⟩ : ↥M) elt' := by
  obtain ⟨elt', hL', -⟩ := ELabelling.subgroupOf h.L hEM htM
  refine ⟨elt', hL', ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 h.tD
  · intro s hs e he
    exact Subtype.ext (h.comm _ (Subgroup.mem_subgroupOf.1 hs) _ (Subgroup.mem_subgroupOf.1 he))

end CFSG.EvenSporadicStandard.Fin76b
