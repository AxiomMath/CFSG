module

public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.ClassicalInvolution.Q3.TL4VtxDich

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


theorem tightLinkDatumR_three (n : ℕ) : TightLinkDatumR 3 n := by
  intro Y _ _ R S t hL _ hT htr
  have h := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  obtain ⟨J, hJ, -⟩ := exists_noGNbr_of_not_triNbrAll hT
  have hK := subgroupOf_mem_linkRestrict (t := t) hJ
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
  obtain ⟨S'⟩ := (inferInstance : Nonempty (Sylow 2
    ↥((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))))
  have hcore : tightCore ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf
      (linkGrp R t)) = (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf
      (linkGrp R t) := h.closure_twoElts hK
  refine ⟨_, S', z, Vtx.tightDatum_of_mem h hK hz S',
    ⟨Vtx.nonempty_sylow_equiv h hK S', ?_, oddCore_linkGrp_eq_bot hL⟩, ?_⟩
  · show (⨆ g : ↥(linkGrp R t), conjSub g (tightCore _)) = ⊤
    rw [hcore, eq_top_iff, ← omegaGen_linkRestrict (R := R) (t := t)]
    refine iSup₂_le fun L hL' => ?_
    obtain ⟨g, rfl⟩ := htr _ hK L hL'
    exact le_iSup (fun g : ↥(linkGrp R t) =>
      conjSub g ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) g
  · rw [hcore]
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact h.hyp.conjInvariant g _ hK
    · intro hL'
      exact htr _ hK L hL'

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
