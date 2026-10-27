module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdHeSuz
public import CFSG.Sporadic.SmallOddCore.HeLocal

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore


theorem he : CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .He := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  obtain ⟨e⟩ := hY
  have := hN
  have e' : ↥N ≃* Blueprint.NativeSporadic.He := e
  by_cases hαN : α ∈ N
  · exact (false_of_inner_card hα hαN hJN hJα hJ hsmall fun a ha B hB =>
      cti_he_involution_local_components_simple_quotient_order ⟨e'⟩ ha hB).elim
  · let θ : ↥N ≃* Sporadic.HeldB.heP := e'.trans Sporadic.HeldB.heEquivP
    have hM := Catalog7Std.heAutModelStd
    obtain ⟨hmem, hord⟩ := embed_mem_orderOf hM hC θ hα
    have hnP : hM.embed N θ α ∉ Sporadic.HeldB.heP := fun h =>
      hαN ((embed_mem_iff hM hC θ α).1 h)
    exact concl_of_coset hα hJN hJα hZ (coset_of_autModel hM hC θ
      (coset_of_rep_outer hM.le Sporadic.HeldB.heAutU
        (fun _ ht htP ht2 => Sporadic.HeldB.exists_conj_heAutU ht htP ht2) _ hmem hnP hord))

end CFSG.ComponentClassification.GSThmB.CF23I
