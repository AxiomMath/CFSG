module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore


theorem j3_coset : ∀ t ∈ j3R, orderOf t = 2 → ∀ s ∈ Sporadic.Schreier.j3P,
    orderOf (t * s) = 2 → ∃ c ∈ Sporadic.Schreier.j3P, c⁻¹ * t * c = t * s := by
  obtain ⟨-, -, -, hrow, hcls, -, -, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hnd : (j3Rows.map fun r => r.outer).Nodup := by decide
  refine coset_of_table le_sup_left (fun r : {r // r ∈ j3Rows} => tp 6156 r.1.rep)
    (fun t ht ht2 => ?_) (fun i j hij => Subtype.ext ?_)
  · obtain ⟨r, hr, g, hg, h⟩ := hcls t ht ht2
    exact ⟨⟨r, hr⟩, g, hg, h⟩
  · refine List.inj_on_of_nodup_map hnd i.2 j.2 (Bool.eq_iff_iff.mpr ?_)
    exact (hrow i.1 i.2).2.2.1.trans ((not_congr hij).trans (hrow j.1 j.2).2.2.1.symm)

theorem j3 : CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .J3 := by
  intro G _ _ N hN hC hY α J hα hJN hJα _ _ _ hZ _
  obtain ⟨e⟩ := hY
  have := hN
  have e' : ↥N ≃* Blueprint.NativeSporadic.J3 := e
  let θ : ↥N ≃* Sporadic.Schreier.j3P := e'.trans Sporadic.Schreier.j3PermEquiv
  have hM := j3_autModel
  obtain ⟨hmem, hord⟩ := embed_mem_orderOf hM hC θ hα
  exact concl_of_coset hα hJN hJα hZ
    (coset_of_autModel hM hC θ (j3_coset _ hmem hord))

end CFSG.ComponentClassification.GSThmB.CF23I
