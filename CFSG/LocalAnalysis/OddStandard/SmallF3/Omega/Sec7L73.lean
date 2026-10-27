module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma73_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (hP : Asc82Tab6P) :
    Asc82Lemma73 := by
  intro G _ _ t L S z hctx g hg
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hs2 : orderOf (g⁻¹ * z * g) = 2 := by
    rw [show g⁻¹ * z * g = (MulAut.conj g⁻¹) z by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq, hz2]
  have hsN : g⁻¹ * z * g ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hinv : CFSG.conjugate L (g⁻¹ * z * g)⁻¹ = L :=
      hnorm (g⁻¹ * z * g)⁻¹ (inv_mem hg)
    rw [conjugate_inv_eq_map_conj] at hinv
    simpa using hinv
  have hlayer : layerCent L (g⁻¹ * z * g) = ⊥ :=
    h37 G t L hS z g hctx.pocket hg
  have htab := hP.layer_trivial G L ⟨hS.component.isQuasisimple, hctx.omega6⟩
    (g⁻¹ * z * g) hs2 hsN
  rcases htab.mp hlayer with h4 | h3
  · exact Or.inr h4
  · exact Or.inl h3

end CFSG.OddStandard.SmallF3.Omega
