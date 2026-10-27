module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

theorem kxSporadicCore_of_inputs (hL613 : L613) (h2401 : KFact2401Spor) (hloc : KFactSporLocal) :
    KxSporadicCore := by
  intro G _ _ p _ M _ z _ _ L c hsp h3 hclos _ hy hnorm _
  obtain ⟨s, e⟩ := hsp
  have hzK : z ∈ L ⊓ M := ⟨c.z_mem, c.conf.config.B_le_M (mem_sup_right (mem_zpowers z))⟩
  have hclos2 : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → z ∈ normalizer (U : Set G) →
      U ⊓ (L ⊓ M) ≠ ⊥ → normalizer (U : Set G) ⊓ L ≤ L ⊓ M := by
    intro U hUL hU2 hz hUK
    have hUM : U ⊓ M ≠ ⊥ := fun h =>
      hUK (le_bot_iff.mp ((inf_le_inf_left U (inf_le_right : L ⊓ M ≤ M)).trans h.le))
    exact le_inf inf_le_right (inf_le_left.trans (c.normalizer_le hUL hU2 hz hUM))
  obtain ⟨⟨H, N, hHK, hsec, hzH, hzN, h3d⟩, hMs⟩ :=
    hloc G L (L ⊓ M) s z p e h3 hclos c.conf.config.prime c.conf.config.situation.p_ge c.rank
      c.orderOf_z inf_le_left hzK (fun h => c.not_le (h.trans inf_le_right))
      (le_inf inf_le_right c.normalizer_zpowers_le) hclos2 hy hnorm
  exact c.le_of_section_three_spor hL613 h2401 e h3 hMs (hHK.trans inf_le_left)
    (hHK.trans inf_le_right) hsec hzH hzN h3d

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
