module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81
public import CFSG.LocalAnalysis.GLTheoremA.CatB.O8p2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

theorem center_aglOm8_eq_bot : Subgroup.center ↥CFSG.AGLEmbedding.Om8 = ⊥ := by
  haveI := CatB.U42Cat.isSimple_om8
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥CFSG.AGLEmbedding.Om8) with
    h | h
  · exact h
  · exfalso
    obtain ⟨E, -, hE⟩ := CatB.O8p2.om8_exists_E64
    letI : CommGroup ↥CFSG.AGLEmbedding.Om8 := Group.commGroupOfCenterEqTop h
    have hp : (Nat.card ↥CFSG.AGLEmbedding.Om8).Prime := IsSimpleGroup.prime_card
    have hd : 2 ^ 6 ∣ Nat.card ↥CFSG.AGLEmbedding.Om8 := hE ▸ Subgroup.card_subgroup_dvd_card E
    rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
