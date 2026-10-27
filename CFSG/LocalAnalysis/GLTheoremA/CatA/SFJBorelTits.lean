module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GChev
public import CFSG.Assembly.InCatalogConverse

public section


namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

theorem I137BorelTits_holds : I137BorelTits := by
  intro K _ _ hK T hT hT0
  have hcat : ∃ i : TauCeti.CFSGIndex, Nonempty (K ≃* i.Group) := by
    rcases hK with ⟨i, -, hi⟩ | ⟨i, -, hi⟩
    · exact ⟨i, hi⟩
    · exact ⟨i, hi⟩
  obtain ⟨-, hsimp⟩ := CFSG.Assembly.inCatalog_converse K hcat
  obtain ⟨a, b, hab⟩ := chevTwoNonabelian_holds K hsimp hK
  refine ⟨Subgroup.normalizer (T : Set K), ?_, le_rfl⟩
  intro htop
  have hTn : T.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hsimp.eq_bot_or_eq_top_of_normal T with h | h
  · exact hT0 h
  · have hp : IsPGroup 2 K := by
      intro g
      have hg : g ∈ T := by rw [h]; exact Subgroup.mem_top g
      obtain ⟨k, hk⟩ := hT ⟨g, hg⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hnt : Nontrivial (Subgroup.center K) := IsPGroup.center_nontrivial hp
    rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hc
    · have ha : a ∈ Subgroup.center K := by rw [hc]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm

end CFSG.LocalAnalysis.GLTheoremA
