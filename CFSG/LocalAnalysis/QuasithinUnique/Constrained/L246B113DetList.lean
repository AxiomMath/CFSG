module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Native
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Cited
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native

public section

namespace CFSG.QuasithinUnique.Bridge.B113Det

open CFSG.Blueprint CFSG.Milestones

theorem sqtkSimpleList_of_quasisimple
    {G L : Type} [Group G] [Group L] (f : L →* G)
    (hf : Function.Injective f) (hSQ : IsSQTKQuotient CFSG.SectionRank.IsKGroupCat G)
    (hL : CFSG.IsQuasisimple L) : SQTKSimpleList (L ⧸ Subgroup.center L) := by
  obtain ⟨Y, _, _, φ, hφ, hSQT, hK⟩ := hSQ
  have hSQTK : CFSG.SectionRank.IsSQTKCat Y :=
    ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr hSQT, hK⟩
  let θ₀ : ↥(f.range.comap φ) →* L :=
    (MonoidHom.ofInjective hf).symm.toMonoidHom.comp (φ.subgroupComap f.range)
  have hθ₀ : Function.Surjective θ₀ := by
    intro l
    obtain ⟨y, hy⟩ := hφ (f l)
    have hmem : φ y ∈ f.range := by rw [hy]; exact ⟨l, rfl⟩
    refine ⟨⟨y, hmem⟩, ?_⟩
    show (MonoidHom.ofInjective hf).symm ⟨φ y, hmem⟩ = l
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [MonoidHom.ofInjective_apply]; exact hy)
  let θ : ↥(f.range.comap φ) →* L ⧸ Subgroup.center L :=
    (QuotientGroup.mk' (Subgroup.center L)).comp θ₀
  have hθ : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp hθ₀
  let e : (↥(f.range.comap φ) ⧸ θ.ker) ≃* (L ⧸ Subgroup.center L) :=
    QuotientGroup.quotientKerEquivOfSurjective θ hθ
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.1
  have : IsSimpleGroup (↥(f.range.comap φ) ⧸ θ.ker) := e.isSimpleGroup
  have hnonab : ∃ a b : ↥(f.range.comap φ) ⧸ θ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL.2.2
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hlist := cl_lit_sqtk_simple_list_section Y hSQTK (f.range.comap φ) θ.ker hnonab
  exact CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e.symm hlist

theorem sqtkCharTwoOrAltNative_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SQTKCharTwoOrAltNative Y) : SQTKCharTwoOrAltNative X := by
  rcases h with ⟨n, h5, h8, ⟨e'⟩⟩ | h | h | h | h | h
  · exact Or.inl ⟨n, h5, h8, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (CFSG.QuasithinUnique.Ch1.SQTKCharTwoLie.of_mulEquiv e h)))))

end CFSG.QuasithinUnique.Bridge.B113Det
