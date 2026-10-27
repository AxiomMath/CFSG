module

public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.RootWordBruhatCover
public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL

public section

open scoped CFSG.ConvolutionPoints

open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups.SeminaireExp3

namespace CFSG.LieType.AlgebraicGroups

theorem isDomainImage_pinnedXCurve {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k]
    (α : Fin τ.rank → ℤ) :
    SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' Set.range (pinnedX τ k α))) := by
  have hbc : ∀ z : Polynomial k →ₐ[k] k,
      z.comp (unitCo k (wordUnit τ (Polynomial k)
          (pinnedWord τ (Polynomial k) α Polynomial.X))) =
        (modGLPoint τ k (pinnedX τ k α (z Polynomial.X))).ofConv := fun z => by
    rw [comp_unitCo_wordUnit, mapWord_pinnedWord, wordUnit_pinnedWord]
    rfl
  refine ⟨Polynomial k, inferInstance, inferInstance, inferInstance, inferInstance,
    unitCo k (wordUnit τ (Polynomial k) (pinnedWord τ (Polynomial k) α Polynomial.X)), ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Polynomial.aeval c, ?_⟩
    show (Polynomial.aeval c).comp _ = _
    rw [hbc, Polynomial.aeval_X, pt_modGLZariski]
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨_, ⟨z Polynomial.X, rfl⟩, rfl⟩, by rw [pt_modGLZariski]; exact (hbc z).symm⟩

theorem isConnectedAlgebraicSubgroup_rootSpan {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k] (S : Set (Fin τ.rank → ℤ)) :
    IsConnectedAlgebraicSubgroup k ((rootSpan τ k S).map (modGLPoint τ k).toMonoidHom) := by
  let W : ↥S → Set (SeminaireExp3.ZariskiGL (Label τ) k) :=
    fun α => modGLZariski τ k '' Set.range (pinnedX τ k α.1)
  have hspan : rootSpan τ k S =
      Subgroup.closure (⋃ α : ↥S, Set.range (pinnedX τ k α.1)) := by
    rw [rootSpan, iSup_subtype']
    simp only [rootSubgroup, Subgroup.closure_iUnion]
  have hW : ∀ α : ↥S, SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' W α) := fun α => isDomainImage_pinnedXCurve α.1
  have h1 : ∀ α : ↥S, (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ W α :=
    fun α => ⟨1, ⟨0, pinnedX_zero τ k α.1⟩, map_one _⟩
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet W hW h1
  have hmap : (rootSpan τ k S).map (modGLZariski τ k).toMonoidHom =
      Subgroup.closure (⋃ α : ↥S, W α) := by
    rw [hspan, MonoidHom.map_closure]
    congr 1
    simp [W, Set.image_iUnion]
  have hdom : SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k) (rootSpan τ k S : Set (ModGL τ k))) := by
    have himg : modGLZariski τ k '' (rootSpan τ k S : Set (ModGL τ k)) =
        SeminaireExp3.ZariskiGL.wordSet W a := by
      rw [← ha, ← hmap, Subgroup.coe_map]
      rfl
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet W hW a
  exact (isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (rootSpan τ k S)
    hdom.isPointConstructible hdom.isPointIrreducible).2.1

end CFSG.LieType.AlgebraicGroups
