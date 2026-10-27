module

public import Mathlib.GroupTheory.Subgroup.Centralizer


public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary

variable {G : Type} [Group G]

theorem mem_normalizer {P : Subgroup G} (hP : P.Normal) (g : G) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hP]; trivial

@[expose] noncomputable def conjOnP (P : Subgroup G) (hP : P.Normal) : G →* MulAut P where
  toFun g := P.normalizerMonoidHom ⟨g, mem_normalizer hP g⟩
  map_one' := by
    have := P.normalizerMonoidHom.map_one
    exact this
  map_mul' g h := by
    exact P.normalizerMonoidHom.map_mul ⟨g, mem_normalizer hP g⟩ ⟨h, mem_normalizer hP h⟩

theorem conjOnP_apply (P : Subgroup G) (hP : P.Normal) (g : G) (x : P) :
    ((conjOnP P hP g x : P) : G) = g * (x : G) * g⁻¹ := by
  rfl

theorem image_eq (P : Subgroup G) (hP : P.Normal) (H : Subgroup G) :
    H.map (conjOnP P hP) =
      (H.subgroupOf (Subgroup.normalizer (P : Set G))).map P.normalizerMonoidHom := by
  ext u
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, mem_normalizer hP h⟩, hh, rfl⟩
  · rintro ⟨⟨h, hn⟩, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
