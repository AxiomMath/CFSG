module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G] (H D : Subgroup G) [hDn : (D.subgroupOf H).Normal]

abbrev QA : Type := ↥H ⧸ D.subgroupOf H

@[expose] def qmk : ↥H →* QA H D := QuotientGroup.mk' (D.subgroupOf H)

@[expose] def img (U : Subgroup G) : Subgroup (QA H D) := (U.subgroupOf H).map (qmk H D)

@[expose] def pre (T : Subgroup (QA H D)) : Subgroup G := (T.comap (qmk H D)).map H.subtype

variable {H D}

theorem qmk_surjective : Function.Surjective (qmk H D) := QuotientGroup.mk'_surjective _

theorem qmk_eq_one_iff {h : ↥H} : qmk H D h = 1 ↔ (h : G) ∈ D := by
  show QuotientGroup.mk' (D.subgroupOf H) h = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl

theorem qmk_eq_iff {a b : ↥H} : qmk H D a = qmk H D b ↔ (a : G)⁻¹ * b ∈ D := by
  show QuotientGroup.mk' (D.subgroupOf H) a = QuotientGroup.mk' (D.subgroupOf H) b ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rfl

theorem mem_img {U : Subgroup G} {a : QA H D} :
    a ∈ img H D U ↔ ∃ h : ↥H, (h : G) ∈ U ∧ qmk H D h = a := by
  unfold img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem mem_pre {T : Subgroup (QA H D)} {g : G} :
    g ∈ pre H D T ↔ ∃ h : ↥H, (h : G) = g ∧ qmk H D h ∈ T := by
  unfold pre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, rfl, hh⟩
  · rintro ⟨h, rfl, hh⟩
    exact ⟨h, hh, rfl⟩

theorem pre_le (T : Subgroup (QA H D)) : pre H D T ≤ H := by
  intro g hg
  obtain ⟨h, rfl, -⟩ := mem_pre.mp hg
  exact h.2

theorem D_le_pre (hDH : D ≤ H) (T : Subgroup (QA H D)) : D ≤ pre H D T := by
  intro d hd
  refine mem_pre.mpr ⟨⟨d, hDH hd⟩, rfl, ?_⟩
  rw [qmk_eq_one_iff.mpr hd]
  exact T.one_mem

theorem img_pre (T : Subgroup (QA H D)) : img H D (pre H D T) = T := by
  ext a
  rw [mem_img]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h', hh', hmem⟩ := mem_pre.mp hh
    have : h' = h := Subtype.ext hh'
    rw [← this]
    exact hmem
  · intro ha
    obtain ⟨h, rfl⟩ := qmk_surjective a
    exact ⟨h, mem_pre.mpr ⟨h, rfl, ha⟩, rfl⟩

theorem mem_pre_img {U : Subgroup G} (hDU : D ≤ U) {g : G} :
    g ∈ pre H D (img H D U) ↔ g ∈ U ∧ g ∈ H := by
  rw [mem_pre]
  constructor
  · rintro ⟨h, rfl, hh⟩
    obtain ⟨u, hu, hqu⟩ := mem_img.mp hh
    have hd : (u : G)⁻¹ * h ∈ D := qmk_eq_iff.mp hqu
    have : (h : G) = u * ((u : G)⁻¹ * h) := by group
    refine ⟨?_, h.2⟩
    rw [this]
    exact U.mul_mem hu (hDU hd)
  · rintro ⟨hgU, hgH⟩
    exact ⟨⟨g, hgH⟩, rfl, mem_img.mpr ⟨⟨g, hgH⟩, hgU, rfl⟩⟩

theorem mem_normalizer_pre {a : ↥H} {T : Subgroup (QA H D)}
    (ha : qmk H D a ∈ normalizer (T : Set (QA H D))) :
    (a : G) ∈ normalizer ((pre H D T : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at ha ⊢
  intro g
  constructor
  · intro hg
    obtain ⟨h, rfl, hh⟩ := mem_pre.mp hg
    refine mem_pre.mpr ⟨a * h * a⁻¹, by simp, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact (ha _).mp hh
  · intro hg
    obtain ⟨h', hh', hmem⟩ := mem_pre.mp hg
    refine mem_pre.mpr ⟨a⁻¹ * h' * a, ?_, ?_⟩
    · have e : ((a⁻¹ * h' * a : ↥H) : G) = (a : G)⁻¹ * (h' : G) * a := rfl
      rw [e, hh']
      group
    · rw [map_mul, map_mul, map_inv]
      have := (ha ((qmk H D a)⁻¹ * qmk H D h' * qmk H D a)).mpr (by
        have e : qmk H D a * ((qmk H D a)⁻¹ * qmk H D h' * qmk H D a) * (qmk H D a)⁻¹ =
          qmk H D h' := by group
        rw [e]
        exact hmem)
      exact this

theorem qmk_mem_normalizer_img {U : Subgroup G} {a : ↥H}
    (ha : (a : G) ∈ normalizer (U : Set G)) :
    qmk H D a ∈ normalizer ((img H D U : Subgroup (QA H D)) : Set (QA H D)) := by
  have ha' := mem_normalizer_iff.mp ha
  rw [mem_normalizer_iff]
  intro x
  obtain ⟨g, rfl⟩ := qmk_surjective x
  constructor
  · intro hx
    obtain ⟨u, hu, hqu⟩ := mem_img.mp hx
    refine mem_img.mpr ⟨a * u * a⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (ha' _).mp hu
    · rw [map_mul, map_mul, map_inv, hqu]
  · intro hx
    obtain ⟨u, hu, hqu⟩ := mem_img.mp hx
    refine mem_img.mpr ⟨a⁻¹ * u * a, ?_, ?_⟩
    · have hu' := (ha' ((a : G)⁻¹ * u * a)).mpr (by
        have e : (a : G) * ((a : G)⁻¹ * u * a) * (a : G)⁻¹ = u := by group
        rw [e]
        exact hu)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hu'
    · rw [map_mul, map_mul, map_inv, hqu]
      group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC
