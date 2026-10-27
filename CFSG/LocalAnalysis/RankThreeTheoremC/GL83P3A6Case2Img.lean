module

public import CFSG.Open.LocalVocabulary

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Img

open CFSG.Open Subgroup

variable {G : Type} [Group G] {M O : Subgroup G} [(O.subgroupOf M).Normal]

variable (M O) in
def img (X : Subgroup G) : Subgroup (M ⧸ O.subgroupOf M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (O.subgroupOf M))

theorem mem_img_iff {X : Subgroup G} {z : M ⧸ O.subgroupOf M} :
    z ∈ img M O X ↔ ∃ g ∈ X, ∃ hg : g ∈ M, (QuotientGroup.mk ⟨g, hg⟩ : M ⧸ O.subgroupOf M) = z := by
  unfold img
  simp only [mem_map, mem_subgroupOf, QuotientGroup.mk'_apply]
  constructor
  · rintro ⟨⟨g, hgM⟩, hgX, rfl⟩
    exact ⟨g, hgX, hgM, rfl⟩
  · rintro ⟨g, hgX, hgM, rfl⟩
    exact ⟨⟨g, hgM⟩, hgX, rfl⟩

theorem mk_mem_img {X : Subgroup G} {g : G} (hgX : g ∈ X) (hgM : g ∈ M) :
    (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M) ∈ img M O X :=
  mem_img_iff.mpr ⟨g, hgX, hgM, rfl⟩

theorem img_mono {X Y : Subgroup G} (h : X ≤ Y) : img M O X ≤ img M O Y := by
  intro z hz
  obtain ⟨g, hg, hgM, rfl⟩ := mem_img_iff.mp hz
  exact mk_mem_img (h hg) hgM

theorem mk_eq_iff {g h : G} (hg : g ∈ M) (hh : h ∈ M) :
    (QuotientGroup.mk ⟨g, hg⟩ : M ⧸ O.subgroupOf M) = QuotientGroup.mk ⟨h, hh⟩ ↔
      g⁻¹ * h ∈ O := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem mk_eq_one_iff {g : G} (hg : g ∈ M) :
    (QuotientGroup.mk ⟨g, hg⟩ : M ⧸ O.subgroupOf M) = 1 ↔ g ∈ O := by
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem exists_mk (z : M ⧸ O.subgroupOf M) :
    ∃ g : G, ∃ hg : g ∈ M, (QuotientGroup.mk ⟨g, hg⟩ : M ⧸ O.subgroupOf M) = z := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨g, hg, rfl⟩

theorem isPGroup_img {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) : IsPGroup p (img M O X) :=
  (hX.comap_subtype (K := M)).map _

theorem isElemAbelian_img {p : ℕ} {X : Subgroup G} (hX : IsElemAbelian p X) :
    IsElemAbelian p (img M O X) := by
  haveI := hX.1
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_, fun z hz => ?_⟩
  · obtain ⟨g, hg, hgM, rfl⟩ := mem_img_iff.mp ha
    obtain ⟨h, hh, hhM, rfl⟩ := mem_img_iff.mp hb
    show (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M) * QuotientGroup.mk ⟨h, hhM⟩ =
      QuotientGroup.mk ⟨h, hhM⟩ * QuotientGroup.mk ⟨g, hgM⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (setLike_mul_comm hg hh)
  · obtain ⟨g, hg, hgM, rfl⟩ := mem_img_iff.mp hz
    rw [← QuotientGroup.mk_pow]
    have : (⟨g, hgM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hX.2 g hg)
    rw [this]
    rfl

theorem img_le_normalizer {U Y : Subgroup G} (h : U ≤ normalizer (Y : Set G)) :
    img M O U ≤ normalizer ((img M O Y : Subgroup (M ⧸ O.subgroupOf M)) : Set _) := by
  have fwd : ∀ g (hgM : g ∈ M), g ∈ normalizer (Y : Set G) → ∀ w ∈ img M O Y,
      (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M) * w *
        (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M)⁻¹ ∈ img M O Y := by
    intro g hgM hgn w hw
    obtain ⟨y, hy, hyM, rfl⟩ := mem_img_iff.mp hw
    refine mem_img_iff.mpr ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hgn y).mp hy,
      M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM), ?_⟩
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  intro z hz
  obtain ⟨g, hg, hgM, rfl⟩ := mem_img_iff.mp hz
  have hgn := h hg
  refine mem_normalizer_iff.mpr fun w => ⟨fwd g hgM hgn w, fun hw => ?_⟩
  have h2 := fwd g⁻¹ (M.inv_mem hgM) ((normalizer (Y : Set G)).inv_mem hgn) _ hw
  have e : (QuotientGroup.mk ⟨g⁻¹, M.inv_mem hgM⟩ : M ⧸ O.subgroupOf M) =
      (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M)⁻¹ := by
    rw [← QuotientGroup.mk_inv]
    rfl
  rw [e] at h2
  have e2 : ∀ a b : M ⧸ O.subgroupOf M, a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := fun a b => by group
  rwa [e2] at h2

theorem img_conj {X : Subgroup G} {g : G} (hg : g ∈ M) :
    img M O (X.map (MulAut.conj g).toMonoidHom) =
      (img M O X).map
        (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : M ⧸ O.subgroupOf M)).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨y', hy', hy'M, rfl⟩ := mem_img_iff.mp hz
    obtain ⟨y, hyX, rfl⟩ := hy'
    have hyM : y ∈ M := by
      have : g⁻¹ * (g * y * g⁻¹) * g ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem hg) hy'M) hg
      simpa [mul_assoc] using this
    refine ⟨QuotientGroup.mk ⟨y, hyM⟩, mk_mem_img hyX hyM, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hyX, hyM, rfl⟩ := mem_img_iff.mp hw
    refine mem_img_iff.mpr ⟨g * y * g⁻¹, ⟨y, hyX, rfl⟩,
      M.mul_mem (M.mul_mem hg hyM) (M.inv_mem hg), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem card_img {X : Subgroup G} (hXM : X ≤ M) :
    Nat.card (img M O X) = (X ⊓ O).relIndex X := by
  set φ : ↥(X.subgroupOf M) →* M ⧸ O.subgroupOf M :=
    (QuotientGroup.mk' (O.subgroupOf M)).comp (X.subgroupOf M).subtype with hφ
  have hrange : φ.range = img M O X := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : φ.ker = (O.subgroupOf M).subgroupOf (X.subgroupOf M) := by
    ext k
    simp only [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.subtype_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have h1 := Subgroup.index_ker φ
  rw [hrange] at h1
  rw [← h1, hker]
  change ((O.subgroupOf M).relIndex (X.subgroupOf M)) = _
  rw [Subgroup.relIndex_subgroupOf hXM, ← Subgroup.inf_relIndex_right, inf_comm]

theorem card_img_of_inf {X : Subgroup G} (hXM : X ≤ M) (hXO : X ⊓ O = ⊥) :
    Nat.card (img M O X) = Nat.card X := by
  rw [card_img hXM, hXO, Subgroup.relIndex_bot_left]

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Img
