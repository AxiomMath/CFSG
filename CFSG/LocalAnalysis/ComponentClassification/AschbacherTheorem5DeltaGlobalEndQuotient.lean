module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

namespace SubQuot

variable {Q : Type*} [Group Q] (Y₀ N : Subgroup Q) [(N.subgroupOf Y₀).Normal]

@[expose] def proj : Y₀ →* Y₀ ⧸ N.subgroupOf Y₀ := QuotientGroup.mk' _

@[expose] def img (P : Subgroup Q) : Subgroup (Y₀ ⧸ N.subgroupOf Y₀) :=
  (P.subgroupOf Y₀).map (proj Y₀ N)

variable {Y₀ N}

theorem proj_surjective : Function.Surjective (proj Y₀ N) := QuotientGroup.mk'_surjective _

theorem proj_eq_one_iff (x : Y₀) : proj Y₀ N x = 1 ↔ (x : Q) ∈ N := by
  rw [proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem proj_eq_proj_iff (x y : Y₀) : proj Y₀ N x = proj Y₀ N y ↔ (x : Q)⁻¹ * y ∈ N := by
  rw [proj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simp

theorem mem_img {P : Subgroup Q} {y : Y₀ ⧸ N.subgroupOf Y₀} :
    y ∈ img Y₀ N P ↔ ∃ x : Y₀, (x : Q) ∈ P ∧ proj Y₀ N x = y := by
  rw [img, Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem proj_mem_img {P : Subgroup Q} {x : Y₀} (hx : (x : Q) ∈ P) : proj Y₀ N x ∈ img Y₀ N P :=
  mem_img.mpr ⟨x, hx, rfl⟩

theorem img_mono {P P' : Subgroup Q} (h : P ≤ P') : img Y₀ N P ≤ img Y₀ N P' :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem img_self : img Y₀ N Y₀ = ⊤ := by
  rw [img, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact proj_surjective

theorem img_eq_bot {P : Subgroup Q} (hP : P ≤ N) : img Y₀ N P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_img.mp hy
  rw [Subgroup.mem_bot, proj_eq_one_iff]
  exact hP hx

theorem img_sup {P P' : Subgroup Q} (hP : P ≤ Y₀) (hP' : P' ≤ Y₀) :
    img Y₀ N (P ⊔ P') = img Y₀ N P ⊔ img Y₀ N P' := by
  rw [img, img, img, Subgroup.subgroupOf_sup hP hP', Subgroup.map_sup]

theorem img_iSup {ι : Sort*} (P : ι → Subgroup Q) (hP : ∀ i, P i ≤ Y₀) :
    img Y₀ N (⨆ i, P i) = ⨆ i, img Y₀ N (P i) := by
  have hsub : (⨆ i, P i).subgroupOf Y₀ = ⨆ i, (P i).subgroupOf Y₀ := by
    have h1 : (⨆ i, P i) = (⨆ i, (P i).subgroupOf Y₀).map Y₀.subtype := by
      rw [Subgroup.map_iSup]
      congr 1
      funext i
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hP i)]
    rw [h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y₀.subtype_injective]
  rw [img, hsub, Subgroup.map_iSup]
  rfl

theorem le_sup_of_img_le {P P' : Subgroup Q} (hP : P ≤ Y₀) (h : img Y₀ N P ≤ img Y₀ N P') :
    P ≤ P' ⊔ N := by
  intro p hp
  obtain ⟨x, hx, hxp⟩ := mem_img.mp (h (proj_mem_img (x := ⟨p, hP hp⟩) hp))
  have hmem := (proj_eq_proj_iff x ⟨p, hP hp⟩).mp hxp
  have heq : p = (x : Q) * ((x : Q)⁻¹ * p) := by group
  rw [heq]
  exact Subgroup.mul_mem_sup hx hmem

theorem img_rightConjugate (P : Subgroup Q) (c : Y₀) :
    img Y₀ N (rightConjugate P (c : Q)) = rightConjugate (img Y₀ N P) (proj Y₀ N c) := by
  ext y
  rw [mem_img, mem_rightConjugate_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rightConjugate_iff] at hx
    rw [← map_mul, ← map_inv, ← map_mul]
    exact proj_mem_img (x := c * x * c⁻¹) (by simpa using hx)
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_img.mp hy
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx
    · rw [map_mul, map_mul, map_inv, hxy]
      group

theorem img_normal {P : Subgroup Q} (hP : P ≤ Y₀) (hn : Y₀ ≤ Subgroup.normalizer (P : Set Q)) :
    (img Y₀ N P).Normal := by
  have : (P.subgroupOf Y₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP).mpr hn
  exact this.map _ proj_surjective

theorem img_le_normalizer {P R : Subgroup Q} (hRP : R ⊓ Y₀ ≤ Subgroup.normalizer (P : Set Q)) :
    img Y₀ N R ≤ Subgroup.normalizer (img Y₀ N P : Set (Y₀ ⧸ N.subgroupOf Y₀)) := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := mem_img.mp hy
  rw [← rightConjugate_eq_self_iff, ← img_rightConjugate,
    (rightConjugate_eq_self_iff P (c : Q)).mpr (hRP ⟨hc, c.2⟩)]

theorem card_img_mul [Finite Q] {P : Subgroup Q} (hP : P ≤ Y₀) :
    Nat.card (img Y₀ N P) * Nat.card (P ⊓ N : Subgroup Q) = Nat.card P := by
  set K := P.subgroupOf Y₀
  set f := (proj Y₀ N).domRestrict K
  have h1 := Subgroup.index_ker f
  have h2 := Subgroup.card_mul_index f.ker
  rw [MonoidHom.domRestrict_range] at h1
  have hker : (proj Y₀ N).ker = N.subgroupOf Y₀ := by
    ext x
    rw [MonoidHom.mem_ker, proj_eq_one_iff, Subgroup.mem_subgroupOf]
  have hinf : N.subgroupOf Y₀ ⊓ K = (N ⊓ P).subgroupOf Y₀ := by
    ext x
    simp [K, Subgroup.mem_subgroupOf]
  have hcardker : Nat.card f.ker = Nat.card (P ⊓ N : Subgroup Q) := by
    rw [MonoidHom.ker_domRestrict, hker, SectionSix.card_subgroupOf, hinf,
      SectionSix.card_subgroupOf, inf_eq_left.mpr (inf_le_right.trans hP), inf_comm]
  have hK : Nat.card K = Nat.card P := by
    rw [SectionSix.card_subgroupOf, inf_eq_left.mpr hP]
  rw [← hK, ← h2, h1, hcardker, mul_comm]
  rfl

end SubQuot

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
