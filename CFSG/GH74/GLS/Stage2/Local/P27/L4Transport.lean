module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup

variable {G : Type} [Group G]

theorem conj_cancel_left (c x : G) : c⁻¹ * (c * x * c⁻¹) * c = x := by group

abbrev cj (c : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj c).toMonoidHom

theorem mem_cj {c x : G} {H : Subgroup G} : x ∈ cj c H ↔ c⁻¹ * x * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    simpa [MulAut.conj_apply, e] using hy
  · intro h
    exact ⟨c⁻¹ * x * c, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem cj_mono {c : G} {H K : Subgroup G} (h : H ≤ K) : cj c H ≤ cj c K := Subgroup.map_mono h

theorem cj_cj_inv (c : G) (H : Subgroup G) : cj c⁻¹ (cj c H) = H := by
  ext x
  simp only [mem_cj]
  rw [inv_inv, conj_cancel_left]

theorem cj_sup (c : G) (H K : Subgroup G) : cj c (H ⊔ K) = cj c H ⊔ cj c K :=
  Subgroup.map_sup _ _ _

theorem cj_inf (c : G) (H K : Subgroup G) : cj c (H ⊓ K) = cj c H ⊓ cj c K :=
  Subgroup.map_inf H K _ (MulAut.conj c).injective

theorem cj_bot (c : G) : cj c (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem cj_zpowers (c a : G) : cj c (zpowers a) = zpowers (c * a * c⁻¹) := by
  show (zpowers a).map (MulAut.conj c).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem cj_commutator (c : G) (H K : Subgroup G) : cj c ⁅H, K⁆ = ⁅cj c H, cj c K⁆ :=
  Subgroup.map_commutator _ _ _

theorem cj_centralizer_singleton (c a : G) :
    cj c (centralizer ({a} : Set G)) = centralizer ({c * a * c⁻¹} : Set G) := by
  ext y
  rw [mem_cj, mem_centralizer_iff, mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have := congrArg (fun w => c * w * c⁻¹) h
    simpa [mul_assoc] using this
  · intro h
    have := congrArg (fun w => c⁻¹ * w * c) h
    simpa [mul_assoc] using this

theorem card_cj (c : G) (H : Subgroup G) : Nat.card ↥(cj c H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem relIndex_cj (c : G) (H K : Subgroup G) : (cj c H).relIndex (cj c K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj c).toMonoidHom) H K (MulAut.conj c).injective

theorem mem_center_map_iff {H : Subgroup G} {y : G} :
    y ∈ (center ↥H).map H.subtype ↔ y ∈ H ∧ ∀ a ∈ H, a * y = y * a := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun a ha => ?_⟩
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨a, ha⟩)
    simpa using this
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_center_iff.2 (fun a => Subtype.ext (h a a.2)), rfl⟩

theorem center_map_cj (c : G) (H : Subgroup G) :
    (center ↥(cj c H)).map (cj c H).subtype = cj c ((center ↥H).map H.subtype) := by
  ext y
  rw [mem_cj, mem_center_map_iff, mem_center_map_iff, mem_cj]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun a ha => ?_⟩
    have h1 := h (c * a * c⁻¹) (mem_cj.2 (by rw [conj_cancel_left]; exact ha))
    have h2 := congrArg (fun w => c⁻¹ * w * c) h1
    simpa [mul_assoc] using h2
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun a ha => ?_⟩
    have ha' : c⁻¹ * a * c ∈ H := mem_cj.1 ha
    have h1 := h _ ha'
    have h2 := congrArg (fun w => c * w * c⁻¹) h1
    simpa [mul_assoc] using h2

noncomputable def cjEquiv (c : G) (H : Subgroup G) : ↥H ≃* ↥(cj c H) :=
  (MulAut.conj c).subgroupMap H

theorem isCyclic_cj {c : G} {H : Subgroup G} (h : IsCyclic ↥H) : IsCyclic ↥(cj c H) :=
  isCyclic_of_surjective (cjEquiv c H).toMonoidHom (cjEquiv c H).surjective

theorem isDihedralOrder_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {m : ℕ}
    (h : IVK.IsDihedralOrder Y m) : IVK.IsDihedralOrder Y' m := by
  obtain ⟨k, hk, hk2, ⟨f⟩⟩ := h
  exact ⟨k, hk, hk2, ⟨e.symm.trans f⟩⟩

theorem isDihedralTwoGroup_cj {c : G} {H : Subgroup G} {n : ℕ} (h : IVK.IsDihedralTwoGroup ↥H n) :
    IVK.IsDihedralTwoGroup ↥(cj c H) n :=
  ⟨h.1, isDihedralOrder_of_mulEquiv (cjEquiv c H) h.2⟩

theorem isSylowOf_cj [Finite G] {c : G} {P K : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf 2 P K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (cj c P) (cj c K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨hPK, hP, hidx⟩ := h
  refine ⟨cj_mono hPK, ?_, ?_⟩
  · exact hP.of_equiv (cjEquiv c P)
  · rwa [relIndex_cj]

end CFSG.GH74.GLS.Stage2.Local.P27
