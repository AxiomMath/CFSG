module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Coord
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section A1

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Hyp.card_le_of_centralizes_conj
    (h : Hyp G A) (d : Datum A) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂) {s : G} (hs : IsConj d.t s) {D : Subgroup G}
    (hDs : ∀ x ∈ D, x * s = s * x) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDsq : ∀ x ∈ D, x * x = 1) : Nat.card ↥D ≤ 32 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hs
  have hP := d.P_isSylow_centralizer
  have hDp : IsPGroup 2 D := fun x => ⟨1, by
    have := hDsq x x.2
    rw [pow_one, pow_two]
    exact Subtype.ext this⟩
  have hE'p : IsPGroup 2 (D.map (MulAut.conj g⁻¹).toMonoidHom) := hDp.map _
  have hE'c : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({d.t} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    rw [mem_map_conj_iff, inv_inv] at hz
    have h1 := hDs _ hz
    rw [← hg] at h1
    calc z * d.t = g⁻¹ * (g * z * g⁻¹ * (g * d.t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d.t * g⁻¹ * (g * z * g⁻¹)) * g := by rw [h1]
      _ = d.t * z := by group
  obtain ⟨c, hc, hcP⟩ := exists_conj_le_of_isSylowOf hP hE'p hE'c
  have hle : D.map (MulAut.conj (c * g⁻¹)).toMonoidHom ≤ d.P := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : g⁻¹ * y * g ∈ D.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj_iff]
      simpa [mul_assoc] using hy
    have := hcP _ hy'
    have e : c * g⁻¹ * y * (c * g⁻¹)⁻¹ = c * (g⁻¹ * y * g) * c⁻¹ := by group
    simpa [MulAut.conj_apply, e] using this
  have hab := isElemAbelian_map_conj hDc hDsq (c * g⁻¹)
  have hE := isElemAbelian_of_forall_two hab.1 hab.2
  have := h.card_elem_le d hR hle hE
  rwa [card_map_conj] at this

end A1

section Prod

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem not_isConj_of_mem_prod
    {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4) (h : Hyp G A) (d : Datum A) {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂)
    {A₁ B₁ : Subgroup G} (hcomm : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) (hdisj : A₁ ⊓ B₁ = ⊥)
    (hsw₁ : ∀ x ∈ A₁, d.t * x * d.t⁻¹ ∈ B₁) (hsw₂ : ∀ x ∈ B₁, d.t * x * d.t⁻¹ ∈ A₁)
    (e : ↥A₁ ≃* ↥(unipAll k)) {s : G} (hs : s ∈ A₁ ⊔ B₁) : ¬ IsConj d.t s := by
  intro hconj
  have hs2 : s * s = 1 := d.mul_self_of_isConj hconj
  obtain ⟨D, -, hDs, hDc, hDsq, hDcard⟩ :=
    exists_rad256 hk d.t_mul_self hcomm hdisj hsw₁ hsw₂ e hs hs2
  have := h.card_le_of_centralizes_conj d hR hconj hDs hDc hDsq
  omega

end Prod

end CFSG.OddStandard.Seitz77
