module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129Syl
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_g_conj_z [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) : g⁻¹ * z * g = z := by
  have h := sec10D_g_comm_z hz2 hctx
  calc g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
    _ = g⁻¹ * (g * z) := by rw [h]
    _ = z := by group

theorem sec10C_g_sq_comm_t [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) :
    (g * g)⁻¹ * t * (g * g) = t := by
  have hgz := sec10C_g_conj_z hz2 hctx
  have h1 : g⁻¹ * (t * z) * g = t := by
    calc g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
      _ = (t * z) * z := by rw [hctx.swap, hgz]
      _ = t := by rw [mul_assoc, hz2, mul_one]
  calc (g * g)⁻¹ * t * (g * g) = g⁻¹ * (g⁻¹ * t * g) * g := by group
    _ = g⁻¹ * (t * z) * g := by rw [hctx.swap]
    _ = t := h1

theorem sec10C_g_sq_mem_S [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) : g * g ∈ S := by
  have hgT : g ∈ S ⊔ zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hcomm : (g * g)⁻¹ * t * (g * g) = t := sec10C_g_sq_comm_t hz2 hctx
  have hC : g * g ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * g * t = (g * g) * ((g * g)⁻¹ * t * (g * g)) := by rw [hcomm]
      _ = t * (g * g) := by group
  rw [← sec10D_T_cent_t hctx]
  exact ⟨(S ⊔ zpowers g).mul_mem hgT hgT, hC⟩

theorem sec10C_g_conj_t' [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) : g * t * g⁻¹ = t * z := by
  have hsq := sec10C_g_sq_mem_S hz2 hctx
  have h2 : (g * g) * z = z * (g * g) := hctx.central _ hsq
  have hcomm : (g * g)⁻¹ * t * (g * g) = t := sec10C_g_sq_comm_t hz2 hctx
  calc g * t * g⁻¹ = (g * g) * (g⁻¹ * t * g) * (g * g)⁻¹ := by group
    _ = (g * g) * (t * z) * (g * g)⁻¹ := by rw [hctx.swap]
    _ = ((g * g) * t * (g * g)⁻¹) * ((g * g) * z * (g * g)⁻¹) := by group
    _ = t * z := by
      have ht' : (g * g) * t * (g * g)⁻¹ = t := by
        have := congrArg (fun x => (g * g) * x * (g * g)⁻¹) hcomm
        simpa [mul_assoc] using this.symm
      have hz'' : (g * g) * z * (g * g)⁻¹ = z := by
        rw [h2, mul_assoc, mul_inv_cancel, mul_one]
      rw [ht', hz'']

theorem sec10C_mem_T [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (hctx : Sec109Ctx G t L S z K1 K2 g) {x : G}
    (hx : x ∈ S ⊔ zpowers g) : x ∈ S ∨ ∃ y ∈ S, x = y * g := by
  have hsq := sec10C_g_sq_mem_S hz2 hctx
  have hgN : ∀ y ∈ S, g * y * g⁻¹ ∈ S := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hctx.norm y).mp hy
  let U : Subgroup G :=
    { carrier := {x | x ∈ S ∨ ∃ y ∈ S, x = y * g}
      one_mem' := Or.inl S.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨y₁, hy₁, rfl⟩) (hb | ⟨y₂, hy₂, rfl⟩)
        · exact Or.inl (S.mul_mem ha hb)
        · exact Or.inr ⟨a * y₂, S.mul_mem ha hy₂, by rw [mul_assoc]⟩
        · refine Or.inr ⟨y₁ * (g * b * g⁻¹), S.mul_mem hy₁ (hgN b hb), by group⟩
        · refine Or.inl ?_
          have : y₁ * g * (y₂ * g) = y₁ * (g * y₂ * g⁻¹) * (g * g) := by group
          rw [this]
          exact S.mul_mem (S.mul_mem hy₁ (hgN y₂ hy₂)) hsq
      inv_mem' := by
        rintro a (ha | ⟨y, hy, rfl⟩)
        · exact Or.inl (S.inv_mem ha)
        · refine Or.inr ⟨(g * g)⁻¹ * (g * y⁻¹ * g⁻¹), S.mul_mem (S.inv_mem hsq)
            (hgN _ (S.inv_mem hy)), by group⟩ }
  have hle : S ⊔ zpowers g ≤ U := by
    refine sup_le (fun x hx => Or.inl hx) (Subgroup.zpowers_le.mpr ?_)
    exact Or.inr ⟨1, S.one_mem, by rw [one_mul]⟩
  exact hle hx

theorem sec10C_isNormalE32In_conjugate {S X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (S : Set G)) (hX : IsNormalE32In S X) :
    IsNormalE32In S (CFSG.conjugate X g) := by
  obtain ⟨hXS, hXe, hXn⟩ := hX
  have hgN : ∀ y, y ∈ S ↔ g * y * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hg
  have hXn' := (Subgroup.normal_subgroupOf_iff hXS).mp hXn
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · have h1 : g * x * g⁻¹ ∈ X := mem_conjugate_iff'.mp hx
    exact (hgN x).mpr (hXS h1)
  · unfold CFSG.conjugate
    refine ⟨CFSG.Open.IsElemAbelian.map hXe.1 (MulAut.conj g⁻¹).toMonoidHom, ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hXe.2
  · have hle : CFSG.conjugate X g ≤ S := fun x hx => by
      have h1 : g * x * g⁻¹ ∈ X := mem_conjugate_iff'.mp hx
      exact (hgN x).mpr (hXS h1)
    refine (Subgroup.normal_subgroupOf_iff hle).mpr fun h k hh hk => ?_
    have h1 : g * h * g⁻¹ ∈ X := mem_conjugate_iff'.mp hh
    have h2 : g * k * g⁻¹ ∈ S := (hgN k).mp hk
    have h3 := hXn' _ _ h1 h2
    rw [mem_conjugate_iff']
    have e : g * (k * h * k⁻¹) * g⁻¹ = (g * k * g⁻¹) * (g * h * g⁻¹) * (g * k * g⁻¹)⁻¹ := by group
    rw [e]
    exact h3

theorem sec10C_exists_A2 [Finite G] (h107c : Asc82Lemma107c) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) :
    ∃ r ∈ S, orderOf r = 2 ∧ InducesTypeSome L r 5 1 4 (-1) ∧
      secA2 t r K1 K2 ≠ secA t S L ∧
      (∀ X : Subgroup G, IsNormalE32In S X ↔ (X = secA t S L ∨ X = secA2 t r K1 K2)) ∧
      CFSG.conjugate (secA t S L) g = secA2 t r K1 K2 := by
  rcases h107c G t L S z K1 K2 hctx.toSec10Ctx with hJ | ⟨r, hrS, hr2, hrty, hne, hX⟩
  · exfalso
    apply hctx.not_M
    show g ∈ normalizer (secA t S L : Set G)
    rw [hJ]
    exact sec12_mem_normalizer_jElem hctx.norm
  · refine ⟨r, hrS, hr2, hrty, hne, hX, ?_⟩
    have hA : IsNormalE32In S (secA t S L) := (hX _).mpr (Or.inl rfl)
    have hAg := sec10C_isNormalE32In_conjugate hctx.norm hA
    rcases (hX _).mp hAg with h | h
    · exfalso
      apply hctx.not_M
      show g ∈ normalizer (secA t S L : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have : y ∈ CFSG.conjugate (secA t S L) g := by rw [h]; exact hy
        exact mem_conjugate_iff'.mp this
      · intro hy
        have : y ∈ CFSG.conjugate (secA t S L) g := mem_conjugate_iff'.mpr hy
        rwa [h] at this
    · exact h

end CFSG.OddStandard.SmallF3.Omega
