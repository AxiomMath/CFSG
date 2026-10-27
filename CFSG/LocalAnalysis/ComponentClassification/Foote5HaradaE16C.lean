module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HaradaE16B
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ComponentClassification.Foote5

open Subgroup

variable {S : Type*} [Group S]

theorem harE16_mem_map_conj {T : Subgroup S} {t y : S} :
    y ∈ T.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ T := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem harE16_map_conj_comm {T : Subgroup S} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {t : S} :
    ∀ a ∈ T.map (MulAut.conj t).toMonoidHom, ∀ b ∈ T.map (MulAut.conj t).toMonoidHom,
      a * b = b * a := by
  intro a ha b hb
  have h1 := hTab _ (harE16_mem_map_conj.mp ha) _ (harE16_mem_map_conj.mp hb)
  calc a * b = t * ((t⁻¹ * a * t) * (t⁻¹ * b * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * b * t) * (t⁻¹ * a * t)) * t⁻¹ := by rw [h1]
    _ = b * a := by group

theorem harE16_map_conj_sq {T : Subgroup S} (hTsq : ∀ a ∈ T, a * a = 1) {t : S} :
    ∀ y ∈ T.map (MulAut.conj t).toMonoidHom, y * y = 1 := by
  intro y hy
  have h1 := hTsq _ (harE16_mem_map_conj.mp hy)
  calc y * y = t * ((t⁻¹ * y * t) * (t⁻¹ * y * t)) * t⁻¹ := by group
    _ = 1 := by rw [h1]; group

variable [Finite S]

theorem harE16_card_inf_conj_le {T U : Subgroup S} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hT16 : Nat.card T = 16) (hUT : U ≤ T) (hU4 : Nat.card U = 4)
    (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T) {t : S}
    (htR : t ∉ normalizer (T : Set S)) :
    Nat.card ↥(T ⊓ T.map (MulAut.conj t).toMonoidHom) ≤ 4 := by
  refine harE16_card_le_four hT16 hUT hU4 inf_le_left fun u hu huU => ?_
  by_contra hu1
  apply htR
  have hle : T.map (MulAut.conj t).toMonoidHom ≤ T := fun y hy =>
    hcent u huU hu1 y (harE16_map_conj_comm hTab y hy u (mem_inf.mp hu).2)
  have heq : T.map (MulAut.conj t).toMonoidHom = T := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj t).injective])
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    apply hle
    rw [harE16_mem_map_conj]
    simpa [mul_assoc] using hn
  · intro hn
    rw [← heq, harE16_mem_map_conj] at hn
    simpa [mul_assoc] using hn

theorem harE16_mem_or_mem_conj {T U : Subgroup S} (hS : IsPGroup 2 S)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTsq : ∀ a ∈ T, a * a = 1)
    (hT16 : Nat.card T = 16) (hUT : U ≤ T) (hU4 : Nat.card U = 4)
    (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T) {t : S}
    (htN : t ∈ normalizer ((normalizer (T : Set S) : Subgroup S) : Set S))
    (htR : t ∉ normalizer (T : Set S)) {r : S} (hr : r ∈ normalizer (T : Set S))
    (hr2 : r * r = 1) : r ∈ T ∨ r ∈ T.map (MulAut.conj t).toMonoidHom := by
  have hTR : T ≤ normalizer (T : Set S) := le_normalizer
  have hT₁R : T.map (MulAut.conj t).toMonoidHom ≤ normalizer (T : Set S) := fun y hy => by
    have h1 := (mem_normalizer_iff.mp htN (t⁻¹ * y * t)).mp (hTR (harE16_mem_map_conj.mp hy))
    simpa [mul_assoc] using h1
  have hT₁16 : Nat.card (T.map (MulAut.conj t).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.conj t).injective, hT16]
  have hZ4 := harE16_card_inf_conj_le hTab hT16 hUT hU4 hcent htR
  have hR64 := harE16_card_normalizer_le hS hTab hTsq hT16 hUT hU4 hcent
  have hKI := harE16_card_mul_card_le hTR hT₁R
  rw [hT16, hT₁16] at hKI
  have hZge : 4 ≤ Nat.card ↥(T ⊓ T.map (MulAut.conj t).toMonoidHom) := by nlinarith
  have hcomm₁ : ∀ y ∈ T.map (MulAut.conj t).toMonoidHom, y ∉ T → ∀ x ∈ T, x * y = y * x →
      x ∈ T.map (MulAut.conj t).toMonoidHom := by
    intro y hy hyT x hx hxy
    have hD4 : Nat.card ↥(T ⊓ centralizer {y}) ≤ 4 :=
      harE16_card_le_four hT16 hUT hU4 inf_le_left fun u hu huU =>
        harE16_eq_one_of_commute hcent hyT huU
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2).symm
    have hZD : T ⊓ T.map (MulAut.conj t).toMonoidHom ≤ T ⊓ centralizer {y} := fun z hz =>
      mem_inf.mpr ⟨(mem_inf.mp hz).1, mem_centralizer_singleton_iff.mpr
        (harE16_map_conj_comm hTab z (mem_inf.mp hz).2 y hy)⟩
    have hDZ := eq_of_le_of_card_ge hZD (by omega)
    have hxD : x ∈ T ⊓ centralizer {y} := mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr hxy⟩
    rw [← hDZ] at hxD
    exact (mem_inf.mp hxD).2
  obtain ⟨y, hy, hyr⟩ := harE16_exists_mem_mul hTR hT₁R le_rfl
    (by rw [hT16, hT₁16]; exact (Nat.mul_le_mul hR64 hZ4).trans (by norm_num)) hr
  by_cases hyT : y ∈ T
  · left
    simpa using T.mul_mem hyT hyr
  · right
    obtain ⟨x, hxT, rfl⟩ : ∃ x ∈ T, r = y * x := ⟨y⁻¹ * r, hyr, by group⟩
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hTsq x hxT)
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (harE16_map_conj_sq hTsq y hy)
    have h2 : (y * x)⁻¹ = y * x := inv_eq_of_mul_eq_one_right hr2
    rw [mul_inv_rev, hxinv, hyinv] at h2
    exact (T.map (MulAut.conj t).toMonoidHom).mul_mem hy (hcomm₁ y hy hyT x hxT h2)

theorem harE16_no_normal_e8 {T U : Subgroup S} (hS : IsPGroup 2 S)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTsq : ∀ a ∈ T, a * a = 1)
    (hT16 : Nat.card T = 16) (hUT : U ≤ T) (hU4 : Nat.card U = 4)
    (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T)
    (hlt : normalizer (T : Set S) ≠ ⊤) :
    ∀ E : Subgroup S, E.Normal → Open.IsElemAbelian 2 E → Nat.card E ≠ 8 := by
  intro A hAn hA hA8
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  have hTR : T ≤ normalizer (T : Set S) := le_normalizer
  by_cases hAR : A ≤ normalizer (T : Set S)
  · obtain ⟨t, -, htR, htN⟩ :=
      harE16_exists_mem_normalizer (le_top : normalizer (T : Set S) ≤ ⊤) (hS.to_subgroup ⊤) hlt
    have hcover : ∀ a ∈ A, a ∈ T ∨ a ∈ T.map (MulAut.conj t).toMonoidHom := fun a ha =>
      harE16_mem_or_mem_conj hS hTab hTsq hT16 hUT hU4 hcent htN htR (hAR ha) (hAsq a ha)
    have hAT : A ≤ T := by
      rcases harE16_le_or_le hcover with hAT | hAT₁
      · exact hAT
      · intro a ha
        have h1 := hAT₁ (hAn.conj_mem a ha t)
        rw [harE16_mem_map_conj] at h1
        simpa [mul_assoc] using h1
    have hAZ : A ≤ T ⊓ T.map (MulAut.conj t).toMonoidHom := fun a ha =>
      mem_inf.mpr ⟨hAT ha, harE16_mem_map_conj.mpr (hAT (by simpa using hAn.conj_mem a ha t⁻¹))⟩
    have h1 := card_le_of_le hAZ
    have h2 := harE16_card_inf_conj_le hTab hT16 hUT hU4 hcent htR
    omega
  · obtain ⟨a₀, ha₀A, ha₀R⟩ := IsConcreteLE.not_le_iff_exists.mp hAR
    have hne : normalizer (T : Set S) ≠ A ⊔ normalizer (T : Set S) := fun h =>
      ha₀R (h ▸ mem_sup_left ha₀A)
    obtain ⟨g, hg, hgR, hgN⟩ := harE16_exists_mem_normalizer le_sup_right (hS.to_subgroup _) hne
    have : A.Normal := hAn
    obtain ⟨a, haA, r, hrR, rfl⟩ := mem_sup_of_normal_left.mp hg
    have haN : a ∈ normalizer ((normalizer (T : Set S) : Subgroup S) : Set S) := by
      have h1 := (normalizer _).mul_mem hgN ((normalizer _).inv_mem (le_normalizer hrR))
      simpa using h1
    have haR : a ∉ normalizer (T : Set S) := fun h => hgR ((normalizer _).mul_mem h hrR)
    have hcover : ∀ x ∈ T, x ∈ (T ⊓ T.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom ∨ x ∈ T ⊓ T.map (MulAut.conj a).toMonoidHom := by
      intro x hx
      have hcA : a * x * a⁻¹ * x⁻¹ ∈ A := by
        have h1 := A.mul_mem haA (hAn.conj_mem a⁻¹ (A.inv_mem haA) x)
        simpa [mul_assoc] using h1
      have hxa : a * x * a⁻¹ ∈ normalizer (T : Set S) := (mem_normalizer_iff.mp haN x).mp (hTR hx)
      have hcR : a * x * a⁻¹ * x⁻¹ ∈ normalizer (T : Set S) :=
        (normalizer _).mul_mem hxa ((normalizer _).inv_mem (hTR hx))
      have hxT₁ : a * x * a⁻¹ ∈ T.map (MulAut.conj a).toMonoidHom := by
        rw [harE16_mem_map_conj]
        simpa [mul_assoc] using hx
      rcases harE16_mem_or_mem_conj hS hTab hTsq hT16 hUT hU4 hcent haN haR hcR (hAsq _ hcA)
        with hc | hc
      · left
        rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
        refine mem_inf.mpr ⟨?_, hxT₁⟩
        simpa using T.mul_mem hc hx
      · right
        refine mem_inf.mpr ⟨hx, ?_⟩
        rw [harE16_mem_map_conj] at hc ⊢
        have h1 := T.inv_mem (T.mul_mem (T.inv_mem hx) hc)
        convert h1 using 1
        group
    have h2 := harE16_card_inf_conj_le hTab hT16 hUT hU4 hcent haR
    rcases harE16_le_or_le hcover with h | h
    · have h1 := card_le_of_le h
      rw [card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
      omega
    · have h1 := card_le_of_le h
      omega

end CFSG.ComponentClassification.Foote5
