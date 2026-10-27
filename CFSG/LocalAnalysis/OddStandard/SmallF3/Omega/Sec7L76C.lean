module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76CH
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec76_exists_s [Finite G] (h36 : Asc82Lemma36) (h74 : Asc82Lemma74) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z) (hnc : ¬ IsConj t (t * z)) :
    ∃ g : G, g⁻¹ * t * g ∈ S ∧ g⁻¹ * t * g ≠ t ∧
      g⁻¹ * t * g ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ∧
      ∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 1 α := by
  obtain ⟨g₀, hC₀, hne₀⟩ := sec7_zstar hctx.simple hctx.nonabelian hctx.involution
  have hα₀ : ∃ α : ℤˣ, InducesTypeSome L (g₀⁻¹ * t * g₀) 6 1 1 α :=
    ((h74 G t L S z hctx).resolve_left hnc) (g₀⁻¹ * t * g₀)
      (isConj_iff_inv_mul.mpr ⟨g₀, rfl⟩) hC₀ hne₀
  have hs₀2 : orderOf (g₀⁻¹ * t * g₀) = 2 := by
    rw [orderOf_conj_inv, hctx.involution]
  have hs₀N : g₀⁻¹ * t * g₀ ∈ normalizer (L : Set G) :=
    hctx.cent_le_normalizer h36 _ hC₀
  obtain ⟨l, hlL, B, hB, hcent⟩ :=
    hP.i1_cent G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36)
      (g₀⁻¹ * t * g₀) hs₀2 hs₀N hα₀
  set s₁ : G := l⁻¹ * (g₀⁻¹ * t * g₀) * l with hs₁def
  have hlC : l ∈ centralizer ({t} : Set G) := hctx.le_centralizer hlL
  have hs₁C : s₁ ∈ centralizer ({t} : Set G) := by
    rw [hs₁def]
    exact (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).inv_mem hlC) hC₀) hlC
  have hs₁2 : orderOf s₁ = 2 := by
    rw [hs₁def, orderOf_conj_inv, hs₀2]
  have hs₁ne : s₁ ≠ t := by
    intro h
    apply hne₀
    have hlt : l * t * l⁻¹ = t := by
      have hcomm : l * t = t * l := Subgroup.mem_centralizer_singleton_iff.mp hlC
      rw [hcomm]; group
    calc g₀⁻¹ * t * g₀ = l * s₁ * l⁻¹ := by rw [hs₁def]; group
      _ = l * t * l⁻¹ := by rw [h]
      _ = t := hlt
  have hs₁P : s₁ ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpN : p ∈ normalizer (B : Set G) := le_normalizer_of_isNormalE16In hB hp
    have h := hcent p ⟨hp.2, hpN⟩
    rw [hs₁def]
    exact h.symm
  obtain ⟨s₂, hs₂S, hs₂P, c, hc, hs₂c⟩ := sec76_move_into_S h36 hctx hs₁C hs₁2 hs₁P
  have hs₂ne : s₂ ≠ t := by
    intro h2
    apply hs₁ne
    have hcinv : c⁻¹ * t = t * c⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp ((centralizer ({t} : Set G)).inv_mem hc)
    calc s₁ = c⁻¹ * (c * s₁ * c⁻¹) * c := by group
      _ = c⁻¹ * t * c := by rw [← hs₂c, h2]
      _ = t := by rw [hcinv]; group
  have hg : (g₀ * l * c⁻¹)⁻¹ * t * (g₀ * l * c⁻¹) = s₂ := by
    have h1 : (g₀ * l * c⁻¹)⁻¹ * t * (g₀ * l * c⁻¹) = c * s₁ * c⁻¹ := by
      rw [hs₁def]; group
    rw [h1, hs₂c]
  have hs₂C : s₂ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hs₂S
  have hα₂ : ∃ α : ℤˣ, InducesTypeSome L s₂ 6 1 1 α :=
    ((h74 G t L S z hctx).resolve_left hnc) s₂
      (isConj_iff_inv_mul.mpr ⟨g₀ * l * c⁻¹, hg⟩) hs₂C hs₂ne
  obtain ⟨α, hα⟩ := hα₂
  exact ⟨g₀ * l * c⁻¹, by rw [hg]; exact hs₂S, by rw [hg]; exact hs₂ne,
    by rw [hg]; exact hs₂P, ⟨α, by rw [hg]; exact hα⟩⟩

theorem asc82Lemma76Choice_of (h36 : Asc82Lemma36) (h74 : Asc82Lemma74) (hP : Asc82Tab6P)
    (h75a : Asc82Lemma75a) (h75b : Asc82Lemma75b) : Asc82Lemma76Choice := by
  intro G _ _ t L S z hctx
  by_cases hc : IsConj t (t * z)
  ·
    obtain ⟨g, hg⟩ := isConj_iff_inv_mul.mp hc
    obtain ⟨B₁, B₂, -, hB₁, -, -⟩ := h75a G t L S z hctx
    refine ⟨g, B₁, hctx, hB₁, ?_, ?_, Or.inl hg⟩
    · rw [hg]; exact S.mul_mem hctx.t_mem_S hctx.mem_S
    · rw [hg]
      intro ht
      have hz1 : z = 1 := by
        exact mul_left_cancel (show t * z = t * 1 by rw [mul_one]; exact ht)
      have hz2 : orderOf z = 2 := hctx.pocket.1
      rw [hz1, orderOf_one] at hz2
      norm_num at hz2
  ·
    obtain ⟨g, hmem, hne, hC, hα⟩ := sec76_exists_s h36 h74 hP hctx hc
    have hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := hctx.sylow.1 hmem
    have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
      hctx.cent_le_normalizer h36 _ hsC
    obtain ⟨B, hB, n, hn, hnc'⟩ := sec76_exists_B h36 hP h75a h75b hctx hsN hC hα
    exact ⟨g, B, hctx, hB, hmem, hne, Or.inr ⟨hc, hC, hα, n, hn, hnc'⟩⟩

end CFSG.OddStandard.SmallF3.Omega
