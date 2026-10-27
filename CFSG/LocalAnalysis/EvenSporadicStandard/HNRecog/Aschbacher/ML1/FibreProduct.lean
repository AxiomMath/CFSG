module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

abbrev C2 : Type := Multiplicative (ZMod 2)

theorem exists_mulEquiv_of_hom_C2 {L L' : Type} [Group L] [Group L'] (G : Subgroup (L × L'))
    (z : L) (z' : L') (hz : (z, (1 : L')) ∈ G) (hz' : ((1 : L), z') ∈ G)
    (hπ₁ : ∀ l : L, ∃ l' : L', (l, l') ∈ G) (hπ₂ : ∀ l' : L', ∃ l : L, (l, l') ∈ G)
    (hk₁ : ∀ l' : L', ((1 : L), l') ∈ G → l' = 1 ∨ l' = z')
    (hk₂ : ∀ l : L, (l, (1 : L')) ∈ G → l = 1 ∨ l = z)
    (lam : G →* C2) (hlam : lam ⟨(z, 1), hz⟩ ≠ 1) (hlam' : lam ⟨(1, z'), hz'⟩ ≠ 1) :
    ∃ e : L ≃* L', ∀ l : L, (l, e l) ∈ G := by
  have hC2 : ∀ a b : C2, a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
  classical
  let D : Subgroup (L × L') := lam.ker.map G.subtype
  have mem_D : ∀ p : L × L', p ∈ D ↔ ∃ h : p ∈ G, lam ⟨p, h⟩ = 1 := by
    intro p
    constructor
    · intro hp
      obtain ⟨g, hgker, hgp⟩ := Subgroup.mem_map.mp hp
      refine ⟨?_, ?_⟩
      · exact hgp ▸ g.2
      · have h_eq : (⟨p, hgp ▸ g.2⟩ : G) = g := Subtype.ext hgp.symm
        rw [h_eq]
        exact hgker
    · rintro ⟨h, hh⟩
      exact Subgroup.mem_map.mpr ⟨⟨p, h⟩, hh, rfl⟩
  let f₁ : D →* L := (MonoidHom.fst L L').comp D.subtype
  let f₂ : D →* L' := (MonoidHom.snd L L').comp D.subtype
  have hzz' : (z, z') ∈ G := by simpa using G.mul_mem hz hz'
  have hzz'_D : (z, z') ∈ D := by
    rw [mem_D]
    refine ⟨hzz', ?_⟩
    have hsplit : (⟨(z, z'), hzz'⟩ : G) = ⟨(z, 1), hz⟩ * ⟨(1, z'), hz'⟩ := by
      apply Subtype.ext
      simp
    rw [hsplit, map_mul]
    exact hC2 _ _ hlam hlam'
  let dz : D := ⟨(z, z'), hzz'_D⟩
  have hdz₁ : f₁ dz = z := rfl
  have hdz₂ : f₂ dz = z' := rfl
  have inj₁ : Function.Injective f₁ := by
    intro d₁ d₂ h
    have hfst : (d₁ : L × L').1 = (d₂ : L × L').1 := h
    have hmem : ((1 : L), (d₁ : L × L').2⁻¹ * (d₂ : L × L').2) ∈ D := by
      have heq : ((1 : L), (d₁ : L × L').2⁻¹ * (d₂ : L × L').2)
          = (d₁ : L × L')⁻¹ * (d₂ : L × L') := by
        apply Prod.ext
        · simp [hfst]
        · rfl
      rw [heq]
      exact D.mul_mem (D.inv_mem d₁.2) d₂.2
    rw [mem_D] at hmem
    obtain ⟨hG, hlam1⟩ := hmem
    rcases hk₁ _ hG with h1 | hz1
    · have hsec : (d₁ : L × L').2 = (d₂ : L × L').2 := inv_mul_eq_one.mp h1
      exact Subtype.ext (Prod.ext hfst hsec)
    · exfalso
      apply hlam'
      have hp : (((1 : L), z') : L × L')
          = ((1 : L), (d₁ : L × L').2⁻¹ * (d₂ : L × L').2) := by
        rw [hz1]
      have hconj : (⟨((1 : L), z'), hz'⟩ : G)
          = ⟨((1 : L), (d₁ : L × L').2⁻¹ * (d₂ : L × L').2), hG⟩ := by
        apply Subtype.ext
        exact hp
      rw [hconj]
      exact hlam1
  have surj₁ : Function.Surjective f₁ := by
    intro l
    obtain ⟨l', hl'⟩ := hπ₁ l
    by_cases hg : lam (⟨(l, l'), hl'⟩ : G) = 1
    · have hD : (l, l') ∈ D := by
        rw [mem_D]
        exact ⟨hl', hg⟩
      exact ⟨⟨(l, l'), hD⟩, rfl⟩
    · have hker : (⟨(l, l'), hl'⟩ : G) * ⟨(z, 1), hz⟩ ∈ lam.ker := by
        rw [MonoidHom.mem_ker, map_mul]
        exact hC2 _ _ hg hlam
      have hD : ((⟨(l, l'), hl'⟩ : G) * ⟨(z, 1), hz⟩).val ∈ D :=
        Subgroup.mem_map.mpr ⟨(⟨(l, l'), hl'⟩ : G) * ⟨(z, 1), hz⟩, hker, rfl⟩
      refine ⟨⟨((⟨(l, l'), hl'⟩ : G) * ⟨(z, 1), hz⟩).val, hD⟩ * dz⁻¹, ?_⟩
      have hA : f₁ ⟨((⟨(l, l'), hl'⟩ : G) * ⟨(z, 1), hz⟩).val, hD⟩ = l * z := rfl
      rw [map_mul, map_inv, hdz₁, hA]
      simp
  have inj₂ : Function.Injective f₂ := by
    intro d₁ d₂ h
    have hsnd : (d₁ : L × L').2 = (d₂ : L × L').2 := h
    have hmem : ((d₁ : L × L').1⁻¹ * (d₂ : L × L').1, (1 : L')) ∈ D := by
      have heq : ((d₁ : L × L').1⁻¹ * (d₂ : L × L').1, (1 : L'))
          = (d₁ : L × L')⁻¹ * (d₂ : L × L') := by
        apply Prod.ext
        · rfl
        · simp [hsnd]
      rw [heq]
      exact D.mul_mem (D.inv_mem d₁.2) d₂.2
    rw [mem_D] at hmem
    obtain ⟨hG, hlam1⟩ := hmem
    rcases hk₂ _ hG with h1 | hz1
    · have hfst : (d₁ : L × L').1 = (d₂ : L × L').1 := inv_mul_eq_one.mp h1
      exact Subtype.ext (Prod.ext hfst hsnd)
    · exfalso
      apply hlam
      have hp : ((z, (1 : L')) : L × L')
          = ((d₁ : L × L').1⁻¹ * (d₂ : L × L').1, (1 : L')) := by
        rw [hz1]
      have hconj : (⟨(z, (1 : L')), hz⟩ : G)
          = ⟨((d₁ : L × L').1⁻¹ * (d₂ : L × L').1, (1 : L')), hG⟩ := by
        apply Subtype.ext
        exact hp
      rw [hconj]
      exact hlam1
  have surj₂ : Function.Surjective f₂ := by
    intro l'
    obtain ⟨l, hl⟩ := hπ₂ l'
    by_cases hg : lam (⟨(l, l'), hl⟩ : G) = 1
    · have hD : (l, l') ∈ D := by
        rw [mem_D]
        exact ⟨hl, hg⟩
      exact ⟨⟨(l, l'), hD⟩, rfl⟩
    · have hker : (⟨(l, l'), hl⟩ : G) * ⟨(1, z'), hz'⟩ ∈ lam.ker := by
        rw [MonoidHom.mem_ker, map_mul]
        exact hC2 _ _ hg hlam'
      have hD : ((⟨(l, l'), hl⟩ : G) * ⟨(1, z'), hz'⟩).val ∈ D :=
        Subgroup.mem_map.mpr ⟨(⟨(l, l'), hl⟩ : G) * ⟨(1, z'), hz'⟩, hker, rfl⟩
      refine ⟨⟨((⟨(l, l'), hl⟩ : G) * ⟨(1, z'), hz'⟩).val, hD⟩ * dz⁻¹, ?_⟩
      have hA : f₂ ⟨((⟨(l, l'), hl⟩ : G) * ⟨(1, z'), hz'⟩).val, hD⟩ = l' * z' := rfl
      rw [map_mul, map_inv, hdz₂, hA]
      simp
  let e₁ : D ≃* L := MulEquiv.ofBijective f₁ ⟨inj₁, surj₁⟩
  let e₂ : D ≃* L' := MulEquiv.ofBijective f₂ ⟨inj₂, surj₂⟩
  refine ⟨e₁.symm.trans e₂, ?_⟩
  intro l
  have hval : ((e₁.symm l : D) : L × L') = (l, e₁.symm.trans e₂ l) := by
    apply Prod.ext
    · exact e₁.apply_symm_apply l
    · rfl
  have hDG : D ≤ G := Subgroup.map_subtype_le lam.ker
  rw [← hval]
  exact hDG (e₁.symm l).2

end CFSG.EvenSporadicStandard.HNRecog.ML1
