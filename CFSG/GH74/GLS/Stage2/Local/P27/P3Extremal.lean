module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

section Extremal

theorem isSylowOf_centralizer_of_isConj {x t' : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hxt : IsConj x t')
    (hTc : T ≤ centralizer ({t'} : Set G)) : IsSylowOf 2 T (centralizer ({t'} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 hxt
  have hmap : (centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({t'} : Set G) := by
    ext y
    simp only [Subgroup.mem_map, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [← hc]
      calc c * x * c⁻¹ * (MulAut.conj c).toMonoidHom a = c * (x * a) * c⁻¹ := by
            simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]; group
        _ = c * (a * x) * c⁻¹ := by rw [ha]
        _ = (MulAut.conj c).toMonoidHom a * (c * x * c⁻¹) := by
            simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]; group
    · intro hy
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · rw [← hc] at hy
        calc x * (c⁻¹ * y * c) = c⁻¹ * (c * x * c⁻¹ * y) * c := by group
          _ = c⁻¹ * (y * (c * x * c⁻¹)) * c := by rw [hy]
          _ = c⁻¹ * y * c * x := by group
      · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]; group
  have hcard : Nat.card (centralizer ({t'} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact isSylowOf_of_card hTc (by rw [hT.card_eq, hcard])

theorem exists_conj_centralizer_of_extremal {x t' s : G} {T D₁ : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hxt : IsConj x t') (ht'c : ∀ y ∈ T, t' * y = y * t')
    (hD₁ : D₁ ≤ T) (hx : x ∈ ⁅D₁, D₁⁆) (hx1 : x ≠ 1) (hx2 : x * x = 1)
    (hs : IsConj s t') (hsD : ∀ a ∈ D₁, s * a = a * s) (hxs : x ≠ s)
    (hΩ : ∀ y ∈ ⁅T, T⁆, y * y = 1 → y = 1 ∨ y = x ∨ y = t' ∨ y = x * t')
    (hnc : ¬ IsConj x (x * t')) :
    ∃ c ∈ centralizer ({x} : Set G), c * t' * c⁻¹ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTc : T ≤ centralizer ({t'} : Set G) := fun y hy =>
    mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact ht'c y hy)
  have hTt : IsSylowOf 2 T (centralizer ({t'} : Set G)) := isSylowOf_centralizer_of_isConj hT hxt hTc
  obtain ⟨Ts, hTs⟩ := hT.isPGroup.exists_le_sylow
  have hS : IsPGroup 2 (Ts : Subgroup G) := Ts.isPGroup'
  have hTS : T ≤ (Ts : Subgroup G) ⊓ centralizer ({t'} : Set G) := le_inf hTs hTc
  have hP2 : IsPGroup 2 ↥((Ts : Subgroup G) ⊓ centralizer ({t'} : Set G)) := hS.to_inf_left
  have hPT : (Ts : Subgroup G) ⊓ centralizer ({t'} : Set G) = T :=
    hTt.eq_of_le hTS inf_le_right hP2
  obtain ⟨c0, hc0⟩ := isConj_iff.1 hs
  have huv : c0⁻¹ * t' * c0 = s := by rw [← hc0]; group
  obtain ⟨g, hg1, hg2⟩ := CFSG.ComponentClassification.GHarris.exists_conj_extremal (S := (Ts : Subgroup G))
    hS (u := s) (v := t') (h := c0) (by rw [hPT]; exact hTt) huv
  have hD₁g : ∀ a ∈ D₁, g⁻¹ * a * g ∈ T := by
    intro a ha
    have h1 : a ∈ (Ts : Subgroup G) ⊓ centralizer ({s} : Set G) :=
      ⟨hTs (hD₁ ha), mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact hsD a ha)⟩
    have := hg2 a h1
    rwa [hPT] at this
  set φ : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφa : ∀ a : G, φ a = g⁻¹ * a * g := fun a => by simp [hφ]
  have hmem : g⁻¹ * x * g ∈ ⁅T, T⁆ := by
    have h1 : φ x ∈ ⁅D₁, D₁⁆.map φ := Subgroup.mem_map_of_mem φ hx
    rw [Subgroup.map_commutator] at h1
    have h2 : D₁.map φ ≤ T := by
      rintro _ ⟨a, ha, rfl⟩
      rw [hφa a]
      exact hD₁g a ha
    rw [hφa x] at h1
    exact Subgroup.commutator_mono h2 h2 h1
  have hsq : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  have hgx : g⁻¹ * x * g = x := by
    rcases hΩ _ hmem hsq with h | h | h | h
    · exfalso
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]; group
    · exact h
    · exfalso
      apply hxs
      have h' : g⁻¹ * x * g = g⁻¹ * s * g := by rw [h, hg1]
      have := congrArg (fun y => g * y * g⁻¹) h'
      simpa [mul_assoc] using this
    · exfalso
      apply hnc
      exact isConj_iff.2 ⟨g⁻¹, by rw [← h]; simp⟩
  refine ⟨g, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    calc x * g = g * (g⁻¹ * x * g) := by group
      _ = g * x := by rw [hgx]
  · rw [← hg1]; group

end Extremal

end CFSG.GH74.GLS.Stage2.Local.P27
