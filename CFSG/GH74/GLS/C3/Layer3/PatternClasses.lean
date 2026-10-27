module

public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.C3.Layer3.Basic

public section

namespace CFSG.GH74.GLS.Layer3

open Subgroup

theorem exists_centralizer_mulEquiv_of_sameCentralizerOfInvolutionPattern
    {G G' : Type*} [Group G] [Finite G] [Group G']
    (hP : SameCentralizerOfInvolutionPattern G G') {z : G} (hz : orderOf z = 2) :
    ∃ w : G', orderOf w = 2 ∧
      Nonempty (centralizer ({z} : Set G) ≃* centralizer ({w} : Set G')) := by
  obtain ⟨S, S', φ, -, hcent⟩ := hP
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_two S hz
  have hconj : IsConj z (g * z * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have hz' : orderOf (g * z * g⁻¹) = 2 := by
    rw [← orderOf_eq_of_isConj' hconj]
    exact hz
  let u : ↥(S : Subgroup G) := ⟨g * z * g⁻¹, hg⟩
  have hu : orderOf u = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz'
  refine ⟨(φ u : G'), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq φ u]
    exact hu
  · obtain ⟨e⟩ := hcent u hu
    exact ⟨(nonempty_centralizer_mulEquiv_of_isConj hconj).some.trans e⟩

theorem pattern_two_classes {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (hP : SameCentralizerOfInvolutionPattern G G') {a b : G'} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : ¬ IsConj a b)
    (hcl : ∀ w : G', orderOf w = 2 → IsConj a w ∨ IsConj b w) :
    ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y ∧
      (∀ w : G, orderOf w = 2 → IsConj x w ∨ IsConj y w) ∧
      Nonempty (centralizer ({x} : Set G) ≃* centralizer ({a} : Set G')) ∧
      Nonempty (centralizer ({y} : Set G) ≃* centralizer ({b} : Set G')) := by
  obtain ⟨S, S', φ, hconj, hcent⟩ := hP
  obtain ⟨g₁, hg₁⟩ := exists_conj_mem_sylow_two S' ha
  obtain ⟨g₂, hg₂⟩ := exists_conj_mem_sylow_two S' hb
  set a' : G' := g₁ * a * g₁⁻¹ with ha'
  set b' : G' := g₂ * b * g₂⁻¹ with hb'
  have haa' : IsConj a a' := (isConj_iff.2 ⟨g₁, rfl⟩)
  have hbb' : IsConj b b' := (isConj_iff.2 ⟨g₂, rfl⟩)
  have ha'o : orderOf a' = 2 := by rw [← orderOf_eq_of_isConj' haa']; exact ha
  have hb'o : orderOf b' = 2 := by rw [← orderOf_eq_of_isConj' hbb']; exact hb
  set sa : ↥(S : Subgroup G) := φ.symm ⟨a', hg₁⟩ with hsa
  set sb : ↥(S : Subgroup G) := φ.symm ⟨b', hg₂⟩ with hsb
  have hφa : φ sa = ⟨a', hg₁⟩ := by rw [hsa]; exact φ.apply_symm_apply _
  have hφb : φ sb = ⟨b', hg₂⟩ := by rw [hsb]; exact φ.apply_symm_apply _
  have hsao : orderOf sa = 2 := by
    rw [← MulEquiv.orderOf_eq φ, hφa, Subgroup.orderOf_mk]; exact ha'o
  have hsbo : orderOf sb = 2 := by
    rw [← MulEquiv.orderOf_eq φ, hφb, Subgroup.orderOf_mk]; exact hb'o
  have hxo : orderOf (sa : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hsao
  have hyo : orderOf (sb : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hsbo
  refine ⟨(sa : G), (sb : G), hxo, hyo, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := (hconj sa sb hsao hsbo).1 h
    rw [hφa, hφb] at h1
    exact hab (haa'.trans (h1.trans hbb'.symm))
  · intro w hw
    obtain ⟨g, hg⟩ := exists_conj_mem_sylow_two S hw
    set w' : ↥(S : Subgroup G) := ⟨g * w * g⁻¹, hg⟩ with hw'
    have hw'o : orderOf w' = 2 := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (g * w * g⁻¹) = 2
      rw [← orderOf_eq_of_isConj' (isConj_iff.2 ⟨g, rfl⟩)]; exact hw
    have hww' : IsConj w (w' : G) := isConj_iff.2 ⟨g, rfl⟩
    have hφw : orderOf ((φ w' : ↥(S' : Subgroup G')) : G') = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hw'o
    rcases hcl _ hφw with h | h
    · left
      refine ((hconj sa w' hsao hw'o).2 ?_).trans hww'.symm
      rw [hφa]
      exact haa'.symm.trans h
    · right
      refine ((hconj sb w' hsbo hw'o).2 ?_).trans hww'.symm
      rw [hφb]
      exact hbb'.symm.trans h
  · obtain ⟨e⟩ := hcent sa hsao
    rw [hφa] at e
    exact ⟨e.trans (nonempty_centralizer_mulEquiv_of_isConj haa'.symm).some⟩
  · obtain ⟨e⟩ := hcent sb hsbo
    rw [hφb] at e
    exact ⟨e.trans (nonempty_centralizer_mulEquiv_of_isConj hbb'.symm).some⟩

theorem pattern_two_classes_card {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (hP : SameCentralizerOfInvolutionPattern G G') {a b : G'} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : ¬ IsConj a b)
    (hcl : ∀ w : G', orderOf w = 2 → IsConj a w ∨ IsConj b w) :
    ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y ∧
      (∀ w : G, orderOf w = 2 → IsConj x w ∨ IsConj y w) ∧
      Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({a} : Set G')) ∧
      Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({b} : Set G')) := by
  obtain ⟨x, y, hx, hy, hxy, hcl', ⟨e₁⟩, ⟨e₂⟩⟩ := pattern_two_classes hP ha hb hab hcl
  exact ⟨x, y, hx, hy, hxy, hcl', Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv⟩

end CFSG.GH74.GLS.Layer3
