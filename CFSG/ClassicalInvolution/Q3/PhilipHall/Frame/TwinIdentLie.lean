module

public import CFSG.ClassicalInvolution.Uniform.UOmegaLie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdent

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77


section OneComponent

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem commute_range (D : LieSystemData3 ι X Φ) {i j : ι} (h : i ≠ j) {x y : X}
    (hx : x ∈ (D.hom i).range) (hy : y ∈ (D.hom j).range) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact D.commute i j h a b

theorem mem_normalizer_range (D : LieSystemData3 ι X Φ) (i : ι) (g : X) :
    g ∈ Subgroup.normalizer ((D.hom i).range : Set X) := by
  have hle : (⨆ k, (D.hom k).range : Subgroup X) ≤
      Subgroup.normalizer ((D.hom i).range : Set X) := by
    refine iSup_le fun k => ?_
    by_cases hki : k = i
    · subst hki
      exact Subgroup.le_normalizer
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hc : ∀ y ∈ (D.hom i).range, x * y = y * x := fun y hy =>
        commute_range D hki hx hy
      constructor
      · intro hh
        have : x * h * x⁻¹ = h := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hc h hh
        rw [this]
        exact hh
      · intro hh
        have hw := hc _ hh
        have e : x * h = x * (x * h * x⁻¹) := by
          calc x * h = (x * h * x⁻¹) * x := by group
            _ = x * (x * h * x⁻¹) := hw.symm
        have e' : h = x * h * x⁻¹ := mul_left_cancel e
        rw [e']
        exact hh
  exact hle (by rw [D.generate]; trivial)

theorem le_range_of_transitive (D : LieSystemData3 ι X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {K : Subgroup X} (hK : K ∈ Φ) {i : ι}
    (hKi : K ≤ (D.hom i).range) : ∀ L ∈ Φ, L ≤ (D.hom i).range := by
  intro L hL x hx
  obtain ⟨g, rfl⟩ := htrans K hK L hL
  rw [mem_conjSub_iff] at hx
  have h1 := hKi hx
  have h2 := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_range D i g) _).mp h1
  simpa [mul_assoc] using h2

theorem exists_le_range (D : LieSystemData3 ι X Φ) {K : Subgroup X} (hK : K ∈ Φ) :
    ∃ i, K ≤ (D.hom i).range := by
  obtain ⟨i, R, -, rfl⟩ := D.fundamental K hK
  exact ⟨i, Subgroup.map_le_range _ _⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.LieSystemData3.subsingleton_of_transitive
    (D : LieSystemData3 ι X Φ) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hnc : ∀ L ∈ Φ, ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) (hne : Φ.Nonempty) :
    ∀ i j : ι, i = j := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨i₀, hKi₀⟩ := exists_le_range D hK
  have hall := le_range_of_transitive D htrans hK hKi₀
  have hsub : ∀ j : ι, j = i₀ := by
    intro j
    by_contra hji
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc _ hRΦ
    have hxj : x ∈ (D.hom j).range := Subgroup.map_le_range _ _ hx
    have hyj : y ∈ (D.hom j).range := Subgroup.map_le_range _ _ hy
    exact hxy (commute_range D hji hxj (hall _ hRΦ hy))
  intro i j
  rw [hsub i, hsub j]

theorem _root_.CFSG.ClassicalInvolution.Q3.LieSystemData3.subsingleton_of_conjClass
    {M : Subgroup X} (hM : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x)
    (D : LieSystemData3 ι X (CoreAssembly.conjClass M)) : ∀ i j : ι, i = j := by
  refine D.subsingleton_of_transitive ?_ ?_ ⟨M, 1, conjSub_one M⟩
  · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right]
  · rintro _ ⟨g, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hM
    refine ⟨g * x * g⁻¹, ?_, g * y * g⁻¹, ?_, ?_⟩
    · rw [mem_conjSub_iff]; simpa [mul_assoc] using hx
    · rw [mem_conjSub_iff]; simpa [mul_assoc] using hy
    · intro h
      apply hxy
      have := congrArg (fun w => g⁻¹ * w * g) h
      simpa [mul_assoc] using this

end OneComponent

section OddCore

variable {X : Type} [Group X] {Λ : Set (Subgroup X)}

theorem lieSystem3_of_oddCore_eq_bot (hO : classicalInvolutionOddCore X = ⊥)
    (h : LieSystemMod3 Λ) : LieSystem3 X Λ := by
  let e : (X ⧸ classicalInvolutionOddCore X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hee : ∀ x : X, e (QuotientGroup.mk x) = x := fun x => rfl
  have hfam : Subgroup.map e.toMonoidHom '' oddQuotientFamily Λ = Λ := by
    ext L
    constructor
    · rintro ⟨_, ⟨K, hK, rfl⟩, rfl⟩
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore X)) =
          MonoidHom.id X := by
        ext x
        exact hee x
      rw [this, Subgroup.map_id]
      exact hK
    · intro hL
      refine ⟨_, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore X)) =
          MonoidHom.id X := by
        ext x
        exact hee x
      rw [this, Subgroup.map_id]
  have := LieSystem3.congr e h
  rwa [hfam] at this

end OddCore

section OfOmegaLieU

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem compData_valid_of_compValid {c : CompData} (h : CompValid 3 1 c) : c.Valid := by
  rcases h with ⟨t, n, e, ht, hadm, he, rfl⟩ | ⟨-, h | h⟩
  · have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩
      · exact he
      · omega
    subst he1
    exact Or.inl ⟨t, n, ht, hadm, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

@[expose] noncomputable def _root_.CFSG.ClassicalInvolution.Uniform.OmegaLieU.toLieSystemData3
    (D : OmegaLieU 3 1 Φ) (hgen : omegaGen Φ = ⊤) : LieSystemData3 (Fin D.card) X Φ where
  kind := D.kind
  valid i := compData_valid_of_compValid (D.valid i)
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate.trans hgen
  fundamental := D.fundamental
  meets := D.meets
  card_eq := D.card_eq (by norm_num)

end OfOmegaLieU


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdent
