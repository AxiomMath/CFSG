module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22M11T
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T7P25X01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups


variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem exists_comp_all_U (D : Uniform.OmegaLieU 3 1 Φ)
    {A A' B : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hB : B ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hBA : B ≠ A) (hBA' : B ≠ A') (hBn : B ∉ omegaNbr Φ A) (hBn' : B ∉ omegaNbr Φ A') :
    ∃ i₀, ∀ L ∈ Φ, L ≤ D.comp i₀ := by
  obtain ⟨i₀, hAi₀⟩ := D.exists_comp_of_mem hA
  have hBi : B ≤ D.comp i₀ := by
    obtain ⟨j, hBj⟩ := D.exists_comp_of_mem hB
    by_cases hj : j = i₀
    · subst hj; exact hBj
    · exfalso; apply hBn
      refine MuTab.mem_omegaNbr_of_commutes hB hBA ?_
      intro a ha b hb
      exact D.comp_commute (Ne.symm hj) a (hAi₀ ha) b (hBj hb)
  have hA'i : A' ≤ D.comp i₀ := by
    obtain ⟨j, hA'j⟩ := D.exists_comp_of_mem hA'
    by_cases hj : j = i₀
    · subst hj; exact hA'j
    · exfalso; apply hBn'
      refine MuTab.mem_omegaNbr_of_commutes hB hBA' ?_
      intro a ha b hb
      exact D.comp_commute hj a (hA'j ha) b (hBi hb)
  refine ⟨i₀, fun L hL => ?_⟩
  obtain ⟨j, hLj⟩ := D.exists_comp_of_mem hL
  by_cases hj : j = i₀
  · subst hj; exact hLj
  · by_cases hLA : L = A
    · exact hLA ▸ hAi₀
    · have hLn : L ∈ omegaNbr Φ A :=
        MuTab.mem_omegaNbr_of_commutes hL hLA (fun a ha b hb =>
          D.comp_commute (Ne.symm hj) a (hAi₀ ha) b (hLj hb))
      exact (hnb L hL hLn) ▸ hA'i

theorem card_eq_one_of_all_le_U [Finite X] (D : Uniform.OmegaLieU 3 1 Φ) (hΦ : Q3T7M.HM Φ)
    {i₀ : Fin D.card} (hall : ∀ L ∈ Φ, L ≤ D.comp i₀) : D.card = 1 := by
  have hsub : ∀ j : Fin D.card, j = i₀ := by
    intro j
    by_contra hji
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    obtain ⟨z, hz⟩ := hΦ.classical _ hRΦ
    obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
    have hxj : x ∈ D.comp j := Subgroup.map_le_range _ _ hx
    exact hxy (D.comp_commute hji x hxj y (hall _ hRΦ hy))
  have hle : D.card ≤ 1 :=
    Fin.subsingleton_iff_le_one.mp ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have hpos : 0 < D.card := i₀.pos
  omega

theorem exists_hasLieType_of_frame [Finite X] {n : ℕ} (hBelow : Generic.CITBelowU n)
    (hΦ : Q3T7M.HM Φ) (hne : Φ.Nonempty) (hO : classicalInvolutionOddCore X = ⊥)
    (hlt : Nat.card X < n)
    {A A' B : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hB : B ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hBA : B ≠ A) (hBA' : B ≠ A') (hBn : B ∉ omegaNbr Φ A) (hBn' : B ∉ omegaNbr Φ A')
    (hAA' : A ≠ A') {z : X} (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z) :
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k : ℕ), HasLieType 3 1 Φ t k := by
  obtain ⟨D⟩ := Uniform.exists_omegaLieU hBelow hΦ hne hO hlt
  obtain ⟨i₀, hall⟩ := exists_comp_all_U D hA hA' hB hnb hBA hBA' hBn hBn'
  have hcard : D.card = 1 := card_eq_one_of_all_le_U D hΦ hall
  have hsub : ∀ j : Fin D.card, j = i₀ := fun j => Fin.ext (by
    have h1 := i₀.2
    have h2 := j.2
    omega)
  rcases D.valid i₀ with ⟨t, k, e, hft, hadm, hexp, hc⟩ | ⟨-, hs | hm⟩
  · have hi : CompIs 3 1 (D.kind i₀) t k := ⟨e, hexp, hft, hadm, hc⟩
    let σ : ∀ j, ModelSpec 3 1 (D.kind j) := fun j => (hsub j).symm ▸ hi.modelSpec
    exact ⟨t, k, D.toOmegaLieOfSpec σ, hcard, i₀, rfl, rfl⟩
  · exfalso
    let ψ : (SL(2, ZMod 3)) →* X := Uniform.castHom hs (D.hom i₀)
    have key : ∀ {L : Subgroup X}, L ∈ Φ → L = ψ.range := by
      intro L hL
      obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
      obtain rfl : i₀ = j := (hsub j).symm
      obtain ⟨R', hR', hRR⟩ := Uniform.exists_map_castHom hs (D.hom i₀) hR
      have hR'top : R' = ⊤ := Set.mem_singleton_iff.mp hR'
      rw [hLR, ← hRR, hR'top, ← MonoidHom.range_eq_map]
    exact hAA' ((key hA).trans (key hA').symm)
  · exact absurd (M11Tw.not_twins_of_hasM11TypeU ⟨by norm_num, D, hcard, i₀, hm⟩ hA hA' hAA' hzA
      hzA') id

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
