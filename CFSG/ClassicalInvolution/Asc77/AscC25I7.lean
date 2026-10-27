module

public import CFSG.ClassicalInvolution.Asc77.AscC25I6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Asc77.C25V

section ModelFact

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinSwapQ5 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ →
    (∃ s : Y, s * s = 1 ∧ s * z' = z' * s ∧ conjSub s A = A' ∧ conjSub s A' = A ∧
      (∃ x : Y, s = x * z' * x⁻¹) ∧
      ∃ x y : Y, y ∈ conjSub x A ∧ orderOf y = 4 ∧ y * (z' * s) = (z' * s) * y) ∧
    ∀ w : Y, (∀ v : Y, v * w = w * v) → w = 1

end ModelFact

variable {p f : ℕ} [Fact p.Prime]


theorem twinSwapQ5_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (hperf : Group.IsPerfect (StatedSp 2 (GaloisField p e)))
    (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    (∃ s : Y, s * s = 1 ∧ s * z' = z' * s ∧ conjSub s (R.map ψ) = R'.map ψ ∧
      conjSub s (R'.map ψ) = R.map ψ ∧ (∃ x : Y, s = x * z' * x⁻¹) ∧
      ∃ x y : Y, y ∈ conjSub x (R.map ψ) ∧ orderOf y = 4 ∧
        y * (z' * s) = (z' * s) * y) ∧
      ∀ w : Y, (∀ v : Y, v * w = w * v) → w = 1 := by
  subst ht hk
  have h2 := C25W.two_ne_zero_gf (p := p) e hp2
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact Sp5.psp4_model_twinQ h2 hperf ψ hker hsurj hi hi' hne hz hz'


theorem twinSwapQ5_proved : TwinSwapQ5 p f := by
  intro hp2 h5 Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  have hexp : D.exp i₂ = f := by
    rcases D.exp_eq i₂ with h | ⟨h, -⟩
    · exact h
    · rw [(hcase i₂).1] at h
      exact absurd h (by decide)
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p (D.exp i₂)) := by
    rw [hexp, GaloisField.card p f hf0]
    omega
  have key := twinSwapQ5_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂)
    (isPerfect_statedSp_of_four_le h4)
    (D.hom i₂) (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hR hR' hne hz hz'
  rw [← hAR, ← hAR'] at key
  exact key

end CFSG.ClassicalInvolution.Asc77.C25I
