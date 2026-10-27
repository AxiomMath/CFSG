module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscC25G4
public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25I7
public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
public import CFSG.ClassicalInvolution.Uniform.ULieType

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section ModelU

variable {p e₀ : ℕ} [Fact p.Prime]

theorem isOrthTag_five {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (h : IsOrthTag 5 true t n) :
    t = .PSp ∧ n = 2 := by
  simp only [IsOrthTag] at h
  rcases h with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
  · exact ⟨ht, hn⟩
  all_goals omega

theorem perfect_statedSp_gf {e : ℕ} (h3 : 3 ≤ p ^ e) (he : 0 < e) :
    Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField p e)) := by
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he.ne'
  by_cases h : p ^ e = 3
  · exact CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 (GaloisField p e)
      (Or.inr (Or.inl ⟨by rw [hcard, h], le_rfl⟩))
  · exact isPerfect_statedSp_of_four_le (by rw [hcard]; omega)



theorem twinSwapQ5U (hp2 : p ≠ 2) (h3 : 3 ≤ p ^ e₀) {Y : Type} [Group Y] [Finite Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemDataU p e₀ (Fin 1) Y Φ)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (hT : IsOrthTag 5 true t n)
    (hC : CompIs p e₀ (D.kind 0) t n) {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (T : TwinSect0 Φ A A' z' a₀ b₀) :
    (∃ s : Y, s * s = 1 ∧ s * z' = z' * s ∧ conjSub s A = A' ∧ conjSub s A' = A ∧
      (∃ x : Y, s = x * z' * x⁻¹) ∧
      ∃ x y : Y, y ∈ conjSub x A ∧ orderOf y = 4 ∧ y * (z' * s) = (z' * s) * y) ∧
    ∀ w : Y, (∀ v : Y, v * w = w * v) → w = 1 := by
  obtain ⟨ht, hn⟩ := isOrthTag_five hT
  obtain ⟨e, he, -, hadm, hcomp⟩ := hC
  have hee : e = e₀ := by
    rcases he with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  subst hee
  let ψ := castHom hcomp (D.hom 0)
  have hker := castHom_ker_le_center hcomp (D.hom 0) (D.ker_le_center 0)
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, range_castHom]
    have h1 := D.generate
    have h2 : (⨆ i : Fin 1, (D.hom i).range) = (D.hom 0).range := by
      refine le_antisymm (iSup_le fun i => ?_) (le_iSup (fun i : Fin 1 => (D.hom i).range) 0)
      rw [Subsingleton.elim i 0]
    rw [h2] at h1
    exact h1
  obtain ⟨i₁, R₁, hR₁, hAR⟩ := D.fundamental A T.hA
  obtain ⟨i₂, R₂, hR₂, hAR'⟩ := D.fundamental A' T.hA'
  have hi₁ : i₁ = 0 := Subsingleton.elim _ _
  have hi₂ : i₂ = 0 := Subsingleton.elim _ _
  subst hi₁ hi₂
  obtain ⟨R₁', hR₁', hRR₁⟩ := exists_map_castHom hcomp (D.hom 0) hR₁
  obtain ⟨R₂', hR₂', hRR₂⟩ := exists_map_castHom hcomp (D.hom 0) hR₂
  have hA : R₁'.map ψ = A := hRR₁.trans hAR.symm
  have hA' : R₂'.map ψ = A' := hRR₂.trans hAR'.symm
  have hz : IsUniqueInvolution (R₁'.map ψ) z' := by
    rw [hA]
    exact T.hzA
  have hz' : IsUniqueInvolution (R₂'.map ψ) z' := by
    rw [hA']
    exact T.hzA'
  have hne : R₁'.map ψ ≠ R₂'.map ψ := by
    rw [hA, hA']
    exact T.ne
  have he0 : 0 < e := hadm.2.1
  have key := C25I.twinSwapQ5_of_hom hp2 t n e hadm (perfect_statedSp_gf h3 he0) ψ hker hsurj ht hn
    hR₁' hR₂' hne hz hz'
  rw [hA, hA'] at key
  exact key

theorem twinCent6U (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemDataU p e₀ (Fin 1) Y Φ)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (hT : IsOrthTag 6 (!piSign p e₀) t n)
    (hC : CompIs p e₀ (D.kind 0) t n) {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (T : TwinSect0 Φ A A' z' a₀ b₀) :
    ∃ τ y : Y, τ ≠ z' ∧ τ * z' = z' * τ ∧ τ * τ = 1 ∧ y * z' * y⁻¹ = τ ∧
      conjSub τ A = A ∧ conjSub τ A' = A' := by
  obtain ⟨e, he, -, hadm, hcomp⟩ := hC
  have hcase : (t = .PSL ∧ n = 4 ∧ ¬ p ^ e₀ % 4 = 1) ∨ (t = .PSU ∧ n = 4 ∧ p ^ e₀ % 4 = 1) := by
    simp only [IsOrthTag] at hT
    rcases hT with ⟨h5, -⟩ | ⟨-, hε, ht, hn⟩ | ⟨-, hε, ht, hn⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · omega
    · left
      refine ⟨ht, hn, ?_⟩
      simp only [piSign, Bool.not_eq_true', decide_eq_false_iff_not] at hε
      exact hε
    · right
      refine ⟨ht, hn, ?_⟩
      simp only [piSign, Bool.not_eq_false', decide_eq_true_eq] at hε
      exact hε
    · omega
    · omega
    · omega
  have hee : e = e₀ := by
    rcases he with h | ⟨h, -⟩
    · exact h
    · rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact absurd h (by decide)
  subst hee
  let ψ := castHom hcomp (D.hom 0)
  have hker := castHom_ker_le_center hcomp (D.hom 0) (D.ker_le_center 0)
  obtain ⟨i₁, R₁, hR₁, hAR⟩ := D.fundamental A T.hA
  obtain ⟨i₂, R₂, hR₂, hAR'⟩ := D.fundamental A' T.hA'
  have hi₁ : i₁ = 0 := Subsingleton.elim _ _
  have hi₂ : i₂ = 0 := Subsingleton.elim _ _
  subst hi₁ hi₂
  obtain ⟨R₁', hR₁', hRR₁⟩ := exists_map_castHom hcomp (D.hom 0) hR₁
  obtain ⟨R₂', hR₂', hRR₂⟩ := exists_map_castHom hcomp (D.hom 0) hR₂
  have hA : R₁'.map ψ = A := hRR₁.trans hAR.symm
  have hA' : R₂'.map ψ = A' := hRR₂.trans hAR'.symm
  have hz : IsUniqueInvolution (R₁'.map ψ) z' := by
    rw [hA]
    exact T.hzA
  have hz' : IsUniqueInvolution (R₂'.map ψ) z' := by
    rw [hA']
    exact T.hzA'
  have hne : R₁'.map ψ ≠ R₂'.map ψ := by
    rw [hA, hA']
    exact T.ne
  have key := C25G.twinCent6_of_hom hp2 t n e hadm ψ hker hcase hR₁' hR₂' hne hz hz'
  rw [hA, hA'] at key
  exact key

end ModelU

end CFSG.ClassicalInvolution.Asc77.C25J
