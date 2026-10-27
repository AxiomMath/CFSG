module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X9

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


theorem MF2L.reflWit_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y] (t : StatedLieTag)
    (k e : ℕ) (hadm : StatedLieAdmissible t k p e)
    (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (hcase : t = .PSL ∧ k = 4 ∧ ¬ p ^ e % 4 = 1)
    (hq : 5 ≤ p ^ e) {R R' : Subgroup (Generic.modelUniv t k p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ (R.map ψ) (R'.map ψ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ R.map ψ, β y = y) (hβA' : ∀ y ∈ R'.map ψ, β y = y) (hβ2 : β * β = 1)
    (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj z') :
    ∃ (hA : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hB : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
      (hB' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
      IsOm5 p e (centTG _ _ β hA hA') ∧ IsOm5 p e (centTG _ _ (β * MulAut.conj z') hB hB') ∧
        DiagWit p (centTG _ _ β hA hA') (centTG _ _ (β * MulAut.conj z') hB hB') := by
  obtain ⟨rfl, rfl, h4⟩ := hcase
  have he : 1 ≤ e := hadm.2.1
  have hsq : ¬ IsSquare (-1 : GaloisField p e) := by
    have : Fintype (GaloisField p e) := Fintype.ofFinite _
    have hodd : p ^ e % 2 = 1 :=
      Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
      GaloisField.card p e (by omega)]
    omega
  exact MF2L.reflWit_psl4 hp2 hq hsq ψ hker hsurj
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    htw hconj β hβA hβA' hβ2 hβ1 hβz

theorem isOm5_of_eq {e e' : ℕ} (h : e = e') {K₀ K₀' : Type} [Group K₀] [Group K₀']
    {L : TwinGroup K₀ K₀'} (hL : IsOm5 p e L) : IsOm5 p e' L :=
  h ▸ hL

theorem om6ReflWit_of (hU : p ^ f % 4 = 1 → Om6ReflWit p f) : Om6ReflWit p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  by_cases h1 : p ^ f % 4 = 1
  · exact hU h1 Y Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  obtain ⟨D, hD1, i, hi⟩ := hY.lie
  have htw := hY.twin
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom i).range := by
      intro l
      rw [Subsingleton.elim l i]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : D.tag i = .PSL ∧ D.rank i = 4 ∧ ¬ p ^ f % 4 = 1 := by
    simp only [IsOrthTag] at hi
    rcases hi with ⟨h5, -⟩ | ⟨-, -, ht, hn⟩ | ⟨-, hε, -, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · omega
    · exact ⟨ht, hn, h1⟩
    · exfalso
      simp only [piSign, Bool.not_eq_false', decide_eq_true_eq] at hε
      exact h1 hε
    · omega
    · omega
    · omega
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨hT, -⟩
    · exact h
    · rw [hcase.1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₁ : i₁ = i := Subsingleton.elim _ _
  have h₂ : i₂ = i := Subsingleton.elim _ _
  subst h₁ h₂
  have hq : 5 ≤ p ^ D.exp i₂ := by rw [hexp]; exact hY.five
  subst hAR hAR'
  obtain ⟨hA, hA', hB, hB', h5, h5', hw⟩ := MF2L.reflWit_of_hom hY.odd (D.tag i₂) (D.rank i₂)
    (D.exp i₂) (D.admissible i₂) (D.hom i₂) (D.ker_le_center i₂) hsurj
    ⟨hcase.1, hcase.2.1, by rw [hexp]; exact h1⟩ hq hR hR' htw hY.conj β hβA hβA' hβ2 hβ1 hβz
  exact ⟨hA, hA', hB, hB', isOm5_of_eq hexp h5, isOm5_of_eq hexp h5', hw⟩

end CFSG.ClassicalInvolution.Asc77.CX
