module

public import CFSG.ClassicalInvolution.Asc77.AscC25J15
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Uniform.U3Datum

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
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Single

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)} {ι : Type}


theorem exists_single_or_all (D : LieSystemDataU 3 1 ι E Φ) (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    {A A' : Subgroup E} {z a₀ b₀ : E} (T : TwinSect0 Φ A A' z a₀ b₀) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨ ∃ i₀ : ι, ∀ j, j = i₀ := by
  by_cases hall : ∀ L ∈ Φ, L = A ∨ L = A'
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨L₀, hL₀, hL₀A, hL₀A'⟩ := hall
  obtain ⟨iA, RA, -, hAeq⟩ := D.fundamental A T.hA
  obtain ⟨iB, RB, -, hBeq⟩ := D.fundamental A' T.hA'
  have hQ : ∀ j k : ι, j ≠ k → ∀ x ∈ (D.hom j).range, ∀ y ∈ (D.hom k).range, x * y = y * x := by
    rintro j k hjk _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact D.commute j k hjk x y
  have hnc : ∀ M ∈ Φ, ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x := by
    intro M hM
    obtain ⟨zM, hzM⟩ := hΦ.classical M hM
    exact hzM.exists_noncomm
  have hAle : A ≤ (D.hom iA).range := by rw [hAeq]; exact Subgroup.map_le_range _ _
  have hBle : A' ≤ (D.hom iB).range := by rw [hBeq]; exact Subgroup.map_le_range _ _
  have hmemA : ∀ M ∈ Φ, M ≠ A → M ≠ A' → M ≤ (D.hom iA).range := by
    intro M hM hMA hMA'
    obtain ⟨j, R, -, hMR⟩ := D.fundamental M hM
    have hMj : M ≤ (D.hom j).range := by rw [hMR]; exact Subgroup.map_le_range _ _
    by_cases hj : j = iA
    · rw [← hj]; exact hMj
    · exfalso
      have hc : Commutes A M := fun x hx y hy => hQ iA j (Ne.symm hj) x (hAle hx) y (hMj hy)
      exact hMA' (T.nbA M hM (mem_omegaNbr_of_commutes' hM hMA hc))
  have hmemB : ∀ M ∈ Φ, M ≠ A → M ≠ A' → M ≤ (D.hom iB).range := by
    intro M hM hMA hMA'
    obtain ⟨j, R, -, hMR⟩ := D.fundamental M hM
    have hMj : M ≤ (D.hom j).range := by rw [hMR]; exact Subgroup.map_le_range _ _
    by_cases hj : j = iB
    · rw [← hj]; exact hMj
    · exfalso
      have hc : Commutes A' M := fun x hx y hy => hQ iB j (Ne.symm hj) x (hBle hx) y (hMj hy)
      exact hMA (T.nbA' M hM (mem_omegaNbr_of_commutes' hM hMA' hc))
  have hAB : iB = iA := by
    by_contra hne
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc L₀ hL₀
    exact hxy (hQ iA iB (Ne.symm hne) x (hmemA L₀ hL₀ hL₀A hL₀A' hx) y
      (hmemB L₀ hL₀ hL₀A hL₀A' hy))
  refine ⟨iA, fun j => ?_⟩
  by_contra hj
  obtain ⟨R, -, hRΦ⟩ := D.meets j
  have hMj : R.map (D.hom j) ≤ (D.hom j).range := Subgroup.map_le_range _ _
  have hMi : R.map (D.hom j) ≤ (D.hom iA).range := by
    by_cases hMA : R.map (D.hom j) = A
    · rw [hMA]; exact hAle
    by_cases hMA' : R.map (D.hom j) = A'
    · rw [hMA']
      rw [hAB] at hBle
      exact hBle
    exact hmemA _ hRΦ hMA hMA'
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc _ hRΦ
  exact hxy (hQ j iA hj x (hMj hx) y (hMi hy))

theorem ih8Model_of_comp (hconj : ConjInvariant Φ) {c : Q3.CompData}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t k 3 e)
    (he : e = 1 ∨ (t = .trialityD4 ∧ 3 * e = 1)) (hc : c = compModel 3 e t k) (φ : c.G →* E)
    (hker : φ.ker ≤ Subgroup.center c.G) (hsurj : Function.Surjective φ)
    (hfund' : ∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map φ) : Nonempty (Ih8Model 3 1 Φ t k e) := by
  exact ⟨{ isFundTag := hfund
           admissible := hadm
           exp_eq := he
           ψ := castHom hc φ
           ker_le_center := castHom_ker_le_center hc φ hker
           surj := by
             rw [← MonoidHom.range_eq_top] at hsurj ⊢
             rw [range_castHom]
             exact hsurj
           cls := {R | R ∈ fundamentalSubgroups t (modelUniv t k 3 e Fact.out).D ∧
             R.map (castHom hc φ) ∈ Φ}
           cls_sub := fun _ hR => hR.1
           mem_iff := by
             intro L
             constructor
             · intro hL
               obtain ⟨R, hR, rfl⟩ := hfund' L hL
               obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc φ hR
               exact ⟨R', ⟨hR', by rw [hRR]; exact hL⟩, hRR.symm⟩
             · rintro ⟨R, hR, rfl⟩
               exact hR.2
           cls_conj := by
             intro R hR g
             refine ⟨Asc77.OmegaLie.fund_conj hR.1 g, ?_⟩
             have := map_conj_eq_conjSub_map (castHom hc φ) g R
             change Subgroup.map (castHom hc φ) (conjSub g R) ∈ Φ
             rw [show Subgroup.map (castHom hc φ) (conjSub g R) =
               conjSub (castHom hc φ g) (R.map (castHom hc φ)) from this]
             exact hconj _ _ hR.2 }⟩

end Single

end CFSG.ClassicalInvolution.Asc77.C25J
