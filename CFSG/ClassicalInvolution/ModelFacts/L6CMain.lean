module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y4
public import CFSG.ClassicalInvolution.ModelFacts.L6CDefs
import CFSG.ClassicalInvolution.ModelFacts.L6CChar2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


theorem models_of_lie (hL : Aut164L4 p) (hU : Aut164U4 p) {Y : Type} [Group Y]
    (t : StatedLieTag) (k e : ℕ) (hadm : StatedLieAdmissible t k p e)
    (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ)
    (hcase : (t = .PSL ∧ k = 4 ∧ p ^ e % 4 = 3) ∨ (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 1))
    (β : MulAut Y) (hβ : β ^ 2 = 1) :
    ∃ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D, ∃ s ∈ R,
      orderOf (ψ s) = 4 ∧ β (ψ s) = ψ s := by
  rcases hcase with ⟨rfl, rfl, h4⟩ | ⟨rfl, rfl, h4⟩
  · exact hL e hadm h4 Y ψ hker hsurj β hβ
  · exact hU e hadm h4 Y ψ hker hsurj β hβ

theorem false_of_char2 (hp2 : p = 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K) (ht : t = .PSL)
    (hk : k = 4)
    {R : Subgroup (Generic.modelUniv t k p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D) {z : Y}
    (hz : IsUniqueInvolution (R.map ψ) z) : False := by
  subst ht hk hp2
  exact not_uniqueInvolution_char2 ψ hker
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR) hz

theorem false_of_twin_char2 (hp2 : p = 2) {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}
    (D : LieSystemData p f Y Φ) (hD1 : D.card = 1) (i : Fin D.card) (ht : D.tag i = .PSL)
    (hn : D.rank i = 4) {A : Subgroup Y} (hA : A ∈ Φ) {z : Y}
    (hz : IsUniqueInvolution A z) : False := by
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  obtain ⟨i', R, hR, hAR⟩ := D.fundamental A hA
  have hii : i' = i := Subsingleton.elim _ _
  subst hii
  rw [hAR] at hz
  exact false_of_char2 hp2 (D.tag i') (D.rank i') (D.exp i') (D.hom i') (D.ker_le_center i') ht hn
    hR hz

theorem layer6Cen4_of_models (hL : Aut164L4 p) (hU : Aut164U4 p) :
    C25Y.Layer6Cen4 p f := by
  intro Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw hconj β hββ
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ j : Fin D.card, (D.hom j).range ≤ (D.hom i).range := by
      intro j
      rw [Subsingleton.elim j i]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hβ : β ^ 2 = 1 := by
    ext x
    simp [pow_two, hββ]
  have hexp_of : D.tag i ≠ .trialityD4 → D.exp i = f := by
    intro hne
    rcases D.exp_eq i with h | ⟨hT, -⟩
    · exact h
    · exact absurd hT hne
  have hcase : (D.tag i = .PSL ∧ D.rank i = 4 ∧ ¬ p ^ f % 4 = 1) ∨
      (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ f % 4 = 1) := by
    simp only [IsOrthTag] at hi
    rcases hi with ⟨h5, -⟩ | ⟨-, hε, ht, hn⟩ | ⟨-, hε, ht, hn⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
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
  have hker := D.ker_le_center i
  have hfund : D.tag i ≠ .trialityD4 ∧ D.tag i ≠ .G2 := by
    rcases hcase with ⟨ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] <;> simp
  have hexp : D.exp i = f := hexp_of hfund.1
  have hmain : ∃ R ∈ Generic.fundamentalSubgroups (D.tag i)
      (Generic.modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, ∃ s ∈ R,
        orderOf (D.hom i s) = 4 ∧ β (D.hom i s) = D.hom i s := by
    rcases hcase with ⟨ht, hn, h1⟩ | ⟨ht, hn, h1⟩
    · by_cases hp2 : p = 2
      · exfalso
        exact false_of_twin_char2 hp2 D hD1 i ht hn htw.hA htw.hzA
      · have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
        have hodd : Odd (p ^ f) := hpodd.pow
        have h2 : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd
        exact models_of_lie hL hU (D.tag i) (D.rank i) (D.exp i) (D.admissible i) (D.hom i) hker
          hsurj (Or.inl ⟨ht, hn, by rw [hexp]; omega⟩) β hβ
    · exact models_of_lie hL hU (D.tag i) (D.rank i) (D.exp i) (D.admissible i) (D.hom i) hker
        hsurj (Or.inr ⟨ht, hn, by rw [hexp]; exact h1⟩) β hβ
  obtain ⟨R, hR, s, hs, hord, hfix⟩ := hmain
  have hsingle := CFSG.ClassicalInvolution.RouteD.Gaps.fundamentalSingleClass_of_ne D i hfund.2
    hfund.1
  have hJ : R.map (D.hom i) ∈ Φ :=
    D.map_mem_of_single_class (fun g L hL => hconj L hL g) i hsingle hR
  refine ⟨R.map (D.hom i), hJ, D.hom i s, Subgroup.mem_map_of_mem _ hs, ?_, ?_, hfix⟩
  · have h4 : D.hom i s ^ 4 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    simpa [pow_succ, mul_assoc] using h4
  · intro h
    have h2 : orderOf (D.hom i s) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hord] at h2
    omega

end CFSG.ClassicalInvolution.ModelFacts.L6C
