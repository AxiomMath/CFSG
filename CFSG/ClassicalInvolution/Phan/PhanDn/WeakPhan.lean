module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Family
public import CFSG.ClassicalInvolution.RouteD.Entries
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

private theorem routeD_dAdj_iff_edgeD {n : ℕ} (_hn : 4 ≤ n) (i j : Fin n) :
    CFSG.ClassicalInvolution.RouteD.DAdj n i j ↔ edgeD n i j ∨ edgeD n j i := by
  have hadj : ∀ {a b : Fin n}, edgeD n a b → CFSG.ClassicalInvolution.RouteD.DAdj n a b := by
    intro a b h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hb : b.val + 2 < n
      · exact Or.inl ⟨h1, hb⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr h2⟩))
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by
        unfold edgeD
        left
        exact ⟨h1, by omega⟩)
    · exact Or.inr (by
        unfold edgeD
        left
        exact ⟨h1, by omega⟩)
    · rcases h2 with h2 | h2
      · exact Or.inl (by
          unfold edgeD
          left
          exact ⟨by omega, by omega⟩)
      · exact Or.inl (by
          unfold edgeD
          right
          exact ⟨h1, h2⟩)
    · rcases h2 with h2 | h2
      · exact Or.inr (by
          unfold edgeD
          left
          exact ⟨by omega, by omega⟩)
      · exact Or.inr (by
          unfold edgeD
          right
          exact ⟨h1, h2⟩)
  · rintro (h | h)
    · exact hadj h
    · exact (CFSG.ClassicalInvolution.RouteD.DAdj_symm i j).2 (hadj h)

theorem ggCoxeterMatrixD_eq_three_iff {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    CFSG.StandardType.ggCoxeterMatrixD n i j = 3 ↔ edgeD n i j ∨ edgeD n j i := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    constructor
    · intro h
      omega
    · rintro (h | h)
      · exact absurd h (edgeD_irrefl n i)
      · exact absurd h (edgeD_irrefl n i)
  · rw [if_neg hij]
    by_cases hD : CartanMatrix.D n i j = 0
    · rw [if_pos hD]
      constructor
      · intro h
        omega
      · rintro (h | h)
        · exact absurd ((routeD_dAdj_iff_edgeD hn i j).2 (Or.inl h))
            ((CFSG.ClassicalInvolution.RouteD.D_eq_zero_iff i j).1 hD).2
        · exact absurd ((routeD_dAdj_iff_edgeD hn i j).2 (Or.inr h))
            ((CFSG.ClassicalInvolution.RouteD.D_eq_zero_iff i j).1 hD).2
    · rw [if_neg hD]
      have hDAdj : CFSG.ClassicalInvolution.RouteD.DAdj n i j := by
        by_contra h
        exact hD ((CFSG.ClassicalInvolution.RouteD.D_eq_zero_iff i j).2 ⟨hij, h⟩)
      exact ⟨fun _ => (routeD_dAdj_iff_edgeD hn i j).1 hDAdj, fun _ => rfl⟩

theorem ggCoxeterMatrixD_eq_two_iff {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    CFSG.StandardType.ggCoxeterMatrixD n i j = 2 ↔
      i ≠ j ∧ ¬ edgeD n i j ∧ ¬ edgeD n j i := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    constructor
    · intro h
      omega
    · rintro ⟨h, -⟩
      exact absurd rfl h
  · rw [if_neg hij]
    by_cases hD : CartanMatrix.D n i j = 0
    · rw [if_pos hD]
      have hne : ¬ CFSG.ClassicalInvolution.RouteD.DAdj n i j :=
        ((CFSG.ClassicalInvolution.RouteD.D_eq_zero_iff i j).1 hD).2
      constructor
      · intro _
        refine ⟨hij, ?_, ?_⟩
        · intro h
          exact hne ((routeD_dAdj_iff_edgeD hn i j).2 (Or.inl h))
        · intro h
          exact hne ((routeD_dAdj_iff_edgeD hn i j).2 (Or.inr h))
      · intro _
        rfl
    · rw [if_neg hD]
      constructor
      · intro h
        omega
      · rintro ⟨-, h1, h2⟩
        exact absurd ((CFSG.ClassicalInvolution.RouteD.D_eq_zero_iff i j).2
          ⟨hij, fun hd => Or.elim ((routeD_dAdj_iff_edgeD hn i j).1 hd) h1 h2⟩) hD

theorem _root_.CFSG.ClassicalInvolution.Phan.WeakPhanSL.exists_phanFamilyD {n : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = (p ^ f) ^ 2)
    {X : Type} [Group X] {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}
    (h : CFSG.ClassicalInvolution.Phan.WeakPhanSL K p f (CFSG.StandardType.ggCoxeterMatrixD n)
      U W) :
    ∃ F : PhanFamilyD K p f n X, (∀ i, (F.ι i).range = U i) ∧
      (∀ i, Function.Injective (F.ι i)) ∧
      ∀ i j (h : edgeD n i j), (F.θ i j h).ker ≤ Subgroup.center (Su K p f 3) := by
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij h1 h2 a ha b hb
    exact h.comm i j ((ggCoxeterMatrixD_eq_two_iff hn i j).2 ⟨hij, h1, h2⟩) a ha b hb
  have hpair' : ∀ i j : Fin n, edgeD n i j →
      UnitaryBlockStandardPair K p f (W i j) (U i) (U j) :=
    fun i j hj => h.pair i j ((ggCoxeterMatrixD_eq_three_iff hn i j).2 (Or.inl hj))
  obtain ⟨F, hrange, hinj, hker, -⟩ := exists_family hn hK U W hcomm' hpair'
  exact ⟨F, hrange, hinj, hker⟩

end CFSG.ClassicalInvolution.PhanDn
