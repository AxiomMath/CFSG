module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixCases
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Transitive

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix DeltaLocal

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace DeltaLocal.Six

omit [Finite G] in
theorem exists_third {r : ℕ} (hr : 3 ≤ r) (j k : Fin r) : ∃ l : Fin r, l ≠ j ∧ l ≠ k := by
  by_contra h
  push Not at h
  have hv : ∀ a : ℕ, (ha : a < r) → a = j.val ∨ a = k.val := by
    intro a ha
    by_cases haj : (⟨a, ha⟩ : Fin r) = j
    · exact Or.inl (congrArg Fin.val haj)
    · exact Or.inr (congrArg Fin.val (h ⟨a, ha⟩ haj))
  have h0 := hv 0 (by omega)
  have h1 := hv 1 (by omega)
  have h2 := hv 2 (by omega)
  omega

end DeltaLocal.Six

theorem lemma_6_6 (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar)
    (hΔ : (deltaConjugates (Subgroup.normalizer (D : Set G))).Nonempty) (i : Fin r) :
    2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) := by
  by_contra hlt
  push Not at hlt
  have hri : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1 := by omega
  have hrank : ∀ j, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar j)) ≤ 1 := by
    intro j
    obtain ⟨h, -, hij⟩ := lemma_6_3 h3 hin hC i j
    rw [← hij, Conj.pRank_map (MulAut.conj h) (by norm_num)]
    exact hri
  obtain ⟨K, g, rfl, hg, U, hU⟩ := hΔ
  have hpairs := fun j => RankOne.exists_q8Pair_of_rank_one hC hin hg hU j (hrank j)
  choose p q hP using hpairs
  have hP' : ∀ j, Six.PairAt D U Abar j (p j) (q j) := hP
  have hr2 := two_le hC
  rcases (show r = 2 ∨ 3 ≤ r by omega) with hr | hr
  · subst hr
    by_cases hz : p 0 ^ 2 = p 1 ^ 2
    · exact Six.caseShared2 hC hrank hP' hz
    · exact Six.caseTwo hC hin hg hU hrank hP' hz
  by_cases hsh : ∃ j k : Fin r, j ≠ k ∧ p j ^ 2 = p k ^ 2
  · obtain ⟨j, k, hjk, hz⟩ := hsh
    obtain ⟨l, hlj, hlk⟩ := Six.exists_third hr j k
    exact Six.caseSharedRank hC hin hg hU hrank hP' hjk (Ne.symm hlj) (Ne.symm hlk) hz
  push Not at hsh
  set i0 : Fin r := ⟨0, by omega⟩ with hi0
  set i1 : Fin r := ⟨1, by omega⟩ with hi1
  set i2 : Fin r := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := fun h => absurd (congrArg Fin.val h) (by simp [hi0, hi1])
  have h02 : i0 ≠ i2 := fun h => absurd (congrArg Fin.val h) (by simp [hi0, hi2])
  have h12 : i1 ≠ i2 := fun h => absurd (congrArg Fin.val h) (by simp [hi1, hi2])
  rcases Nat.even_or_odd r with hev | hodd
  · have hr4 : 4 ≤ r := by
      obtain ⟨t, ht⟩ := hev
      omega
    set i3 : Fin r := ⟨3, by omega⟩ with hi3
    have h03 : i0 ≠ i3 := fun h => absurd (congrArg Fin.val h) (by simp [hi0, hi3])
    have h13 : i1 ≠ i3 := fun h => absurd (congrArg Fin.val h) (by simp [hi1, hi3])
    have h23 : i2 ≠ i3 := fun h => absurd (congrArg Fin.val h) (by simp [hi2, hi3])
    have hne1 : ∀ m, p m ^ 2 ≠ 1 := fun m => (hP' m).1.2.2.2
    by_cases hprod : p i2 ^ 2 = p i0 ^ 2 * p i1 ^ 2
    · refine Six.caseCentralRank hC hin hg hU hrank hP' h01 h03 h13 (hsh _ _ h01) ?_
      intro hmem
      rcases hmem with h | h | h | h
      · exact hne1 i3 h
      · exact hsh _ _ (Ne.symm h03) h
      · exact hsh _ _ (Ne.symm h13) h
      · exact hsh _ _ (Ne.symm h23) (h.trans hprod.symm)
    · refine Six.caseCentralRank hC hin hg hU hrank hP' h01 h02 h12 (hsh _ _ h01) ?_
      intro hmem
      rcases hmem with h | h | h | h
      · exact hne1 i2 h
      · exact hsh _ _ (Ne.symm h02) h
      · exact hsh _ _ (Ne.symm h12) h
      · exact hprod h
  · exact Six.caseOdd hC hin hg hU hrank hP' hodd h01 h02 h12 (hsh _ _ h01)

end CFSG.ComponentClassification.AschbacherTheorem5
