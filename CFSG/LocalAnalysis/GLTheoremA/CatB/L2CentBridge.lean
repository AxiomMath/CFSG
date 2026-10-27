module

public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsAlternating
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10 Matrix
open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels TauCeti

theorem l2c_valid_A1 {n : ℕ} (hn : 3 ≤ n) :
    (LieTypeIndex.A 1 ⟨2, n, Nat.prime_two, by omega⟩).Valid := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, PrimePower.card_def]
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

theorem l2c_isTypeL2_of_catalog {S : Type} [Group S] [Finite S] {n : ℕ}
    (h : catalogIs S (isL2n n)) :
    1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (S ≃* StatedProj (StatedSL 2 F)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isL2n] at hi
  | sporadic s => simp [isL2n] at hi
  | alternating k hk =>
    simp only [isL2n] at hi
    obtain ⟨rfl, rfl⟩ := hi
    have hF : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    refine ⟨by norm_num, GaloisField 2 2, inferInstance, inferInstance, hF, ⟨?_⟩⟩
    exact e.trans ((CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five.some.symm).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)))
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · simp [isL2n] at hi
      · simp only [isL2n] at hi
        obtain ⟨hp2, hn⟩ := hi
        have hpos : 0 < q.exponent := q.exponent_pos
        haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
        have hF : Nat.card (GaloisField q.p q.exponent) = 2 ^ n := by
          rw [GaloisField.card q.p q.exponent hpos.ne', hp2, hn]
        refine ⟨hn ▸ hpos, GaloisField q.p q.exponent, inferInstance, inferInstance, hF, ⟨?_⟩⟩
        exact e.trans ((linearCatalogCandidateEquivPSL 1 q hv).trans
          (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField q.p q.exponent)))
      · simp [isL2n] at hi
    | _ => simp [isL2n] at hi

theorem l2c_catalog_of_iso {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (e : S ≃* StatedProj (StatedSL 2 F)) : catalogIs S (isL2n n) := by
  have hpos : 0 < n := by omega
  have e' : S ≃* ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.trans (statedLinearModelEquivGaloisPSL F 2 2 n hpos hF)
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    refine ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num), ⟨rfl, rfl⟩, ⟨?_⟩⟩
    exact e.trans ((statedLinearModelEquivGaloisPSL F 2 2 2 hpos hF).trans
      (CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five).some)
  · have hv := l2c_valid_A1 h3
    refine ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ⟨2, n, Nat.prime_two, by omega⟩, hv⟩, ⟨rfl, rfl⟩, ⟨?_⟩⟩
    exact e'.trans (linearCatalogCandidateEquivPSL 1 ⟨2, n, Nat.prime_two, by omega⟩ hv).symm

end CFSG.LocalAnalysis.GLTheoremA
