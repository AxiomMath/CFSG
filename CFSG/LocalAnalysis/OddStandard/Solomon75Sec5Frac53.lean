module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiSmall
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiTwelve
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiLarge
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCOne
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracMain

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Multi

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem frac53_large (h : Sec5Data X n z Z S) (hn : 13 ≤ n) {s : X}
    (hs : IsSec5Inv X Z s) {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) (M : AhatModel X n A)
    (hσ : fixCount (M.perm s hsA) = 4 ∨
      (transCount (M.perm s hsA) = 3 ∧ fixCount (M.perm s hsA) ≤ 3)) : False := by
  classical
  have hn8 : 8 ≤ n := by omega
  obtain ⟨u, hu, huZ, hu1, hus⟩ := h.exists_witness_Z hs hA hsA
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hs2 : s * s = 1 := hs.sq
  have hsu : s * u = u * s := hus.symm
  obtain ⟨L, E, hL, htL, M', huE, hEAL, hEcov, htE, hperm⟩ :=
    exists_Lu_model h hA huZ hu1 hu hsA hsu M
  have hbad : fixCount (M'.perm s htL) = 4 ∨
      (transCount (M'.perm s htL) = 3 ∧ fixCount (M'.perm s htL) ≤ 3) := by
    rw [hperm]; exact hσ
  have hEL : E ≤ L := fun x hx => (hEAL hx).2
  obtain ⟨Q, -, hQ2, hQ8, huQ, hQpow, -, hyQ, hQlp, hQo⟩ :=
    exists_sl23_piece hn8 hu2 hu1 hs2 hsu hL.isPCompIn hEL huE hEcov htL htE M' hbad
  have hQn : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → Q ≤ normalizer (B : Set X) :=
    fun B hB => le_normalizer_of_le_lPlus_inf hu2 hus hQlp hB.isPCompIn
  obtain ⟨d⟩ := quatPermDataM_of_multi hn h hs huZ hu1 hus hQ2 hQ8 huQ hQpow hyQ hQo hQn
  exact d.false hn

theorem frac53_multi_small_gap (hTC : Solomon75TwoComp) (h : Sec5Data X n z Z S)
    (hk : ¬ Sec5One X n Z) (hn : n ≤ 12) {s : X} (hs : IsSec5Inv X Z s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) (hsA : s ∈ normalizer (A : Set X))
    (M : AhatModel X n A)
    (hσ : fixCount (M.perm s hsA) = 4 ∨
      (transCount (M.perm s hsA) = 3 ∧ fixCount (M.perm s hsA) ≤ 3)) : False := by
  by_cases h12 : n = 12
  · exact frac53_multi_12 hTC h hk h12 hs hA hsA M hσ
  · exact frac53_multi_le11 h hk (by omega) hs hA hsA M hσ

theorem frac53_multi (hTC : Solomon75TwoComp) (h : Sec5Data X n z Z S) (hk : ¬ Sec5One X n Z)
    {s : X} (hs : IsSec5Inv X Z s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) (hsA : s ∈ normalizer (A : Set X))
    (M : AhatModel X n A)
    (hσ : fixCount (M.perm s hsA) = 4 ∨
      (transCount (M.perm s hsA) = 3 ∧ fixCount (M.perm s hsA) ≤ 3)) : False := by
  by_cases h13 : 13 ≤ n
  · exact frac53_large h h13 hs hA hsA M hσ
  · exact frac53_multi_small_gap hTC h hk (by omega) hs hA hsA M hσ

end Multi

section Leaves

theorem frac53Four_of_pieces (hTC : Solomon75TwoComp) : Solomon75Frac53Four := by
  intro X _ _ n z Z S h s hs A hA hsA M hfix
  by_cases h1 : Sec5One X n Z
  · obtain ⟨P⟩ := exists_quatPiece h h1 hs hA hsA M hfix
    obtain ⟨d⟩ := quatPermData_of_piece h h1 hs P
    exact d.false
  · exact frac53_multi hTC h h1 hs hA hsA M (Or.inl hfix)

theorem frac53Three_of_pieces (hTC : Solomon75TwoComp) : Solomon75Frac53Three := by
  intro X _ _ n z Z S h s hs A hA hsA M h3 hf
  have hn : 8 ≤ n := h.maxdeg.1
  by_cases h1 : Sec5One X n Z
  · have hσ2 := perm_sq_eq_one hn M hsA hs.sq
    have hsign := sign_perm_eq_one_of_sec5One h h1 hs hA hsA M
    rw [sign_eq_neg_one_of_transCount_three hσ2 h3] at hsign
    exact absurd hsign (by decide)
  · exact frac53_multi hTC h h1 hs hA hsA M (Or.inr ⟨h3, hf⟩)

theorem solomon75Frac53_of_twoComp (hTC : Solomon75TwoComp) : Solomon75Frac53 :=
  frac53 ⟨frac53Four_of_pieces hTC, frac53Three_of_pieces hTC⟩

end Leaves

end CFSG.OddStandard.Solomon75
