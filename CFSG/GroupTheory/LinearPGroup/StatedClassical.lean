module

public import CFSG.ClassicalInvolution.Orders.Basic
public import CFSG.GH74.SectionalRank
public import CFSG.Open.StatedDefs
public import CFSG.Open.Defs

public section

namespace CFSG.LinearPGroup

open CFSG.GH74

private theorem sectionalTwoRankLE_of_statedProj
    (hGL : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] [Finite K],
      (2 : K) ≠ 0 → CFSG.GH74.SectionalTwoRankLE (GL ι K) (2 * Fintype.card ι - 1))
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (H : Subgroup (GL ι K)) {S : Type} [Group S]
    (e : S ≃* CFSG.Open.StatedProj H) :
    SectionalTwoRankLE S (2 * Fintype.card ι - 1) := by
  have hH : SectionalTwoRankLE H (2 * Fintype.card ι - 1) :=
    SectionalTwoRankLE.subgroup H (hGL ι K h2)
  have hq : SectionalTwoRankLE (CFSG.Open.StatedProj H) (2 * Fintype.card ι - 1) :=
    SectionalTwoRankLE.quotient ((CFSG.Open.StatedScalars ι K).subgroupOf H) hH
  exact SectionalTwoRankLE.of_mulEquiv e.symm hq

theorem sectionalTwoRankLE_of_statedClassicalModel
    (hGL : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] [Finite K],
      (2 : K) ≠ 0 → CFSG.GH74.SectionalTwoRankLE (GL ι K) (2 * Fintype.card ι - 1))
    {S : Type} [Group S] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hp : p ≠ 2) (h : CFSG.Open.StatedClassicalModel S t n p f) :
    (t = .PSL → SectionalTwoRankLE S (2 * n - 1)) ∧
      (t = .PSU → SectionalTwoRankLE S (2 * n - 1)) ∧
        (t = .PSp → SectionalTwoRankLE S (2 * (2 * n) - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    rw [CFSG.Open.StatedClassicalModel] at h
    obtain ⟨hadm, K, hfield, hfin, hcard, ⟨e⟩⟩ := h
    rw [CFSG.Open.StatedLieAdmissible] at hadm
    obtain ⟨hpprime, -, -⟩ := hadm
    have h2 : (2 : K) ≠ 0 :=
      @CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow K hfield hfin p f
        hpprime hp hcard
    have hbound :=
      @sectionalTwoRankLE_of_statedProj hGL (Fin n) _ _ K hfield hfin h2
        (@CFSG.Open.StatedSL n K hfield) S _ e
    simpa [Fintype.card_fin] using hbound
  · rintro rfl
    rw [CFSG.Open.StatedClassicalModel] at h
    obtain ⟨hadm, K, hfield, hfin, hcard, ⟨e⟩⟩ := h
    rw [CFSG.Open.StatedLieAdmissible] at hadm
    obtain ⟨hpprime, -, -⟩ := hadm
    have hcard' : Nat.card K = p ^ (f * 2) := by rw [hcard, pow_mul]
    have h2 : (2 : K) ≠ 0 :=
      @CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow K hfield hfin p (f * 2)
        hpprime hp hcard'
    have hbound :=
      @sectionalTwoRankLE_of_statedProj hGL (Fin n) _ _ K hfield hfin h2
        (@CFSG.Open.StatedSU n (p ^ f) K hfield) S _ e
    simpa [Fintype.card_fin] using hbound
  · rintro rfl
    rw [CFSG.Open.StatedClassicalModel] at h
    obtain ⟨hadm, K, hfield, hfin, hcard, ⟨e⟩⟩ := h
    rw [CFSG.Open.StatedLieAdmissible] at hadm
    obtain ⟨hpprime, -, -⟩ := hadm
    have h2 : (2 : K) ≠ 0 :=
      @CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow K hfield hfin p f
        hpprime hp hcard
    have hbound :=
      @sectionalTwoRankLE_of_statedProj hGL (Fin n ⊕ Fin n) _ _ K hfield hfin h2
        (@CFSG.Open.StatedSp n K hfield) S _ e
    have hcardι : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
      rw [Fintype.card_sum]
      simp [two_mul]
    simpa [hcardι] using hbound

end CFSG.LinearPGroup
