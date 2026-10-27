module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.StronglyEmbedded.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public section

noncomputable section

namespace CFSG.ClassicalModels

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.External

theorem projectiveSpecialLinear_two_card_of_card_four
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) = 60 := by
  let _ := Fintype.ofFinite K
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  have hcenter := huppert614_card_center_of_neg_one_eq_one (K := K) (CharTwo.neg_eq 1)
  have hcard := huppert614_card_psl_mul_center (K := K)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

theorem projectiveSpecialLinear_two_card_of_card_five
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) = 60 := by
  let _ := Fintype.ofFinite K
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fact (2 < 5) := ⟨by norm_num⟩
  let _ : CharP K 5 := charP_of_card_eq_prime_pow (p := 5) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hcenter := huppert614_card_center_of_neg_one_ne_one (K := K)
    (CharP.neg_one_ne_one K 5)
  have hcard := huppert614_card_psl_mul_center (K := K)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  omega

theorem nonempty_statedLinearModel_equiv_alternating_five
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 5) :
    Nonempty (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ≃* alternatingGroup (Fin 5)) := by
  have h22 : (2 : ℕ) ≠ 2 ∨ Nat.card K ≠ 2 := Or.inr (by rcases hK with h | h <;> omega)
  have h23 : (2 : ℕ) ≠ 2 ∨ Nat.card K ≠ 3 := Or.inr (by rcases hK with h | h <;> omega)
  let _ := huppert_II_6_13 (K := K) 2 le_rfl h22 h23
  have hcard : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) = 60 := by
    rcases hK with h | h
    · exact projectiveSpecialLinear_two_card_of_card_four K h
    · exact projectiveSpecialLinear_two_card_of_card_five K h
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five hcard
  exact ⟨(CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans e⟩

theorem statedClassicalModel_PSL_inCatalog_of_card_four_or_five
    (G : Type) [Group G] (p f : ℕ)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f)
    (hq : p ^ f = 4 ∨ p ^ f = 5) : CFSG.Assembly.InCatalog G := by
  obtain ⟨K, hfield, hfinite, hKcard, ⟨e⟩⟩ := h.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e5⟩ := nonempty_statedLinearModel_equiv_alternating_five K (hKcard ▸ hq)
  exact ⟨.alternating 5 le_rfl, ⟨e.trans e5⟩⟩

end CFSG.ClassicalModels
