module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Holds
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Four
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwoLow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.RankThree.Classical2 CFSG.Timmesfeld
open scoped MatrixGroups


private theorem exists_sl2_orderOf {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hq : q.Prime) (hqK : q ∣ Nat.card K - 1 ∨ Nat.card K = 2 ∧ q = 3) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 2) K, c ^ q = 1 ∧ c ≠ 1 := by
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 (k := K) hq (by
    rcases hqK with h | ⟨hcard, rfl⟩
    · rw [← Nat.one_pow 2, Nat.sq_sub_sq]
      exact h.mul_left _
    · rw [hcard]
      norm_num)
  refine ⟨c, hc ▸ pow_orderOf_eq_one c, fun h1 => hq.ne_one ?_⟩
  rw [← hc, h1, orderOf_one]

private def e8D4Leaf : Fin 3 → Fin 8 := ![4, 6, 7]

private def e8D4LeafIdx : Fin 3 → Fin 4 := ![0, 2, 3]

private theorem e8D4Leaf_natAdd (i : Fin 3) : Fin.natAdd 4 (e8D4LeafIdx i) = e8D4Leaf i := by
  fin_cases i <;> rfl

private theorem e8D4Leaf_ne (i j : Fin 3) (hij : i ≠ j) : e8D4Leaf i ≠ e8D4Leaf j := by
  intro h
  apply hij
  revert h
  fin_cases i <;> fin_cases j <;> decide

private theorem e8D4Leaf_nadj (i j : Fin 3) (hij : i ≠ j) :
    ¬ edgeD 8 (e8D4Leaf i) (e8D4Leaf j) ∧ ¬ edgeD 8 (e8D4Leaf j) (e8D4Leaf i) := by
  revert hij
  fin_cases i <;> fin_cases j <;> decide

theorem exists_elemAbelian_e8D4Perp (K : Type) [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hq : q.Prime) (hqK : q ∣ Nat.card K - 1 ∨ Nat.card K = 2 ∧ q = 3) :
    ∃ F : Subgroup (adjointGroup .E8 K), F ≤ e8D4Perp K ∧ CFSG.Open.IsElemAbelian q F ∧
      Nat.card F = q ^ 3 ∧ 3 ≤ CFSG.Open.pRank q F := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨c, hcp, hc1⟩ := exists_sl2_orderOf (K := K) hq hqK
  obtain ⟨ρ, hρ, hcomm, -⟩ := exists_e8D8_family_param K
  have hleaf : ∀ i : Fin 3, ρ (e8D4Leaf i) c ∈ e8D4Levi K := by
    intro i
    have hmem : ρ (e8D4Leaf i) c ∈ e8D8Chain K (e8D4Leaf i) := by
      rw [← (hρ (e8D4Leaf i)).2]
      exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
    refine (le_iSup (fun j : Fin 4 => e8D8Chain K (Fin.natAdd 4 j)) (e8D4LeafIdx i)) ?_
    rwa [e8D4Leaf_natAdd]
  have hcomm' : ∀ i j : Fin 3, i ≠ j → ∀ A B,
      Commute (ρ (e8D4Leaf i) A) (ρ (e8D4Leaf j) B) := by
    intro i j hij A B
    have h1 : ρ (e8D4Leaf i) A ∈ e8D8Chain K (e8D4Leaf i) := by
      rw [← (hρ (e8D4Leaf i)).2]
      exact MonoidHom.mem_range.mpr ⟨A, rfl⟩
    have h2 : ρ (e8D4Leaf j) B ∈ e8D8Chain K (e8D4Leaf j) := by
      rw [← (hρ (e8D4Leaf j)).2]
      exact MonoidHom.mem_range.mpr ⟨B, rfl⟩
    obtain ⟨hne1, hne2⟩ := e8D4Leaf_nadj i j hij
    exact hcomm _ _ (e8D4Leaf_ne i j hij) hne1 hne2 _ h1 _ h2
  obtain ⟨E, hEea, hEcard, hEmax⟩ := exists_elemAbelian_pow_of_commuting_sl2 c hcp hc1
    (fun i => ρ (e8D4Leaf i)) (fun i => (hρ (e8D4Leaf i)).1) hcomm'
  have hEle : E ≤ e8D4Levi K := hEmax (e8D4Levi K) hleaf
  refine ⟨E.map (MulAut.conj (weylWordElt .E8 K e8D4Word)).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [show e8D4Perp K = (e8D4Levi K).map
        (MulAut.conj (weylWordElt .E8 K e8D4Word)).toMonoidHom from rfl]
    exact Subgroup.map_mono hEle
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map q hEea _
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hEcard]
  · exact (CFSG.SectionRank.le_pRank (p := q) hq.one_lt (le_refl _) hEea hEcard).trans
      (CFSG.SectionRank.pRank_le_map (p := q) hq.one_lt _ (MulEquiv.injective _) E)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
