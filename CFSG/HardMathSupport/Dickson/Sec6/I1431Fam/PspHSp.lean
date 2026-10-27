module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHBasic
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem t6psph_sqOK_statedSp {K : Type} [Field K] [Finite K] {s : ℕ} (hs : 1 ≤ s) {q : ℕ}
    (hq : 10 ≤ q) : t6psph_SqOK q ↥(StatedSp s K) := by
  by_cases hQ : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s)
  · exact t6psph_sqOK_of_commutator_eq_top
      (Group.isPerfect_def.mp (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hQ).1)
  · refine t6psph_sqOK_of_card_lt hq ?_
    have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
    have hK4 : Nat.card K < 4 := by
      by_contra h
      exact hQ (Or.inl (Or.inr (by omega)))
    have h3 : Nat.card K = 3 → s < 2 := fun h => by
      by_contra h'
      exact hQ (Or.inr (Or.inl ⟨h, by omega⟩))
    have h2 : Nat.card K = 2 → s < 3 := fun h => by
      by_contra h'
      exact hQ (Or.inr (Or.inr ⟨h, by omega⟩))
    have hcard := SymplecticFlag.card_statedSp (K := K) s
    have hle : Nat.card ↥(commutator ↥(StatedSp s K)) ≤ Nat.card ↥(StatedSp s K) :=
      Subgroup.card_le_card_group _
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
    · rcases (show s = 1 ∨ s = 2 by have := h2 hK; omega) with rfl | rfl
      · have h6 : Nat.card ↥(StatedSp 1 K) = 6 := by
          rw [hcard, hK]
          norm_num [Finset.Icc_self]
        omega
      · have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
        obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK
          (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
          (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
        let e₀ : StatedSp 2 K ≃* sesqUnitaryGroup (CFSG.RankThree.Classical.spForm 2 K) :=
          (MonoidHom.ofInjective
            (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
            (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
        obtain ⟨⟨eA⟩, -⟩ := CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour
          (e₀.trans E)
        have h360 : Nat.card ↥(commutator ↥(StatedSp 2 K)) = 360 := by
          rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
          simp [Nat.card_eq_fintype_card, Nat.factorial]
        omega
    · have hs1 : s = 1 := by have := h3 hK; omega
      subst hs1
      have h24 : Nat.card ↥(StatedSp 1 K) = 24 := by
        rw [hcard, hK]
        norm_num [Finset.Icc_self]
      omega

theorem t6psph_sqOK_sesqUnitaryAlt {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [Nontrivial W] {B : LinearMap.BilinForm K W}
    (hB : B.IsAlt) (hn : B.Nondegenerate) {q : ℕ} (hq : 10 ≤ q) :
    t6psph_SqOK q ↥(sesqUnitaryGroup B) := by
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hs1 : 1 ≤ s := by
    have := Module.finrank_pos (R := K) (M := W)
    omega
  exact t6psph_sqOK_of_mulEquiv e (t6psph_sqOK_statedSp hs1 hq)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
