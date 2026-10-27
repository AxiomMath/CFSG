module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Matrix Subgroup
open scoped MatrixGroups

theorem natCard_quot_pCore_eq_one_of_isPGroup {p : ℕ} {H : Type*} [Group H]
    (hp : IsPGroup p H) : Nat.card (H ⧸ CFSG.pCore p H) = 1 := by
  have htop : CFSG.pCore p H = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
  rw [htop]
  exact Subgroup.index_top

theorem not_dvd_card_GL_of_le_one {p n : ℕ} [Fact p.Prime] (hn : n ≤ 1) :
    ¬ p ∣ Nat.card (GL (Fin n) (ZMod p)) := by
  interval_cases n
  · rw [Matrix.card_GL_field, ZMod.card]
    simp only [Fin.prod_univ_zero, Nat.dvd_one]
    exact (Fact.out : p.Prime).one_lt.ne'
  · rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_one]
    simp only [Fin.val_zero, pow_one, pow_zero]
    intro h
    have h1 : p ∣ 1 := by
      have h2 : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) h
      rwa [Nat.sub_sub_self (Fact.out : p.Prime).one_le] at h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)

theorem eq_one_of_orderOf_eq_primePow_of_le_one {p n : ℕ} [Fact p.Prime] (hn : n ≤ 1)
    {x : GL (Fin n) (ZMod p)} {k : ℕ} (hk : orderOf x = p ^ k) : x = 1 := by
  have hdvd : p ^ k ∣ Nat.card (GL (Fin n) (ZMod p)) := hk ▸ orderOf_dvd_natCard x
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      exact not_dvd_card_GL_of_le_one hn (dvd_trans (dvd_pow_self p h.ne') hdvd)
  have hord : orderOf x = 1 := by rw [hk, hk0, pow_zero]
  exact orderOf_eq_one_iff.mp hord

theorem eq_bot_of_oPPrimeHull_eq_of_forall_primePow_order {p n : ℕ} [Fact p.Prime]
    (h : ∀ x : GL (Fin n) (ZMod p), ∀ k : ℕ, orderOf x = p ^ k → x = 1)
    {H : Subgroup (GL (Fin n) (ZMod p))} (hH : oPPrimeHull p H = H) : H = ⊥ := by
  rw [← hH, oPPrimeHull]
  refine le_bot_iff.mp (Subgroup.closure_le _ |>.mpr ?_)
  rintro x ⟨-, k, hk⟩
  simpa using h x k hk

theorem isIrreducibleMatrixRep_statedSL_two (p : ℕ) [Fact p.Prime] :
    CFSG.RepresentationTheory.IsIrreducibleMatrixRep
      (CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p)).subtype := by
  intro W hW
  have hW' : ∀ A ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p), ∀ w ∈ W,
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w ∈ W := by
    intro A hA w hw
    exact hW ⟨A, hA⟩ w hw
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.eq_bot_or_eq_top_of_forall_mulVec_mem
    W.toAddSubgroup hW' with h | h
  · left
    refine le_bot_iff.mp fun x hx => ?_
    have hx' : x ∈ W.toAddSubgroup := hx
    rw [h] at hx'
    exact AddSubgroup.mem_bot.mp hx'
  · right
    refine top_le_iff.mp fun x hx => ?_
    have hx' : x ∈ (⊤ : AddSubgroup (Fin 2 → ZMod p)) := by simpa using hx
    rw [← h] at hx'
    exact hx'

theorem sLTwoOrTrivialAt (p : ℕ) [Fact p.Prime] : SLTwoOrTrivialAt p := by
  intro H hH
  set S : Set (GL (Fin 2) (ZMod p)) := {x | x ∈ H ∧ orderOf x = p} with hS
  have hSorder : ∀ x ∈ S, orderOf x = p := fun x hx => hx.2
  have hgen : H = Subgroup.closure S := by
    refine le_antisymm ?_ (Subgroup.closure_le _ |>.mpr fun x hx => hx.1)
    rw [← hH, oPPrimeHull]
    refine Subgroup.closure_le _ |>.mpr fun x hx => ?_
    obtain ⟨hxH, k, hk⟩ := hx
    have hk1 : k ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ k := by omega
      exact CFSG.RankThree.SubgroupLists.not_sq_dvd_card_GL_two
        ((pow_dvd_pow p h2).trans (hk ▸ orderOf_dvd_natCard x))
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hx1]
      exact Subgroup.one_mem (Subgroup.closure S)
    · have hk1' : k = 1 := by omega
      exact Subgroup.subset_closure (show x ∈ S from by
        rw [hS]; exact ⟨hxH, by rw [hk, hk1', pow_one]⟩)
  rcases CFSG.RankThree.SubgroupLists.dickson_gl_two_closure S hSorder with hbot | hpc | hSL
  · right
    have hHbot : H = ⊥ := hgen.trans hbot
    have hpgroup : IsPGroup p ↥H := IsPGroup.of_card (G := ↥H) (n := 0)
      (by rw [hHbot, Subgroup.card_bot, pow_zero])
    exact natCard_quot_pCore_eq_one_of_isPGroup (p := p) (H := ↥H) hpgroup
  · right
    have hHcard : Nat.card ↥H = p := hgen ▸ hpc
    have hpgroup : IsPGroup p ↥H :=
      IsPGroup.of_card (G := ↥H) (n := 1) (by simpa using hHcard)
    exact natCard_quot_pCore_eq_one_of_isPGroup (p := p) (H := ↥H) hpgroup
  · left
    have hHSL : H = CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p) := hgen.trans hSL
    have hpcdot : CFSG.pCore p ↥H = ⊥ := by
      rw [hHSL]
      exact pCore_eq_bot_of_isIrreducibleMatrixRep
        (H := CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p))
        (isIrreducibleMatrixRep_statedSL_two p)
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hpcdot).trans ?_⟩
    exact (QuotientGroup.quotientBot (G := ↥H)).trans
      ((MulEquiv.subgroupCongr hHSL).trans
        (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 (ZMod p)))

theorem matrixListAt_of_le_one {p n : ℕ} [Fact p.Prime] (hn : n ≤ 1) : MatrixListAt p n := by
  unfold MatrixListAt
  intro H hH
  have hHbot : H = ⊥ := eq_bot_of_oPPrimeHull_eq_of_forall_primePow_order
    (fun x k hk => eq_one_of_orderOf_eq_primePow_of_le_one hn hk) hH
  have hpgroup : IsPGroup p ↥H := IsPGroup.of_card (G := ↥H) (n := 0)
    (by rw [hHbot, Subgroup.card_bot, pow_zero])
  exact Or.inl (Or.inr (Or.inr (Or.inr
    (natCard_quot_pCore_eq_one_of_isPGroup (p := p) (H := ↥H) hpgroup))))

theorem matrixListAt_of_le_two {p n : ℕ} [Fact p.Prime] (hn : n ≤ 2) : MatrixListAt p n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact matrixListAt_of_le_one (by omega)
  · have hn2 : n = 2 := by omega
    rw [hn2]
    unfold MatrixListAt
    intro H hH
    rcases sLTwoOrTrivialAt p H hH with hSL | h1
    · exact Or.inl (Or.inl hSL)
    · exact Or.inl (Or.inr (Or.inr (Or.inr h1)))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
