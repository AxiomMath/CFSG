module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapEnd
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Tori

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus plusIndexEquiv minusIndexEquiv)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Generic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

theorem pairPerpOf_inf_pairPerpOf (ha : IsHypCoord Q a a') :
    pairPerpOf Q a a' ⊓ pairPerpOf Q b b' = stabPairsBar Q a a' b b' := by
  rw [pairPerpOf, pairPerpOf, stabPairsBar,
    ← Subgroup.map_inf_eq _ _ _ (projHom_injective ha.exists_ne_zero)]
  rfl

theorem perfectCore_pairPerpOf_inf_centralizer_pairTorusOf (hq : 4 ≤ Nat.card K)
    (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hperf : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b') :
    perfectCore (pairPerpOf Q a a' ⊓ centralizer (pairTorusOf Q b b' : Set _)) =
      stabPairsBar Q a a' b b' := by
  have hC := hb.centralizer_pairTorusOf hq
  have hinter := pairPerpOf_inf_pairPerpOf (b := b) (b' := b') ha
  have hDbC : pairPerpOf Q b b' ≤ centralizer (pairTorusOf Q b b' : Set _) := by
    rw [hC]
    exact le_sup_right
  apply le_antisymm
  ·
    set H := pairPerpOf Q a a' ⊓ centralizer (pairTorusOf Q b b' : Set _) with hH
    have hcomm : ⁅H, H⁆ ≤ stabPairsBar Q a a' b b' := by
      rw [← hinter]
      refine le_inf ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le.2 fun x hx y hy => mul_mem (mul_mem (mul_mem hx hy)
          (inv_mem hx)) (inv_mem hy))) ?_
      have hXab : ∀ x ∈ pairTorusOf Q b b', ∀ y ∈ pairTorusOf Q b b', x * y = y * x := by
        have hle := F4Pilot.le_centralizer_self_of_isCyclic hb.isCyclic_pairTorusOf
        intro x hx y hy
        exact mem_centralizer_iff.1 (hle hy) x hx
      have hXN : pairTorusOf Q b b' ≤ normalizer (pairPerpOf Q b b' : Set _) :=
        hb.pairTorusOf_le_centralizer_pairPerpOf.trans (centralizer_le_normalizer _)
      have hHle : H ≤ pairTorusOf Q b b' ⊔ pairPerpOf Q b b' := hC ▸ inf_le_right
      exact (Subgroup.commutator_mono hHle hHle).trans
        (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer hXab hXN)
    have hpc := CFSG.Quasithin.perfectCore_perfect H
    rw [← hpc]
    exact (Subgroup.commutator_mono (perfectCore_le H) (perfectCore_le H)).trans hcomm
  · refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf ?_ ?_) hperf
    · rw [← hinter]
      exact inf_le_left
    · rw [← hinter]
      exact inf_le_right.trans hDbC

end Generic

theorem exists_ne_ne_ne_fin {n : ℕ} (hn : 4 ≤ n) (i j k : Fin n) :
    ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  classical
  obtain ⟨l, -, hl⟩ : ∃ l ∈ (Finset.univ : Finset (Fin n)), l ∉ ({i, j, k} : Finset (Fin n)) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      have h1 := Finset.card_insert_le i ({j, k} : Finset (Fin n))
      have h2 := Finset.card_insert_le j ({k} : Finset (Fin n))
      rw [Finset.card_singleton] at h2
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  exact ⟨l, fun h => hl (by simp [h]), fun h => hl (by simp [h]), fun h => hl (by simp [h])⟩

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {Y : Type*} [Group Y] {D : Subgroup Y}
    (hq : CFSG.IsQuasisimple D) (hZ : center D = ⊥) : IsSimpleGroup D := by
  have : IsSimpleGroup (D ⧸ center D) := hq.2.1
  exact ((QuotientGroup.quotientBot (G := D)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem plusOverlap_eq_stabTwoBar (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) : plusOverlap (K := K) a b = stabTwoBar K a b := by
  have hqs := isQuasisimple_stabTwoBar (K := K) hn hab
  exact perfectCore_pairPerpOf_inf_centralizer_pairTorusOf hq (isHypCoord_coordinateQuadPlus a)
    (isHypCoord_coordinateQuadPlus b) (isPerfect_iff.mp hqs.1.1)

theorem isSimpleGroup_plusOverlap (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) : IsSimpleGroup (plusOverlap (K := K) a b) := by
  rw [plusOverlap_eq_stabTwoBar hq hn hab]
  obtain ⟨hqs, hZ⟩ := isQuasisimple_stabTwoBar (K := K) hn hab
  exact isSimpleGroup_of_isQuasisimple_of_center_eq_bot hqs hZ

theorem center_plusOverlap_eq_bot (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) : center (plusOverlap (K := K) a b) = ⊥ := by
  rw [plusOverlap_eq_stabTwoBar hq hn hab]
  exact (isQuasisimple_stabTwoBar (K := K) hn hab).2

theorem pairPerp_inf_pairPerp (a b : Fin n) :
    pairPerp (K := K) a ⊓ pairPerp b = stabTwoBar K a b :=
  pairPerpOf_inf_pairPerpOf (isHypCoord_coordinateQuadPlus a)

theorem exists_ne_one_mem_plusOverlap_triple (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {o k l : Fin n}
    (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) : ∃ x, x ≠ 1 ∧
      x ∈ plusOverlap (K := K) o k ∧ x ∈ plusOverlap (K := K) o l ∧
        x ∈ plusOverlap (K := K) k l := by
  obtain ⟨j, hjo, hjk, hjl⟩ := exists_ne_ne_ne_fin (by omega) o k l
  have hne : pairTorus (K := K) j ≠ ⊥ :=
    ne_bot_of_one_lt_card (by rw [card_pairTorus]; omega)
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hmem : ∀ {a b : Fin n}, a ≠ b → j ≠ a → j ≠ b → x ∈ plusOverlap (K := K) a b :=
    fun hab hja hjb => by
      rw [plusOverlap_eq_stabTwoBar hq hn hab, ← pairPerp_inf_pairPerp]
      exact ⟨pairTorus_le_pairPerp (Ne.symm hja) hx, pairTorus_le_pairPerp (Ne.symm hjb) hx⟩
  exact ⟨x, hx1', hmem hok hjo hjk, hmem hol hjo hjl, hmem hkl hjk hjl⟩

end Plus

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem minusPairTorus_le_stabPairsBar (hn : 1 ≤ n) (b c : K) {a a' j : Fin (n - 1)}
    (hja : j ≠ a) (hja' : j ≠ a') :
    minusPairTorus (K := K) hn b c j ≤ stabPairsBar (coordinateQuadMinus n K hn b c)
      (minusIndexEquiv n hn (.inl a)) (minusIndexEquiv n hn (.inr (.inl a)))
      (minusIndexEquiv n hn (.inl a')) (minusIndexEquiv n hn (.inr (.inl a'))) := by
  have hinj := (minusIndexEquiv n hn).injective
  refine Subgroup.map_mono fun x hx => ?_
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨u, hu⟩ := hx
  rw [← hu]
  have hne : ∀ {i : Fin (n - 1)}, j ≠ i →
      minusIndexEquiv n hn (.inl i) ≠ minusIndexEquiv n hn (.inl j) ∧
      minusIndexEquiv n hn (.inl i) ≠ minusIndexEquiv n hn (.inr (.inl j)) ∧
      minusIndexEquiv n hn (.inr (.inl i)) ≠ minusIndexEquiv n hn (.inl j) ∧
      minusIndexEquiv n hn (.inr (.inl i)) ≠ minusIndexEquiv n hn (.inr (.inl j)) := by
    intro i hji
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := hinj h
      simp only [Sum.inl.injEq] at this
      exact hji this.symm
    · exact absurd (hinj h) (by simp)
    · exact absurd (hinj h) (by simp)
    · have := hinj h
      simp only [Sum.inr.injEq, Sum.inl.injEq] at this
      exact hji this.symm
  obtain ⟨h1, h2, h3, h4⟩ := hne hja
  obtain ⟨h5, h6, h7, h8⟩ := hne hja'
  exact ⟨torusLin_mem_stabSub h1 h2 h3 h4 u, torusLin_mem_stabSub h5 h6 h7 h8 u⟩

structure MinusSwapGenInput (n : ℕ) (K : Type) [Field K] (hn : 1 ≤ n) (b c : K) : Prop where
  le_sup : ∀ a a' a'' : Fin (n - 1), a ≠ a' → a ≠ a'' → a' ≠ a'' →
    minusPairPerp (K := K) hn b c a ≤ minusOverlap hn b c a a' ⊔ minusOverlap hn b c a a''
  iSup_eq_top : ⨆ a : Fin (n - 1), minusPairPerp (K := K) hn b c a = ⊤

end Minus

end CFSG.SeitzReduction.OmegaPilot
