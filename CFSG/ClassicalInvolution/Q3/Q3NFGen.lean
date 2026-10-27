module

public import CFSG.ClassicalInvolution.Q3.Q3NFPair
public import CFSG.ClassicalInvolution.Q3.Q3KCGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3KB
  CFSG.ClassicalInvolution.Q3.Q3KC
open scoped commutatorElement


section Defs

variable {G : Type} [Group G]

structure PairData3 (Φ : Set (Subgroup G)) (A : Subgroup G) (a : G) (K K' : Subgroup G)
    (w w' : G) : Prop where
  memK : K ∈ centralizingMembers Φ {a}
  memK' : K' ∈ centralizingMembers Φ {a}
  clsK : IsClassicalMember3In (centralizingLayer Φ {a}) K w
  clsK' : IsClassicalMember3In (centralizingLayer Φ {a}) K' w'
  memA : w ∈ A
  memA' : w' ∈ A
  sq : w * w = 1
  sq' : w' * w' = 1
  ne_one : w ≠ 1
  ne_one' : w' ≠ 1
  ne : w ≠ w'
  comm : w * w' = w' * w
  central : ∀ x ∈ K, w * x = x * w
  central' : ∀ x ∈ K', w' * x = x * w'
  cross : ∀ x ∈ K', ⁅w, x⁆ ∈ oddCoreIn (centralizingLayer Φ {a})
  cross' : ∀ x ∈ K, ⁅w', x⁆ ∈ oddCoreIn (centralizingLayer Φ {a})

end Defs

section Pair

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {A : Subgroup G}

theorem range_le_fourCentralizerImage_of_pair_weak (hA : IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hAY : A ≤ centralizingLayer Φ {a}) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Φ a) (localFamily Φ a)) {k : ι} {K K' : Subgroup G}
    {w w' : G} (P : PairData3 Φ A a K K' w w') (hwa : w ≠ a) (hw'a : w' ≠ a)
    (hww' : w * w' ≠ a)
    (hnc : ¬ ∀ q ∈ (D.hom k).range, QuotientGroup.mk'
        (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, hAY P.memA⟩ * q =
          q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
            ⟨w, hAY P.memA⟩)
    (hnc' : ¬ ∀ q ∈ (D.hom k).range, QuotientGroup.mk'
        (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w', hAY P.memA'⟩ * q =
          q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
            ⟨w', hAY P.memA'⟩) :
    (D.hom k).range ≤ fourCentralizerImage Φ A a := by
  let Y : Subgroup G := centralizingLayer Φ {a}
  have hKY : K ≤ Y := le_centralizingLayer P.memK
  have hK'Y : K' ≤ Y := le_centralizingLayer P.memK'
  have hwY : w ∈ Y := hAY P.memA
  have hw'Y : w' ∈ Y := hAY P.memA'
  have hwK : w ∈ K := by
    obtain ⟨hz, hc⟩ := P.clsK
    exact Subgroup.mem_subgroupOf.mp hc.mem
  have hw'K' : w' ∈ K' := by
    obtain ⟨hz, hc⟩ := P.clsK'
    exact Subgroup.mem_subgroupOf.mp hc.mem
  have hwwY : w * w' ∈ Y := Y.mul_mem hwY hw'Y
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hΦ : ∀ {M : Subgroup G}, M ∈ centralizingMembers Φ {a} →
      modOddIn Y M ∈ localFamily Φ a :=
    fun {M} hM => ⟨M.subgroupOf Y, ⟨M, hM, le_centralizingLayer hM, rfl⟩, rfl⟩
  have hsqww : (w * w') * (w * w') = 1 := by
    calc (w * w') * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← P.comm]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [P.sq, P.sq', one_mul]
  have hww1 : w * w' ≠ 1 := fun h => P.ne (by
    have h' : w' = w⁻¹ := eq_inv_of_mul_eq_one_right h
    exact (h'.trans (inv_eq_of_mul_eq_one_right P.sq)).symm)
  have hζmem : π ⟨w, hwY⟩ ∈ modOddIn Y K :=
    ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hwK, rfl⟩
  have hξmem : π ⟨w', hw'Y⟩ ∈ modOddIn Y K' :=
    ⟨⟨w', hw'Y⟩, Subgroup.mem_subgroupOf.mpr hw'K', rfl⟩
  have hζ2 : π ⟨w, hwY⟩ * π ⟨w, hwY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥Y) * ⟨w, hwY⟩ = 1 := Subtype.ext P.sq
    rw [this, map_one]
  have hξ2 : π ⟨w', hw'Y⟩ * π ⟨w', hw'Y⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w', hw'Y⟩ : ↥Y) * ⟨w', hw'Y⟩ = 1 := Subtype.ext P.sq'
    rw [this, map_one]
  have hζ1 : π ⟨w, hwY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hwY P.sq P.ne_one
  have hξ1 : π ⟨w', hw'Y⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hw'Y P.sq' P.ne_one'
  have hmul : π ⟨w * w', hwwY⟩ = π ⟨w, hwY⟩ * π ⟨w', hw'Y⟩ := by
    rw [← map_mul]
    rfl
  have hζξ : π ⟨w, hwY⟩ ≠ π ⟨w', hw'Y⟩ := by
    intro h
    apply Q3Y.mk_ne_one_of_involution Y hwwY hsqww hww1
    rw [hmul, ← h, hζ2]
  have hζc : ∀ y ∈ modOddIn Y K, π ⟨w, hwY⟩ * y = y * π ⟨w, hwY⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.central x (Subgroup.mem_subgroupOf.mp hx))
  have hξc : ∀ y ∈ modOddIn Y K', π ⟨w', hw'Y⟩ * y = y * π ⟨w', hw'Y⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.central' x (Subgroup.mem_subgroupOf.mp hx))
  have hcross : ∀ {u v : G} (hu : u ∈ Y) (hv : v ∈ Y), ⁅u, v⁆ ∈ oddCoreIn Y →
      π ⟨u, hu⟩ * π ⟨v, hv⟩ = π ⟨v, hv⟩ * π ⟨u, hu⟩ := by
    intro u v hu hv h
    rw [mk_comm_eq_iff hu hv]
    simpa [commutatorElement_def] using h
  have hζJ : ∀ y ∈ modOddIn Y K', π ⟨w, hwY⟩ * y = y * π ⟨w, hwY⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    exact hcross hwY (hK'Y hx') (P.cross x hx')
  have hξK : ∀ y ∈ modOddIn Y K, π ⟨w', hw'Y⟩ * y = y * π ⟨w', hw'Y⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    exact hcross hw'Y (hKY hx') (P.cross' x hx')
  have hk : D.kind k ≠ CompData.sl23 := by
    refine kind_ne_sl23_of_distinct D (hΦ P.memK) (hΦ P.memK') (fun h => ?_) hζmem hξmem hnc hnc'
    have hmem := mul_mem_oddCoreIn_of_modOddIn_eq3_in P.clsK P.clsK' h
    exact hww1 (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn Y) hmem hsqww)
  have hrange := range_le_of_pair_weak D hk (hΦ P.memK) (hΦ P.memK') hζmem hξmem hζ2 hξ2 hζ1
    hξ1 hζξ hζc hξc hζJ hξK hnc hnc'
  refine hrange.trans (sup_le (sup_le ?_ ?_) ?_)
  · rintro q ⟨hq, -⟩
    exact mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY P.memA P.ne_one hwa
      (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
  · rintro q ⟨hq, -⟩
    exact mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY P.memA' P.ne_one' hw'a
      (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
  · rintro q ⟨hq, -⟩
    have hq' := Subgroup.mem_centralizer_singleton_iff.mp hq
    rw [← hmul] at hq'
    exact mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY (A.mul_mem P.memA P.memA')
      hww1 hww' hq'.symm

end Pair

section Triple

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {A : Subgroup G}

theorem centralizerGeneration_of_triple (hA : IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hAY : A ≤ centralizingLayer Φ {a}) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Φ a) (localFamily Φ a)) {K : Fin 3 → Subgroup G}
    {w : Fin 3 → G} (P : ∀ p q : Fin 3, p ≠ q → PairData3 Φ A a (K p) (K q) (w p) (w q))
    (hind : w 0 * w 1 ≠ w 2) :
    centralizingLayer Φ {a} ≤ oddCoreIn (centralizingLayer Φ {a}) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A,
        (Subgroup.centralizer (F : Set G) ⊓ centralizingLayer Φ {a}) := by
  classical
  have hsq : ∀ p, w p * w p = 1 := fun p => by
    obtain ⟨q, hq⟩ : ∃ q : Fin 3, p ≠ q := by
      fin_cases p
      exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
    exact (P p q hq).sq
  have hne : ∀ p q : Fin 3, p ≠ q → w p ≠ w q := fun p q hpq => (P p q hpq).ne
  have hcomm : ∀ p q : Fin 3, p ≠ q → w p * w q = w q * w p := fun p q hpq => (P p q hpq).comm
  have h12 : w 1 * w 2 ≠ w 0 := by
    intro h
    apply hind
    calc w 0 * w 1 = w 1 * w 0 := hcomm 0 1 (by decide)
      _ = w 1 * (w 1 * w 2) := by rw [h]
      _ = (w 1 * w 1) * w 2 := by group
      _ = w 2 := by rw [hsq 1, one_mul]
  have h02 : w 0 * w 2 ≠ w 1 := by
    intro h
    apply hind
    calc w 0 * w 1 = w 0 * (w 0 * w 2) := by rw [h]
      _ = (w 0 * w 0) * w 2 := by group
      _ = w 2 := by rw [hsq 0, one_mul]
  have hrange : ∀ i : ι, (D.hom i).range ≤ fourCentralizerImage Φ A a := by
    intro i
    by_cases hα : ∃ (f : G) (hfA : f ∈ A), f ≠ 1 ∧ f ≠ a ∧
        ∀ q ∈ (D.hom i).range, QuotientGroup.mk'
          (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨f, hAY hfA⟩ * q =
            q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
              ⟨f, hAY hfA⟩
    · obtain ⟨f, hfA, hf1, hfa, hall⟩ := hα
      exact fun q hq =>
        mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY hfA hf1 hfa (hall q hq)
    · have key : ∀ p q : Fin 3, ∀ hpq : p ≠ q, w p ≠ a → w q ≠ a → w p * w q ≠ a →
          (D.hom i).range ≤ fourCentralizerImage Φ A a :=
        fun p q hpq hwa hw'a hww' =>
          range_le_fourCentralizerImage_of_pair_weak hA haA ha1 hAY D (P p q hpq) hwa hw'a hww'
            (fun hall => hα ⟨_, (P p q hpq).memA, (P p q hpq).ne_one, hwa, hall⟩)
            (fun hall => hα ⟨_, (P p q hpq).memA', (P p q hpq).ne_one', hw'a, hall⟩)
      by_cases e0 : a = w 0
      · exact key 1 2 (by decide) (by rw [e0]; exact (hne 0 1 (by decide)).symm)
          (by rw [e0]; exact (hne 0 2 (by decide)).symm) (by rw [e0]; exact h12)
      by_cases e1 : a = w 1
      · exact key 0 2 (by decide) (by rw [e1]; exact hne 0 1 (by decide))
          (by rw [e1]; exact (hne 1 2 (by decide)).symm) (by rw [e1]; exact h02)
      by_cases e2 : a = w 2
      · exact key 0 1 (by decide) (by rw [e2]; exact hne 0 2 (by decide))
          (by rw [e2]; exact hne 1 2 (by decide)) (by rw [e2]; exact hind)
      by_cases e3 : a = w 0 * w 1
      · exact key 0 2 (by decide) (Ne.symm e0) (Ne.symm e2) (by
          rw [e3]
          intro h
          exact hne 1 2 (by decide) (mul_left_cancel h).symm)
      · exact key 0 1 (by decide) (Ne.symm e0) (Ne.symm e1) (Ne.symm e3)
  refine Q3Y2.oddCoreIn_sup_of_range_le _ fun y => ?_
  have htop : (⊤ : Subgroup (↥(centralizingLayer Φ {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))) ≤ fourCentralizerImage Φ A a := by
    rw [← D.generate]
    exact iSup_le hrange
  obtain ⟨j, hjJ, hjy⟩ := (show QuotientGroup.mk'
    (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) y ∈ fourCentralizerImage Φ A a from
      htop trivial)
  exact ⟨j, Subgroup.mem_subgroupOf.mp hjJ, hjy⟩

end Triple

end CFSG.ClassicalInvolution.Q3.Q3NF
