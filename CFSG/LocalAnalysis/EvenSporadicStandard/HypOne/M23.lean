module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import Certificates.Certificate24271

public section

namespace CFSG.EvenSporadicStandard.HypOne.M23

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates

theorem involution_cover :
    (∀ u, 1⁻¹ * u ∈ NativeSporadic.M23 → orderOf u = 2 →
      ∃ r ∈ [m23Rep1], ∃ c ∈ NativeSporadic.M23, u = c * r * c⁻¹) ∧
    ∀ r ∈ [m23Rep1], (conjClosure 23 (pairTables m23PermA m23PermB)
      (pairTables m23PermA⁻¹ m23PermB⁻¹) (toTable r) 4000).1.size ≤
        (conjClass NativeSporadic.M23 r).ncard := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m23_oddcore_cover
  rw [m23InvReps_eq] at hok
  obtain ⟨hr1, hro1, -, -, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have h := exists_conj_of_repsOK hn m23Certificate m23Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m23Rep1] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok
  rw [m23Certificate_originalSubgroup] at h
  exact h

theorem centralizerIn_rep1 :
    centralizerIn NativeSporadic.M23 m23Rep1 = m23CentQ1.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m23_rep_data1
  obtain ⟨-, hsz, -⟩ := m23_oddcore_cover
  rw [m23InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m23Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (involution_cover.2 _ (by simp)) ?_
  rw [hsz, hKc, m23_card]

theorem fourClassesLarge_centralizer_a :
    FourClassesLarge (centralizerIn NativeSporadic.M23 m23Rep1) := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hc, -, -, -⟩ := m23_oddcore_cent1
  rw [centralizerIn_rep1]
  refine fourClassesLarge_of_fourCheck hn m23CentQ1 hc centGens1 (fun g hg => ?_) fourWords1 4000
    Certificates.certificate24271.1
  rw [m23CentQ1, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem fourClassesLarge_centralizerIn :
    ∀ v ∈ NativeSporadic.M23, orderOf v = 2 →
      FourClassesLarge (centralizerIn NativeSporadic.M23 v) := by
  refine fourClassesLarge_centralizerIn_of_reps _ [m23Rep1] ?_ ?_
  · intro v hv h2
    exact involution_cover.1 v (by rwa [inv_one, one_mul]) h2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact fourClassesLarge_centralizer_a

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.M23 := by
  have hfin : Finite NativeSporadic.M23 := Nat.finite_of_card_ne_zero (by rw [m23_card]; norm_num)
  have hc : Subgroup.center NativeSporadic.M23 = ⊥ := m23_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m23_mulAut_card
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot hc) (fun α => ?_) fun y hy => ?_
  · have : α ∈ inner NativeSporadic.M23 := by rw [htop]; trivial
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg.symm⟩
  · exact SmallNormalFree.centralizer_of_centralizerIn NativeSporadic.M23 y
      (m23_inner_oddCore y hy) (fourClassesLarge_centralizerIn y y.2 (by
        rw [Subgroup.orderOf_coe]; exact hy))

theorem allInner_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .M23) : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  have hfin : Finite NativeSporadic.M23 := Nat.finite_of_card_ne_zero (by rw [m23_card]; norm_num)
  have hc : Subgroup.center NativeSporadic.M23 = ⊥ := m23_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m23_mulAut_card
  refine forall_eq_conj_of_mulEquiv e.symm fun α => ?_
  have : α ∈ inner NativeSporadic.M23 := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := this
  exact ⟨g, hg.symm⟩

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .M23) : CFSG.EvenSmallLie.FoursGroupCondition Y :=
  CFSG.EvenSmallLie.FoursGroupCondition.of_forall_eq_conj (allInner_of_isSporadic h)

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.M23 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hmem : ∀ w : List ℤ, evalCodes gens w ∈ NativeSporadic.M23 := fun w =>
    evalCodes_mem _ (by
      intro g hg
      simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact m23GenA.2
      · exact m23GenB.2) w
  have h1 : e1 ∈ NativeSporadic.M23 := hmem wordE1
  have h2 : e2 ∈ NativeSporadic.M23 := hmem wordE2
  have h3 : e3 ∈ NativeSporadic.M23 := hmem wordE3
  exact hasElemAbelianEight_of_e8Check (a := e1) (b := e2) (c := e3) hn
    Certificates.certificate24271.2 h1 h2 h3

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M23) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne (Carrier .M23) := hypothesisOne_native
  exact rowData_of_hasElemAbelianEight (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI)
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M23) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.M23
