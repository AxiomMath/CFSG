module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import Certificates.Certificate24272

public section

namespace CFSG.EvenSporadicStandard.HypOne.M24

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates

theorem involution_cover :
    (∀ u, 1⁻¹ * u ∈ NativeSporadic.M24 → orderOf u = 2 →
      ∃ r ∈ [m24Rep1, m24Rep2], ∃ c ∈ NativeSporadic.M24, u = c * r * c⁻¹) ∧
    ∀ r ∈ [m24Rep1, m24Rep2], (conjClosure 24 (pairTables m24gA m24gB)
      (pairTables m24gA⁻¹ m24gB⁻¹) (toTable r) 40000).1.size ≤
        (conjClass NativeSporadic.M24 r).ncard := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m24_oddcore_cover
  rw [m24InvReps_eq] at hok
  obtain ⟨hr1, hro1, -, -, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have h := exists_conj_of_repsOK hn m24Certificate m24Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m24Rep1, m24Rep2] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 40000 hok
  rw [m24Certificate_originalSubgroup] at h
  exact h

theorem centralizerIn_rep1 :
    centralizerIn NativeSporadic.M24 m24Rep1 = m24CentQ1.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m24_rep_data1
  obtain ⟨-, hsz, -⟩ := m24_oddcore_cover
  rw [m24InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m24Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (involution_cover.2 _ (by simp)) ?_
  rw [hsz.1, hKc, m24_card]

theorem centralizerIn_rep2 :
    centralizerIn NativeSporadic.M24 m24Rep2 = m24CentQ2.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m24_rep_data2
  obtain ⟨-, hsz, -⟩ := m24_oddcore_cover
  rw [m24InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m24Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (involution_cover.2 _ (by simp)) ?_
  rw [hsz.2, hKc, m24_card]

theorem fourClassesLarge_centralizer_reps :
    FourClassesLarge (centralizerIn NativeSporadic.M24 m24Rep1) ∧
      FourClassesLarge (centralizerIn NativeSporadic.M24 m24Rep2) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have h := Certificates.certificate24272.1
  simp only [fourData, Bool.and_eq_true] at h
  obtain ⟨hc1, -, -, -⟩ := m24_oddcore_cent1
  obtain ⟨hc2, -, -, -⟩ := m24_oddcore_cent2
  rw [centralizerIn_rep1, centralizerIn_rep2]
  refine ⟨fourClassesLarge_of_fourCheck hn m24CentQ1 hc1 centGens1 (fun g hg => ?_) fourWords1
    4000 h.1, fourClassesLarge_of_fourCheck hn m24CentQ2 hc2 centGens2 (fun g hg => ?_)
    fourWords2 4000 h.2⟩
  · rw [m24CentQ1, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  · rw [m24CentQ2, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg

theorem fourClassesLarge_centralizerIn :
    ∀ v ∈ NativeSporadic.M24, orderOf v = 2 →
      FourClassesLarge (centralizerIn NativeSporadic.M24 v) := by
  refine fourClassesLarge_centralizerIn_of_reps _ [m24Rep1, m24Rep2] ?_ ?_
  · intro v hv h2
    exact involution_cover.1 v (by rwa [inv_one, one_mul]) h2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fourClassesLarge_centralizer_reps.1
    · exact fourClassesLarge_centralizer_reps.2

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.M24 := by
  have hfin : Finite NativeSporadic.M24 := Nat.finite_of_card_ne_zero (by rw [m24_card]; norm_num)
  have hc : Subgroup.center NativeSporadic.M24 = ⊥ := m24_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m24_mulAut_card
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot hc) (fun α => ?_) fun y hy => ?_
  · have : α ∈ inner NativeSporadic.M24 := by rw [htop]; trivial
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg.symm⟩
  · exact SmallNormalFree.centralizer_of_centralizerIn NativeSporadic.M24 y
      (m24_inner_oddCore y hy) (fourClassesLarge_centralizerIn y y.2 (by
        rw [Subgroup.orderOf_coe]; exact hy))

theorem allInner_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .M24) : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  have hfin : Finite NativeSporadic.M24 := Nat.finite_of_card_ne_zero (by rw [m24_card]; norm_num)
  have hc : Subgroup.center NativeSporadic.M24 = ⊥ := m24_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m24_mulAut_card
  refine forall_eq_conj_of_mulEquiv e.symm fun α => ?_
  have : α ∈ inner NativeSporadic.M24 := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := this
  exact ⟨g, hg.symm⟩

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .M24) : CFSG.EvenSmallLie.FoursGroupCondition Y :=
  CFSG.EvenSmallLie.FoursGroupCondition.of_forall_eq_conj (allInner_of_isSporadic h)

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.M24 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hmem : ∀ w : List ℤ, evalCodes gens w ∈ NativeSporadic.M24 := fun w =>
    evalCodes_mem _ (by
      intro g hg
      simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact m24a.2
      · exact m24b.2) w
  have h1 : e1 ∈ NativeSporadic.M24 := hmem wordE1
  have h2 : e2 ∈ NativeSporadic.M24 := hmem wordE2
  have h3 : e3 ∈ NativeSporadic.M24 := hmem wordE3
  exact hasElemAbelianEight_of_e8Check (a := e1) (b := e2) (c := e3) hn
    Certificates.certificate24272.2 h1 h2 h3

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M24) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne (Carrier .M24) := hypothesisOne_native
  exact rowData_of_hasElemAbelianEight (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI)
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M24) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.M24
