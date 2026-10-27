module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import Certificates.Certificate24560

public section

namespace CFSG.EvenSporadicStandard.M11Std

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Certificates
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.EvenSporadicStandard.HypOne

abbrev m11Rep1 : Equiv.Perm (Fin 11) := evalCodes [m11gA, m11gB] [1]

theorem involution_cover :
    (∀ u, 1⁻¹ * u ∈ NativeSporadic.M11 → orderOf u = 2 →
      ∃ r ∈ [m11Rep1], ∃ c ∈ NativeSporadic.M11, u = c * r * c⁻¹) ∧
    ∀ r ∈ [m11Rep1], (conjClosure 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
      (toTable r) 400).1.size ≤ (conjClass NativeSporadic.M11 r).ncard := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, -, -, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  have h := exists_conj_of_repsOK hn m11Certificate m11Certificate_check.1
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m11Rep1] (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact ⟨by simpa using hr, hro⟩) 400 hok
  rw [m11Certificate_originalSubgroup] at h
  exact h

theorem centralizerIn_rep1 :
    centralizerIn NativeSporadic.M11 m11Rep1 = m11CentQ1.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m11_rep_data
  obtain ⟨-, hsz, -⟩ := m11_oddcore_cover
  simp only [repSizes, m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hsz
  rw [m11Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (involution_cover.2 _ (by simp)) ?_
  rw [hsz, hKc, m11_card]

theorem fourClassesLarge_centralizer_a :
    FourClassesLarge (centralizerIn NativeSporadic.M11 m11Rep1) := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hc, -, -, -⟩ := m11_oddcore_cent1
  rw [centralizerIn_rep1]
  refine fourClassesLarge_of_fourCheck hn m11CentQ1 hc centGens1 (fun g hg => ?_) fourWords1 400
    Certificates.certificate24560
  rw [m11CentQ1, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem fourClassesLarge_centralizerIn :
    ∀ v ∈ NativeSporadic.M11, orderOf v = 2 →
      FourClassesLarge (centralizerIn NativeSporadic.M11 v) := by
  refine fourClassesLarge_centralizerIn_of_reps _ [m11Rep1] ?_ ?_
  · intro v hv h2
    exact involution_cover.1 v (by rwa [inv_one, one_mul]) h2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact fourClassesLarge_centralizer_a

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.M11 := by
  have hc : Subgroup.center NativeSporadic.M11 = ⊥ := m11_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m11_mulAut_card
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot hc) (fun α => ?_) fun y hy => ?_
  · have : α ∈ inner NativeSporadic.M11 := by rw [htop]; trivial
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg.symm⟩
  · exact SmallNormalFree.centralizer_of_centralizerIn NativeSporadic.M11 y
      (m11_inner_oddCore y hy) (fourClassesLarge_centralizerIn y y.2 (by
        rw [Subgroup.orderOf_coe]; exact hy))

theorem allInner_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .M11) : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  have hc : Subgroup.center NativeSporadic.M11 = ⊥ := m11_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m11_mulAut_card
  refine CFSG.EvenSporadicStandard.HypOne.forall_eq_conj_of_mulEquiv e.symm fun α => ?_
  have : α ∈ inner NativeSporadic.M11 := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := this
  exact ⟨g, hg.symm⟩

end CFSG.EvenSporadicStandard.M11Std
