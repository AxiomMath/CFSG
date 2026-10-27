module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Clique
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.ExtendLemma

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

variable {J : Type*} [Group J] [DecidableEq J] {D : J → Prop}

omit [DecidableEq J] in
theorem exists_related_outside (hD : OrderThreeClass D) {F : Finset J} (hF : IsClique D F)
    {p y : J} (hp : p ∈ F) (hy : D y) (hyF : y ∉ Subgroup.closure (F : Set J))
    (hnc : p * y ≠ y * p) :
    ∃ y', D y' ∧ y' ∉ Subgroup.closure (F : Set J) ∧ (p * y') ^ 2 = 1 := by
  have hpF : p ∈ Subgroup.closure (F : Set J) := Subgroup.subset_closure hp
  rcases hD.pair p y (hF.mem p hp) hy with h | h | h | h | h | ⟨h1, h2, h3, h4⟩
  · exact absurd (by rw [eq_inv_of_mul_eq_one_right h]; exact Subgroup.inv_mem _ hpF) hyF
  · exact absurd (by rw [← mul_inv_eq_one.1 h]; exact hpF) hyF
  · exact absurd h hnc
  · exact ⟨y, hy, hyF, h⟩
  · exact ⟨y⁻¹, hD.inv y hy, fun hm => hyF (by simpa using Subgroup.inv_mem _ hm), h⟩
  · have hra : D (y⁻¹ * p * y) := hD.conj y p (hF.mem p hp)
    have hrb : D (y * p * y⁻¹) := by simpa using hD.conj y⁻¹ p (hF.mem p hp)
    by_cases ha : y⁻¹ * p * y ∈ Subgroup.closure (F : Set J)
    · by_cases hb : y * p * y⁻¹ ∈ Subgroup.closure (F : Set J)
      · exfalso
        apply hyF
        have hgen := mem_closure_of_pow_five (hD.cube y hy) h1
        refine (Subgroup.closure_le _).2 ?_ hgen
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      · refine ⟨y * p * y⁻¹, hrb, hb, ?_⟩
        simpa [mul_assoc] using h2
    · refine ⟨y⁻¹ * p * y, hra, ha, ?_⟩
      simpa [mul_assoc] using h4

theorem IsMaxClique.false_of_related_outside
    (hD : OrderThreeClass D)
    {F : Finset J} (hF : IsMaxClique D F) (hcard : 3 ≤ F.card) {p y : J} (hp : p ∈ F) (hy : D y)
    (hyF : y ∉ Subgroup.closure (F : Set J)) (hpy : (p * y) ^ 2 = 1) : False := by
  have h1 : 1 < (F.erase p).card := by
    rw [Finset.card_erase_of_mem hp]; omega
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 h1
  obtain ⟨hbp, hbF⟩ := Finset.mem_erase.1 hb
  obtain ⟨hcp, hcF⟩ := Finset.mem_erase.1 hc
  have hpF : p ∈ Subgroup.closure (F : Set J) := Subgroup.subset_closure hp
  have hpb : (p * b) ^ 2 = 1 := hF.adj p hp b hbF (Ne.symm hbp)
  have hpc : (p * c) ^ 2 = 1 := hF.adj p hp c hcF (Ne.symm hcp)
  have hbc' : (b * c) ^ 2 = 1 := hF.adj b hbF c hcF hbc
  rcases hD.extend_lemma (hF.mem p hp) (hF.mem b hbF) (hF.mem c hcF) hy hpb hpc hbc' hpy
    with h | h | h | h | h | h | h
  · apply hyF
    have hsub : ({p, b, c} : Set J) ⊆ (F : Set J) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact Subgroup.closure_mono hsub h
  · exact hyF (hF.mem_closure_of_related_two hD hp hbF (Ne.symm hbp) hy hpy h)
  · exact hyF (hF.mem_closure_of_related_two hD hp hcF (Ne.symm hcp) hy hpy h)
  · exact hyF (hF.mem_closure_of_related_two_conj hD (g := p) hpF hp hbF (Ne.symm hbp) hy
      (by simpa using hpy) h)
  · exact hyF (hF.mem_closure_of_related_two_conj hD (g := p) hpF hp hcF (Ne.symm hcp) hy
      (by simpa using hpy) h)
  · exact hyF (hF.mem_closure_of_related_two_conj hD (g := p⁻¹) (Subgroup.inv_mem _ hpF) hp hbF
      (Ne.symm hbp) hy (by simpa using hpy) (by simpa using h))
  · exact hyF (hF.mem_closure_of_related_two_conj hD (g := p⁻¹) (Subgroup.inv_mem _ hpF) hp hcF
      (Ne.symm hcp) hy (by simpa using hpy) (by simpa using h))

theorem IsMaxClique.closure_eq_top
    (hD : OrderThreeClass D)
    {F : Finset J} (hF : IsMaxClique D F)
    (hcard : 3 ≤ F.card)
    (h : Subgroup.closure (F : Set J) ≠ ⊤ → ∃ y p, D y ∧
      y ∉ Subgroup.closure (F : Set J) ∧ p ∈ F ∧ p * y ≠ y * p) :
    Subgroup.closure (F : Set J) = ⊤ := by
  by_contra hne
  obtain ⟨y, p, hy, hyF, hp, hnc⟩ := h hne
  obtain ⟨y', hy', hy'F, hpy'⟩ := exists_related_outside hD hF.toIsClique hp hy hyF hnc
  exact hF.false_of_related_outside hD hcard hp hy' hy'F hpy'

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
