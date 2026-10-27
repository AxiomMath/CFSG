module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Words

variable {τ : Tag}

theorem foldr_reflect_eq_of_forall_mem {J : Finset (Fin τ.rank)} {v : Fin τ.rank → ℤ}
    (hv : ∀ j ∈ J, reflect τ j v = v) {l : List (Fin τ.rank)} (hl : ∀ j ∈ l, j ∈ J) :
    l.foldr (reflect τ) v = v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
    exact hv j (hl j List.mem_cons_self)

theorem exists_letter_notMem_of_smul_ne
    {J : Finset (Fin τ.rank)} {v : Fin τ.rank → ℤ} (hv : ∀ j ∈ J, reflect τ j v = v)
    {l : List (Fin τ.rank)} (h : (coxeterSystem τ).wordProd l • v ≠ v) : ∃ s ∈ l, s ∉ J := by
  by_contra hs
  push Not at hs
  exact h (by rw [wordProd_smul', foldr_reflect_eq_of_forall_mem hv hs])

end Words

section Chev


variable {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} [CharP K p]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem card_le_finrank_of_isChevType_of_fixed [Fact p.Prime] {k V : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [CharP k p] [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K p hw ρ y χ J)
    {v : Fin τ.rank → ℤ} (hv : ∀ j ∈ J, reflect τ j v = v) {m : ℕ} (w : Fin m → WeylGroup τ)
    (hinj : ∀ i j, i ≠ j → w i • v ≠ w j • v) :
    m ≤ Module.finrank k V := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  refine CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.card_le_finrank hρ hμ w
    fun i j hij ω hω hωe => ?_
  obtain ⟨s, hsω, hsJ⟩ := exists_letter_notMem_of_smul_ne hv (l := ω) fun h => hinj i j hij (by
    rw [hωe, mul_smul] at h
    have := congrArg (fun z => w i • z) h
    simpa [smul_smul] using this.symm)
  exact ⟨s, hsω, mu_eq_dScalar_of_notMem ht hμ hsJ⟩

end Chev

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
