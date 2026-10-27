module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Indep
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section Words

variable {τ : Tag}

theorem wordProd_smul'
    (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem foldr_reflect_eq_of_notMem {s : Fin τ.rank} {v : Fin τ.rank → ℤ}
    (hv : ∀ j, j ≠ s → reflect τ j v = v) {l : List (Fin τ.rank)} (hs : s ∉ l) :
    l.foldr (reflect τ) v = v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih (fun h => hs (List.mem_cons_of_mem _ h))]
    exact hv j fun h => hs (h ▸ List.mem_cons_self)

theorem exists_letter_of_smul_ne
    {s : Fin τ.rank} {v : Fin τ.rank → ℤ} (hv : ∀ j, j ≠ s → reflect τ j v = v)
    {l : List (Fin τ.rank)} (h : (coxeterSystem τ).wordProd l • v ≠ v) : s ∈ l := by
  by_contra hs
  exact h (by rw [wordProd_smul', foldr_reflect_eq_of_notMem hv hs])

end Words

section Chev


variable {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} [CharP K p]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem mu_eq_dScalar_of_notMem [Fact p.Prime] {k V : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [CharP k p] {ρ : Representation k (adjointGroup τ K) V}
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K p hw ρ y χ J) {μ : Fin τ.rank → k}
    (hμ : (chevDatum τ K p hw).IsCurtisType ρ y χ μ) {s : Fin τ.rank} (hs : s ∉ J) :
    μ s = (chevDatum τ K p hw).dScalar χ s := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [ht.mu_eq hμ s, dScalar_chevDatum]
  by_cases h : ∀ t : Kˣ, χ (dC τ K s t) = 1
  · simp [h, hs]
  · rw [sum_chi_torusElt hμ s h]
    simp [h]

theorem card_le_finrank_of_isChevType [Fact p.Prime] {k V : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [CharP k p] [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K p hw ρ y χ J)
    {s : Fin τ.rank} (hs : s ∉ J) {v : Fin τ.rank → ℤ} (hv : ∀ j, j ≠ s → reflect τ j v = v)
    {m : ℕ} (w : Fin m → WeylGroup τ) (hinj : ∀ i j, i ≠ j → w i • v ≠ w j • v) :
    m ≤ Module.finrank k V := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  refine CurtisExc.card_le_finrank hρ hμ w fun i j hij ω hω hωe => ⟨s, ?_, mu_eq_dScalar_of_notMem ht hμ hs⟩
  refine exists_letter_of_smul_ne hv fun h => hinj i j hij ?_
  rw [hωe, mul_smul] at h
  have := congrArg (fun z => w i • z) h
  simpa [smul_smul] using this.symm

end Chev

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
