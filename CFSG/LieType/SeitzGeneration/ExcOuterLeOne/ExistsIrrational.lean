module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCellConj
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.PairLemma

open CFSG.LieType.SeitzGeneration
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.CTP

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



theorem exists_irrational_rootElt_of_not_mem {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hpK : p ≠ ringChar K)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ)) (g : ↥(adjointGroup τ K)) (hg : g ∉ subfieldGroup τ σ) :
    ∃ r ∈ subfieldGroup τ σ, ∃ r' ∈ subfieldGroup τ σ, ∃ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ)
      (t : K), t ∉ fixSubfield σ ∧ xPar (rootOperatorFamily τ) γ t ∈
        Subgroup.closure ((subfieldGroup τ σ : Set ↥(adjointGroup τ K)) ∪
          ((subfieldGroup τ σ).map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K))) := by
  
  classical
  have hτ4 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with h | h | h <;> simp [h]
  obtain ⟨θ, hθ⟩ := exists_maxHeightRoot τ
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry hτ4 σ hD hθ g hg
  have hne0 : entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 := fun h =>
    hbad (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμ, hψ⟩ := bigCell' hτ4 hθ (r * g * r') hne0
  set H := Subgroup.closure ((subfieldGroup τ σ : Set ↥(adjointGroup τ K)) ∪
    ((subfieldGroup τ σ).map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K)))
    with hH
  have hu : ∀ c ∈ fixSubfield σ, ψ (u2 (μ₁ * c)) ∈ H := fun c hc => by
    rw [(hψ c).1]
    exact Subgroup.subset_closure (Or.inl (xPar_mem_subfieldGroup τ σ θ hc))
  have hl : ∀ c ∈ fixSubfield σ, ψ (l2 (μ₂ * c)) ∈ H := fun c hc => by
    rw [(hψ c).2]
    exact Subgroup.subset_closure (Or.inr ⟨xPar (rootOperatorFamily τ) θ c,
      xPar_mem_subfieldGroup τ σ θ hc, by simp [MulAut.conj_apply, mul_assoc]⟩)
  have hlam : μ₁ * μ₂ ∉ fixSubfield σ := by
    rcases hμ with h | h
    · rw [h]; exact hbad
    · rw [h]; exact fun hm => hbad (by simpa using (fixSubfield σ).neg_mem hm)
  have hfull := sl2_hom_mem_of_pair σ hp hp2 hσ hD ψ μ₁ μ₂ hμ₁ hlam hu hl
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    have := hp.one_lt
    omega
  obtain ⟨t, ht⟩ : ∃ t : K, σ t ≠ t := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext fun x => by simpa using h x)
  refine ⟨r, hr, r', hr', θ, hθ.1, t, fun h' => ht ((mem_fixSubfield σ).1 h'), ?_⟩
  rw [← (hψ t).1]
  exact hfull t

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
