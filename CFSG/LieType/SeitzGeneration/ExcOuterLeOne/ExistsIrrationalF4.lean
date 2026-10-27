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



theorem exists_irrational_longRootElt_of_not_mem {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hpK : p ≠ ringChar K)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ)) (g : ↥(adjointGroup .F4 K))
    (hg : g ∉ subfieldGroup .F4 σ) :
    ∃ r ∈ subfieldGroup .F4 σ, ∃ r' ∈ subfieldGroup .F4 σ,
      ∃ γ ∈ CFSG.LieType.Ree.ReeTag.longRoots CFSG.LieType.Ree.ReeTag.F4, ∃ t : K,
        t ∉ fixSubfield σ ∧ xPar (rootOperatorFamily .F4) γ t ∈
          Subgroup.closure ((subfieldGroup .F4 σ : Set ↥(adjointGroup .F4 K)) ∪
            ((subfieldGroup .F4 σ).map (MulAut.conj (r * g * r')).toMonoidHom :
              Set ↥(adjointGroup .F4 K))) := by
  
  classical
  have hτ4 : Tag.F4 = .E6 ∨ Tag.F4 = .E7 ∨ Tag.F4 = .E8 ∨ Tag.F4 = .F4 := Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨θ, hθ⟩ := exists_maxHeightRoot Tag.F4
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry hτ4 σ hD hθ g hg
  have hne0 : entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 := fun h =>
    hbad (h ▸ (fixSubfield σ).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμ, hψ⟩ := bigCell' hτ4 hθ (r * g * r') hne0
  set H := Subgroup.closure ((subfieldGroup .F4 σ : Set ↥(adjointGroup .F4 K)) ∪
    ((subfieldGroup .F4 σ).map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup .F4 K)))
    with hH
  have hu : ∀ c ∈ fixSubfield σ, ψ (u2 (μ₁ * c)) ∈ H := fun c hc => by
    rw [(hψ c).1]
    exact Subgroup.subset_closure (Or.inl (xPar_mem_subfieldGroup .F4 σ θ hc))
  have hl : ∀ c ∈ fixSubfield σ, ψ (l2 (μ₂ * c)) ∈ H := fun c hc => by
    rw [(hψ c).2]
    exact Subgroup.subset_closure (Or.inr ⟨xPar (rootOperatorFamily .F4) θ c,
      xPar_mem_subfieldGroup .F4 σ θ hc, by simp [MulAut.conj_apply, mul_assoc]⟩)
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
  have hlong : θ ∈ CFSG.LieType.Ree.ReeTag.longRoots CFSG.LieType.Ree.ReeTag.F4 :=
    ⟨hθ.1, (CFSG.LieType.Ree.ReeTag.lengthParam_eq_prime_iff (t := CFSG.LieType.Ree.ReeTag.F4)
      (α := θ)).2 (hθ.rootNorm_F4.trans (by decide))⟩
  refine ⟨r, hr, r', hr', θ, hlong, t, fun h' => ht ((mem_fixSubfield σ).1 h'), ?_⟩
  rw [← (hψ t).1]
  exact hfull t

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
