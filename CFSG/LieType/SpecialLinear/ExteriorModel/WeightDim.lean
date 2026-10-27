module

public import CFSG.LieType.SpecialLinear.ExteriorModel.WeightRank
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Module
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem card_le_finrank_of_subset_bWeights [CharP k 2] (ε : τ → Finset (Fin n))
    (S : Finset (τ → Fin n → ℤ)) (hS : ∀ μ ∈ S, μ ∈ bWeights k ε) :
    S.card ≤ finrank k (BModel k ε) := by
  classical
  have hchoice : ∀ μ : ↥S, ∃ w : BIdx ε → k,
      w ∈ bCyc (k := k) ε ∧ w ∉ bRad ε ∧ ∀ s, w s ≠ 0 → bWt ε s = μ.1 :=
    fun μ => hS μ.1 μ.2
  choose w hwC hwR hwt using hchoice
  have hindep : LinearIndependent k (fun μ : ↥S =>
      (Submodule.Quotient.mk ⟨w μ, hwC μ⟩ : BModel k ε)) :=
    linearIndependent_mk_of_bWt ε (fun μ => ⟨w μ, hwC μ⟩) (fun μ => μ.1)
      (fun _ _ h => Subtype.ext h) (fun i s hs => hwt i s hs) (fun i => hwR i)
  simpa using hindep.fintype_card_le_finrank

theorem prod_orbitSize_le_finrank [CharP k 2] (ε : τ → Finset (Fin n)) :
    ∏ r ∈ Finset.univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ finrank k (BModel k ε) := by
  classical
  have hother : (Finset.univ.filter fun r => ¬ ε r ≠ ∅).prod (fun r => orbitSize (ε r)) = 1 := by
    refine Finset.prod_eq_one fun r hr => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr
    rw [hr, orbitSize_empty]
  have hprod : (∏ r ∈ Finset.univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r)) =
      ∏ r, orbitSize (ε r) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset τ))
      (p := fun r => ε r ≠ ∅) (f := fun r => orbitSize (ε r)), hother, mul_one]
  calc (∏ r ∈ Finset.univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r))
      = ∏ r, orbitSize (ε r) := hprod
    _ = (Fintype.piFinset fun r => rearr (topWt (ε r))).card := by
        rw [Fintype.card_piFinset]
        simp [orbitSize]
    _ ≤ finrank k (BModel k ε) :=
        card_le_finrank_of_subset_bWeights ε _ fun μ hμ =>
          mem_bWeights_of_mem_piFinset ε hμ

theorem add_choose_le_finrank_of_one_two [CharP k 2] (hn : 5 ≤ n) (ε : τ → Finset (Fin n))
    (r₀ : τ) (hε : ε r₀ = {⟨1, by omega⟩, ⟨2, by omega⟩}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    n * (n - 1) + n.choose 3 ≤ finrank k (BModel k ε) := by
  classical
  obtain ⟨x, ν, hxC, hxR, hxwt, hν0, hνr⟩ :=
    exists_extra_one_two (n := n) (k := k) (by omega) ε hε hε'
  let O₁ : τ → Finset (Fin n → ℤ) := fun r => rearr (topWt (ε r))
  let O₂ : τ → Finset (Fin n → ℤ) := fun r => rearr (ν r)
  have hS₁ : ∀ μ ∈ Fintype.piFinset O₁, μ ∈ bWeights k ε :=
    fun μ hμ => mem_bWeights_of_mem_piFinset ε hμ
  have hS₂ : ∀ μ ∈ Fintype.piFinset O₂, μ ∈ bWeights k ε :=
    fun μ hμ => mem_bWeights_of_rearr ε hxC hxR (ν := ν) hxwt
      (fun r => Fintype.mem_piFinset.mp hμ r)
  have hdisj : Disjoint (Fintype.piFinset O₁) (Fintype.piFinset O₂) := by
    rw [Finset.disjoint_left]
    intro μ hμ1 hμ2
    rw [Fintype.mem_piFinset] at hμ1 hμ2
    have h1 : μ r₀ ∈ rearr (topWt ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n))) := by
      simpa [O₁, hε] using hμ1 r₀
    have h2 : μ r₀ ∈ rearr (topWt ({⟨3, by omega⟩} : Finset (Fin n))) := by
      simpa [O₂, hνr] using hμ2 r₀
    obtain ⟨σ, hσ⟩ := mem_rearr.mp h1
    obtain ⟨σ', hσ'⟩ := mem_rearr.mp h2
    have himg1 : Finset.univ.image (μ r₀) = ({0, 1, 2} : Finset ℤ) := by
      rw [hσ, image_comp_perm]
      exact image_topWt_one_two (by omega)
    have himg2 : Finset.univ.image (μ r₀) = ({0, 1} : Finset ℤ) := by
      rw [hσ', image_comp_perm]
      exact image_topWt_three (by omega)
    rw [himg1] at himg2
    exact (by decide : ({0, 1, 2} : Finset ℤ) ≠ {0, 1}) himg2
  have hcard₁ : (Fintype.piFinset O₁).card = n * (n - 1) := by
    rw [Fintype.card_piFinset, Finset.prod_eq_single r₀]
    · simp only [O₁, hε]
      exact card_rearr_topWt_one_two (by omega)
    · intro r _ hr
      simp [O₁, hε' r hr, topWt_empty, rearr_zero_eq]
    · intro h
      exact absurd (Finset.mem_univ r₀) h
  have hcard₂ : (Fintype.piFinset O₂).card = n.choose 3 := by
    rw [Fintype.card_piFinset, Finset.prod_eq_single r₀]
    · simp only [O₂, hνr]
      have h := orbitSize_singleton (n := n) (⟨3, by omega⟩ : Fin n)
      simpa [orbitSize] using h
    · intro r _ hr
      simp [O₂, hν0 r hr, rearr_zero_eq]
    · intro h
      exact absurd (Finset.mem_univ r₀) h
  have hcard : (Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).card =
      n * (n - 1) + n.choose 3 := by
    rw [Finset.card_union_of_disjoint hdisj, hcard₁, hcard₂]
  rw [← hcard]
  exact card_le_finrank_of_subset_bWeights ε _ fun μ hμ => by
    rw [Finset.mem_union] at hμ
    rcases hμ with hμ | hμ
    · exact hS₁ μ hμ
    · exact hS₂ μ hμ

theorem add_choose_le_finrank_of_last_two [CharP k 2] (hn : 5 ≤ n) (ε : τ → Finset (Fin n))
    (r₀ : τ) (hε : ε r₀ = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    n * (n - 1) + n.choose 3 ≤ finrank k (BModel k ε) := by
  classical
  obtain ⟨x, ν, hxC, hxR, hxwt, hν0, hνr⟩ :=
    exists_extra_last_two (n := n) (k := k) hn ε hε hε'
  let O₁ : τ → Finset (Fin n → ℤ) := fun r => rearr (topWt (ε r))
  let O₂ : τ → Finset (Fin n → ℤ) := fun r => rearr (ν r)
  have hS₁ : ∀ μ ∈ Fintype.piFinset O₁, μ ∈ bWeights k ε :=
    fun μ hμ => mem_bWeights_of_mem_piFinset ε hμ
  have hS₂ : ∀ μ ∈ Fintype.piFinset O₂, μ ∈ bWeights k ε :=
    fun μ hμ => mem_bWeights_of_rearr ε hxC hxR (ν := ν) hxwt
      (fun r => Fintype.mem_piFinset.mp hμ r)
  have hdisj : Disjoint (Fintype.piFinset O₁) (Fintype.piFinset O₂) := by
    rw [Finset.disjoint_left]
    intro μ hμ1 hμ2
    rw [Fintype.mem_piFinset] at hμ1 hμ2
    have h1 : μ r₀ ∈ rearr (topWt ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} :
        Finset (Fin n))) := by
      simpa [O₁, hε] using hμ1 r₀
    have h2 : μ r₀ ∈ rearr (fun a : Fin n =>
        topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)) a + 1) := by
      simpa [O₂, hνr] using hμ2 r₀
    obtain ⟨σ, hσ⟩ := mem_rearr.mp h1
    obtain ⟨σ', hσ'⟩ := mem_rearr.mp h2
    have himg1 : Finset.univ.image (μ r₀) = ({0, 1, 2} : Finset ℤ) := by
      rw [hσ, image_comp_perm]
      exact image_topWt_last_pair hn
    have himg2 : Finset.univ.image (μ r₀) = ({1, 2} : Finset ℤ) := by
      rw [hσ', image_comp_perm]
      exact image_topWt_last hn
    rw [himg1] at himg2
    exact (by decide : ({0, 1, 2} : Finset ℤ) ≠ {1, 2}) himg2
  have hcard₁ : (Fintype.piFinset O₁).card = n * (n - 1) := by
    rw [Fintype.card_piFinset, Finset.prod_eq_single r₀]
    · simp only [O₁, hε]
      exact card_rearr_topWt_last_pair hn
    · intro r _ hr
      simp [O₁, hε' r hr, topWt_empty, rearr_zero_eq]
    · intro h
      exact absurd (Finset.mem_univ r₀) h
  have hcard₂ : (Fintype.piFinset O₂).card = n.choose 3 := by
    rw [Fintype.card_piFinset, Finset.prod_eq_single r₀]
    · simp only [O₂, hνr]
      rw [card_rearr_comp_injective (f := topWt ({⟨n - 3, by omega⟩} : Finset (Fin n)))
        (e := fun z : ℤ => z + 1) (fun a b h => by linarith)]
      rw [card_rearr_topWt_singleton]
      change n.choose (n - 3) = n.choose 3
      exact Nat.choose_symm (by omega)
    · intro r _ hr
      simp [O₂, hν0 r hr, rearr_zero_eq]
    · intro h
      exact absurd (Finset.mem_univ r₀) h
  have hcard : (Fintype.piFinset O₁ ∪ Fintype.piFinset O₂).card =
      n * (n - 1) + n.choose 3 := by
    rw [Finset.card_union_of_disjoint hdisj, hcard₁, hcard₂]
  rw [← hcard]
  exact card_le_finrank_of_subset_bWeights ε _ fun μ hμ => by
    rw [Finset.mem_union] at hμ
    rcases hμ with hμ | hμ
    · exact hS₁ μ hμ
    · exact hS₂ μ hμ

end CFSG.LieType.SpecialLinear.ExteriorModel

end
