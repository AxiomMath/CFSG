module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ModelTwoAF
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairActionOfTheta

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_AT_of_dbl {W : Subgroup (Perm (ι × Bool))} (hWF : W ≤ blockFix ι)
    (hD : ∀ i j : ι, blockTransp i ∉ W → blockTransp j ∉ W → blockTransp i * blockTransp j ∈ W) :
    ∃ T : Finset ι, W = ((fsign T).ker).map (blockPermHom ι) ∧
      ∀ i, blockTransp i ∈ W ↔ i ∉ T := by
  classical
  set E' : Subgroup (ι → Perm Bool) := W.comap (blockPermHom ι) with hE'
  set T : Finset ι := Finset.univ.filter fun i => blockTransp i ∉ W with hT
  have hTi : ∀ i, i ∈ T ↔ tI i ∉ E' := fun i => by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, hE', Subgroup.mem_comap,
      blockPermHom_tI]
  have hDE : ∀ i ∈ T, ∀ j ∈ T, tI i * tI j ∈ E' := by
    intro i hi j hj
    have hi' : blockTransp i ∉ W := by
      simpa [hT] using hi
    have hj' : blockTransp j ∉ W := by
      simpa [hT] using hj
    show blockPermHom ι (tI i * tI j) ∈ W
    rw [map_mul, blockPermHom_tI, blockPermHom_tI]
    exact hD i j hi' hj'
  have hEq := eq_ker_fsign E' T hTi hDE
  refine ⟨T, ?_, fun i => ?_⟩
  · have hle : W ≤ (blockPermHom ι).range := by rw [range_blockPermHom]; exact hWF
    rw [← hEq, hE', Subgroup.map_comap_eq_self hle]
  · have := hTi i
    simp only [hE', Subgroup.mem_comap, blockPermHom_tI] at this
    by_cases h : blockTransp i ∈ W
    · simp [h] at this ⊢; exact this
    · simp [h] at this ⊢; exact this

section GroupLevel

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

open scoped Classical in
theorem pairActionData_of_caseTwo (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S) (n : ℕ) (hn : 5 ≤ n) (θ : ↥(L ⊔ S) →* Perm (Fin n × Bool))
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup (Fin n × Bool),
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hWF : (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) ≤
      blockFix (Fin n))
    (hD : ∀ i j : Fin n,
      blockTransp i ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) →
      blockTransp j ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) →
      blockTransp i * blockTransp j ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))))
    (hT1 : (Finset.univ.filter fun i : Fin n => blockTransp i ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool)))).card ≠ 1)
    (hT2 : (Finset.univ.filter fun i : Fin n => blockTransp i ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool)))).card ≠ 2)
    (hT4 : (Finset.univ.filter fun i : Fin n => blockTransp i ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool)))).card ≠ 4)
    (hC2 : (Finset.univ.filter fun i : Fin n => blockTransp i ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool)))).card ≠ 2)
    (hC4 : (Finset.univ.filter fun i : Fin n => blockTransp i ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool)))).card ≠ 4) :
    PairActionData (L ⊔ S) S L n := by
  classical
  obtain ⟨T, hTW, hts⟩ := exists_AT_of_dbl hWF hD
  have hTeq : T = Finset.univ.filter fun i : Fin n => blockTransp i ∉
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hts i, not_not]
  have hTceq : Tᶜ = Finset.univ.filter fun i : Fin n => blockTransp i ∈
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, hts i]
  have hSθ := theta_S_iff_mem_blockFix_AF hA (by simpa using hn) θ
    (fun m h => hpS ((hker m).1 h))
    (fun x hx => by obtain ⟨l, hl⟩ := hAltL x hx; exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩, hl⟩)
    T hTW (by rw [hTeq]; exact hT1) (by rw [hTeq]; exact hT2) (by rw [hTeq]; exact hT4)
    (by rw [hTceq]; exact hC2) (by rw [hTceq]; exact hC4)
  exact pairActionData_of_theta hLM hSL hpS n θ hker hAltL hSθ

end GroupLevel

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
