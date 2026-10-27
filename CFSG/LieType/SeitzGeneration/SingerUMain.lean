module

public import CFSG.LieType.SeitzGeneration.SingerUBlocks
public import CFSG.LieType.SeitzGeneration.SingerUFixerGeneric
public import CFSG.LieType.SeitzGeneration.SingerUFixerFermat
public import CFSG.LieType.SeitzGeneration.UnitaryOuterNonabFive

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_outer_fixer (h : UnitaryFieldData ℓ f K) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {c : K} (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c)
    (H : Subgroup (GL (Fin p) K))
    (hT : ∀ g ∈ unitarySU ℓ f K p, (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hL : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin p) (Fin p) K) := by
  by_cases hne : ℓ ^ f + 1 = p
  · by_cases h17 : 17 ≤ p
    · exact exists_outer_fixer_fermat h h17 hne hcu hc H hT hL
    · obtain ⟨hℓ, hf⟩ := ug_fermat_small h.prime h.one_le (Fact.out : p.Prime) hp (by omega) hne
      have hp5 : p = 5 := by subst hℓ hf; omega
      exact exists_outer_fixer_five_four h hℓ hf hp5 hcu hc H hT hL
  · exact exists_outer_fixer_generic h hp hpq hne hcu hc H hT hL

theorem singerTorusGenU_of_prime (h : UnitaryFieldData ℓ f K)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) : SingerTorusGenU h p := by
  intro c hcu hc H hHU hT hL
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcu
  set H₀ := Subgroup.closure (thmU_gens ℓ f K p c) with hH₀
  have hgens : thmU_gens ℓ f K p c ⊆ H := by
    intro g hg
    simp only [thmU_gens, Set.mem_setOf_eq] at hg
    obtain ⟨hgU, hg | hg⟩ := hg
    · exact hT g hgU hg
    · exact hL g hgU hg
  have hH₀H : H₀ ≤ H := (Subgroup.closure_le H).2 hgens
  have hH₀U : H₀ ≤ unitarySU ℓ f K p := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [thmU_gens, Set.mem_setOf_eq] at hg
    exact hg.1
  have hT₀ : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H₀ :=
    fun g hgU hg => Subgroup.subset_closure <| by
      simp only [thmU_gens, Set.mem_setOf_eq]; exact ⟨hgU, Or.inl hg⟩
  have hL₀ : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H₀ :=
    fun g hgU hg => Subgroup.subset_closure <| by
      simp only [thmU_gens, Set.mem_setOf_eq]; exact ⟨hgU, Or.inr hg⟩
  let cG : GL (Fin p) K :=
    Matrix.nonsingInvUnit (companionMat p c) (thmU_companionMat_isUnit_det hodd hc0)
  have hcG : (cG : Matrix (Fin p) (Fin p) K) = companionMat p c := rfl
  have hC₀ : ∀ g ∈ H₀, ∀ g' : GL (Fin p) K,
      (g' : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g' ∈ H₀ := by
    intro g hg g' hg'
    have hmem := thmU_closure_conj_stable h hodd hcu cG hcG g hg
    have heq : g' = cG * g * cG⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      ext : 1
      simp only [Units.val_mul, hcG]
      exact hg'
    rw [heq]
    exact hmem
  have hfix := exists_outer_fixer h hp hpq hcu hc H₀ hT₀ hL₀
  have htop := eq_unitarySU_of_fixer_companion h hp hpq hc0 hcu H₀ hH₀U hT₀ hC₀ hfix
  exact le_antisymm hHU (htop ▸ hH₀H)

theorem unitaryOuterHeisFive_holds : UnitaryOuterHeisFive :=
  unitaryOuterHeisFive_of_singerU fun _ _ _ _ h _ hp hp5 hpq =>
    haveI := Fact.mk hp
    singerTorusGenU_of_prime h hp5 hpq

end CFSG.LieType.SeitzGeneration
