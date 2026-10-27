module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.D4Comm
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private theorem d4_height_le_five : ∀ l ∈ TwistTag.D4.tag.artifactRoots, l.sum ≤ 5 := by
  decide

private theorem d4_rho_fixed_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, 0 < l.sum →
    l[0]? = l[1]? → l[1]? = l[3]? → l = [0, 0, 1, 0] ∨ l = [1, 1, 1, 1] ∨ l = [1, 1, 2, 1] := by
  decide

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem commute_pinnedX_rootD_of_mem_posUnipotent {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ posUnipotent TwistTag.D4.tag K) (c : K) :
    Commute x (pinnedX TwistTag.D4.tag K rootD c) := by
  have hgen : ∀ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α → 0 < height α →
      ∀ d : K, Commute (pinnedX TwistTag.D4.tag K rootD c) (pinnedX TwistTag.D4.tag K α d) := by
    intro α hα hpos d
    by_cases hαD : α = rootD
    · rw [hαD]
      have e1 := pinnedX_add TwistTag.D4.tag K rootD c d
      have e2 := pinnedX_add TwistTag.D4.tag K rootD d c
      rw [add_comm d c] at e2
      exact e1.symm.trans e2
    · have hD : height (rootD : Fin TwistTag.D4.tag.rank → ℤ) = 5 := height_rootD
      refine commute_pinnedX_of_not_isRoot_add isRoot_rootD hα (Ne.symm hαD) ?_ ?_ c d
      · intro h
        rw [h, height_neg] at hD
        omega
      · intro h
        have h1 : height (rootD + α) ≤ 5 := by
          have := d4_height_le_five _ (isRoot_iff_mem_artifactRoots.1 h)
          rw [List.sum_ofFn] at this
          exact this
        have h2 : height (rootD + α) = height rootD + height α := by
          simp only [height, Pi.add_apply, Finset.sum_add_distrib]
        omega
  have hle : posUnipotent TwistTag.D4.tag K ≤
      Subgroup.centralizer {pinnedX TwistTag.D4.tag K rootD c} := by
    rw [posUnipotent, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨α, hα, d, rfl⟩
    obtain ⟨hαr, hαp⟩ := hα
    exact Subgroup.mem_centralizer_singleton_iff.2 (hgen α hαr hαp d).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem eq_rootB_or_rootC_or_rootD_of_fixed {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hpos : 0 < height γ)
    (hρ : permLattice TwistTag.D4.perm γ = γ) : γ = rootB ∨ γ = rootC ∨ γ = rootD := by
  have hs1 : TwistTag.D4.perm.symm 1 = 0 := by decide
  have hs3 : TwistTag.D4.perm.symm 3 = 1 := by decide
  have h01 : γ 0 = γ 1 := by
    have h := congrFun hρ 1
    rw [permLattice, Function.comp_apply, hs1] at h
    exact h
  have h13 : γ 1 = γ 3 := by
    have h := congrFun hρ 3
    rw [permLattice, Function.comp_apply, hs3] at h
    exact h
  have hL : List.ofFn γ = [γ 0, γ 1, γ 2, γ 3] := rfl
  have hsum : 0 < (List.ofFn γ).sum := by
    rw [List.sum_ofFn]
    exact hpos
  have hc1 : (List.ofFn γ)[0]? = (List.ofFn γ)[1]? := by
    rw [hL]
    simp [h01]
  have hc2 : (List.ofFn γ)[1]? = (List.ofFn γ)[3]? := by
    rw [hL]
    simp [h13]
  rcases d4_rho_fixed_check _ (isRoot_iff_mem_artifactRoots.1 hγ) hsum hc1 hc2 with h | h | h
  · exact Or.inl (List.ofFn_injective (h.trans rfl))
  · exact Or.inr (Or.inl (List.ofFn_injective (h.trans rfl)))
  · exact Or.inr (Or.inr (List.ofFn_injective (h.trans rfl)))

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
