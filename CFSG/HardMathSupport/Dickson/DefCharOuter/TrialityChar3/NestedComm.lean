module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.CoordC

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


section CoordC

variable {K : Type} [Field K] [Finite K]

private abbrev rootA0B : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 0]
private abbrev rootA1B : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 1, 0]
private abbrev rootA3B : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 1]
private abbrev rootA01B : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 0]
private abbrev rootA13B : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 1, 1]
private abbrev rootA03B : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 1]

private theorem commutator_mul_mul_three {G : Type*} [Group G] (x a b c : G) :
    ⁅x, a * b * c⁆ = ⁅x, a⁆ * (⁅a, ⁅x, b⁆⁆ * ⁅x, b⁆) *
      (⁅a, ⁅b, ⁅x, c⁆⁆⁆ * ⁅b, ⁅x, c⁆⁆ * ⁅a, ⁅x, c⁆⁆ * ⁅x, c⁆) := by
  simp only [commutatorElement_def]
  group

private theorem pinnedX_mem_U2 {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ)
    (h2 : 2 ≤ height γ) (c : K) :
    pinnedX TwistTag.D4.tag K γ c ∈ heightSeries TwistTag.D4.tag K 2 :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧ 2 ≤ height α})
    ⟨hγ, by omega, h2⟩ c

private theorem coordC_list_prod : ∀ l : List (ModGL TwistTag.D4.tag K),
    (∀ x ∈ l, x ∈ heightSeries TwistTag.D4.tag K 2) → coordC l.prod = (l.map coordC).sum
  | [], _ => by
    have h1 : (1 : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 2 := one_mem _
    have h := coordC_mul h1 h1
    rw [mul_one] at h
    simp only [List.prod_nil, List.map_nil, List.sum_nil]
    linear_combination -h
  | a :: l, hl => by
    have ha : a ∈ heightSeries TwistTag.D4.tag K 2 := hl a (by simp)
    have hl' : ∀ x ∈ l, x ∈ heightSeries TwistTag.D4.tag K 2 := fun x hx => hl x (by simp [hx])
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      coordC_mul ha (Subgroup.list_prod_mem _ hl'), coordC_list_prod l hl']

private theorem coordC_pinnedX_ne {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (h2 : 2 ≤ height γ) (hne : γ ≠ rootC) (c : K) :
    coordC (pinnedX TwistTag.D4.tag K γ c) = 0 := by
  rw [coordC_pinnedX hγ h2 c, if_neg hne]

theorem exists_nested_commutator_coord : ∃ ε₀ : K, (ε₀ = 1 ∨ ε₀ = -1) ∧ ∀ s t : K,
    ⁅pinnedX TwistTag.D4.tag K rootB s, pinnedX TwistTag.D4.tag K rootA0 t *
        pinnedX TwistTag.D4.tag K rootA1 t * pinnedX TwistTag.D4.tag K rootA3 t⁆ ∈
        heightSeries TwistTag.D4.tag K 2 ∧
      coordC ⁅pinnedX TwistTag.D4.tag K rootB s, pinnedX TwistTag.D4.tag K rootA0 t *
        pinnedX TwistTag.D4.tag K rootA1 t * pinnedX TwistTag.D4.tag K rootA3 t⁆ = ε₀ * s * t ^ 3 := by
  have hA0 : IsRoot TwistTag.D4.tag rootA0 := mem_rootFinset.1 (by decide +kernel)
  have hA1 : IsRoot TwistTag.D4.tag rootA1 := mem_rootFinset.1 (by decide +kernel)
  have hA3 : IsRoot TwistTag.D4.tag rootA3 := mem_rootFinset.1 (by decide +kernel)
  have hA0B : IsRoot TwistTag.D4.tag rootA0B := mem_rootFinset.1 (by decide +kernel)
  have hA1B : IsRoot TwistTag.D4.tag rootA1B := mem_rootFinset.1 (by decide +kernel)
  have hA3B : IsRoot TwistTag.D4.tag rootA3B := mem_rootFinset.1 (by decide +kernel)
  have hA01B : IsRoot TwistTag.D4.tag rootA01B := mem_rootFinset.1 (by decide +kernel)
  have hA13B : IsRoot TwistTag.D4.tag rootA13B := mem_rootFinset.1 (by decide +kernel)
  have hA03B : IsRoot TwistTag.D4.tag rootA03B := mem_rootFinset.1 (by decide +kernel)
  have k0 : 2 ≤ height rootA0B := by decide
  have k1 : 2 ≤ height rootA1B := by decide
  have k3 : 2 ≤ height rootA3B := by decide
  have k01 : 2 ≤ height rootA01B := by decide
  have k13 : 2 ≤ height rootA13B := by decide
  have k03 : 2 ≤ height rootA03B := by decide
  have kC : 2 ≤ height rootC := by rw [height_rootC]; norm_num
  obtain ⟨e₀, -, h₀⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootB) (β := rootA0)
    (γ := rootA0B) isRoot_rootB hA0 (by decide) (by decide) (by decide) hA0B
  obtain ⟨e₁, -, h₁⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootB) (β := rootA1)
    (γ := rootA1B) isRoot_rootB hA1 (by decide) (by decide) (by decide) hA1B
  obtain ⟨e₃, he₃, h₃⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootB) (β := rootA3)
    (γ := rootA3B) isRoot_rootB hA3 (by decide) (by decide) (by decide) hA3B
  obtain ⟨f₁, -, g₁⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootA0) (β := rootA1B)
    (γ := rootA01B) hA0 hA1B (by decide) (by decide) (by decide) hA01B
  obtain ⟨f₃, hf₃, g₃⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootA1) (β := rootA3B)
    (γ := rootA13B) hA1 hA3B (by decide) (by decide) (by decide) hA13B
  obtain ⟨f₄, hf₄, g₄⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootA0) (β := rootA13B)
    (γ := rootC) hA0 hA13B (by decide) (by decide) (by decide) isRoot_rootC
  obtain ⟨f₅, -, g₅⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootA0) (β := rootA3B)
    (γ := rootA03B) hA0 hA3B (by decide) (by decide) (by decide) hA03B
  have hε : f₄ * f₃ * e₃ = 1 ∨ f₄ * f₃ * e₃ = -1 := by
    rcases hf₄ with rfl | rfl <;> rcases hf₃ with rfl | rfl <;> rcases he₃ with rfl | rfl <;> simp
  refine ⟨f₄ * f₃ * e₃, hε, fun s t => ?_⟩
  have hprod : ⁅pinnedX TwistTag.D4.tag K rootB s, pinnedX TwistTag.D4.tag K rootA0 t *
        pinnedX TwistTag.D4.tag K rootA1 t * pinnedX TwistTag.D4.tag K rootA3 t⁆ =
      [pinnedX TwistTag.D4.tag K rootA0B (e₀ * s * t),
        pinnedX TwistTag.D4.tag K rootA01B (f₁ * t * (e₁ * s * t)),
        pinnedX TwistTag.D4.tag K rootA1B (e₁ * s * t),
        pinnedX TwistTag.D4.tag K rootC (f₄ * t * (f₃ * t * (e₃ * s * t))),
        pinnedX TwistTag.D4.tag K rootA13B (f₃ * t * (e₃ * s * t)),
        pinnedX TwistTag.D4.tag K rootA03B (f₅ * t * (e₃ * s * t)),
        pinnedX TwistTag.D4.tag K rootA3B (e₃ * s * t)].prod := by
    rw [commutator_mul_mul_three, h₀ s t, h₁ s t, h₃ s t]
    simp only [g₁, g₃, g₄, g₅, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hmemL : ∀ y ∈ [pinnedX TwistTag.D4.tag K rootA0B (e₀ * s * t),
        pinnedX TwistTag.D4.tag K rootA01B (f₁ * t * (e₁ * s * t)),
        pinnedX TwistTag.D4.tag K rootA1B (e₁ * s * t),
        pinnedX TwistTag.D4.tag K rootC (f₄ * t * (f₃ * t * (e₃ * s * t))),
        pinnedX TwistTag.D4.tag K rootA13B (f₃ * t * (e₃ * s * t)),
        pinnedX TwistTag.D4.tag K rootA03B (f₅ * t * (e₃ * s * t)),
        pinnedX TwistTag.D4.tag K rootA3B (e₃ * s * t)],
      y ∈ heightSeries TwistTag.D4.tag K 2 := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pinnedX_mem_U2 hA0B k0 _
    · exact pinnedX_mem_U2 hA01B k01 _
    · exact pinnedX_mem_U2 hA1B k1 _
    · exact pinnedX_mem_U2 isRoot_rootC kC _
    · exact pinnedX_mem_U2 hA13B k13 _
    · exact pinnedX_mem_U2 hA03B k03 _
    · exact pinnedX_mem_U2 hA3B k3 _
  rw [hprod]
  refine ⟨Subgroup.list_prod_mem _ hmemL, ?_⟩
  rw [coordC_list_prod _ hmemL]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [coordC_pinnedX_ne hA0B k0 (by decide), coordC_pinnedX_ne hA01B k01 (by decide),
    coordC_pinnedX_ne hA1B k1 (by decide), coordC_pinnedX isRoot_rootC kC, if_pos rfl,
    coordC_pinnedX_ne hA13B k13 (by decide), coordC_pinnedX_ne hA03B k03 (by decide),
    coordC_pinnedX_ne hA3B k3 (by decide)]
  ring

end CoordC

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
