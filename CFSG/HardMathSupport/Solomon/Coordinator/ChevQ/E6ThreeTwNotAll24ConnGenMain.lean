module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem twE6LineGenAt_of_dim_A {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hcube : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    (hdim : TwE6LineDim K σ f 28 ∨ TwE6LineDim K σ f 36) : TwE6LineGenAt K σ E f := by
  have hN : ∀ n ∈ ({22, 30} : Set ℕ), KSGen.TwE6ConnFixed n := fun n hn =>
    KSGen.twE6ConnFixed_A (by simpa using hn)
  have hNsub : ∀ n ∈ ({22, 30} : Set ℕ), n = 22 ∨ n = 30 ∨ n = 40 := fun n hn => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    omega
  rcases hdim with ⟨h, hh, hd⟩ | ⟨h, hh, hd⟩
  · exact KSGen.twE6LineGenAt_of_fixed hN hNsub hcube hfE hf1 hh ⟨22, by simp, by omega⟩
  · exact KSGen.twE6LineGenAt_of_fixed hN hNsub hcube hfE hf1 hh ⟨30, by simp, by omega⟩

theorem twE6EightGen : TwE6EightGen := by
  intro K _ _ σ q E hcube _ f hfE hf1 hdim
  exact twE6LineGenAt_of_dim_A hcube hfE hf1 (Or.inl hdim)

theorem twE6LineGenAt_of_dim (h40 : KSGen.TwE6ConnFixed 40) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {q : ℕ} {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hcube : TwE6Cube K σ q E) {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    (hdim : TwE6LineDim K σ f 28 ∨ TwE6LineDim K σ f 36 ∨ TwE6LineDim K σ f 46) :
    TwE6LineGenAt K σ E f := by
  have hN : ∀ n ∈ ({22, 30, 40} : Set ℕ), KSGen.TwE6ConnFixed n := fun n hn => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · exact KSGen.twE6ConnFixed_A (Or.inl rfl)
    · exact KSGen.twE6ConnFixed_A (Or.inr rfl)
    · exact h40
  have hNsub : ∀ n ∈ ({22, 30, 40} : Set ℕ), n = 22 ∨ n = 30 ∨ n = 40 := fun n hn => by
    simpa using hn
  rcases hdim with ⟨h, hh, hd⟩ | ⟨h, hh, hd⟩ | ⟨h, hh, hd⟩
  · exact KSGen.twE6LineGenAt_of_fixed hN hNsub hcube hfE hf1 hh ⟨22, by simp, by omega⟩
  · exact KSGen.twE6LineGenAt_of_fixed hN hNsub hcube hfE hf1 hh ⟨30, by simp, by omega⟩
  · exact KSGen.twE6LineGenAt_of_fixed hN hNsub hcube hfE hf1 hh ⟨40, by simp, by omega⟩

theorem twE6ConnGen_of_d5 (h40 : KSGen.TwE6ConnFixed 40) : TwE6ConnGen := by
  intro K _ _ σ q E hcube f hfE hf1 hconn
  obtain ⟨h, hh, hd, -⟩ := hconn
  have hd' : twE6MatFixDim K σ h = 28 ∨ twE6MatFixDim K σ h = 36 ∨ twE6MatFixDim K σ h = 46 := by
    simpa using hd
  rcases hd' with hd' | hd' | hd'
  · exact twE6LineGenAt_of_dim h40 hcube hfE hf1 (Or.inl ⟨h, hh, hd'⟩)
  · exact twE6LineGenAt_of_dim h40 hcube hfE hf1 (Or.inr (Or.inl ⟨h, hh, hd'⟩))
  · exact twE6LineGenAt_of_dim h40 hcube hfE hf1 (Or.inr (Or.inr ⟨h, hh, hd'⟩))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
