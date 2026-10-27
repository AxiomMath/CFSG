module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

theorem primaryComponent_X_sub_one_eq_ker (x : StatedSp r K) :
    primaryComponent (spEnd x) (X - 1) = LinearMap.ker (spEnd x - 1) := by
  rw [show (X - 1 : K[X]) = X - C 1 by rw [map_one], primaryComponent_X_sub_C_one]

theorem spForm_eq_zero_of_ne {x : StatedSp r K} (H : AltPrimaryData (spForm r K) (spLin r K x))
    {k : K[X]} (hk : k ∈ primaryFactors (spEnd x)) (hk1 : k ≠ X - 1) {w v : Fin r ⊕ Fin r → K}
    (hw : w ∈ LinearMap.ker (spEnd x - 1)) (hv : v ∈ primaryComponent (spEnd x) k) :
    spForm r K w v = 0 := by
  by_cases hX : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)
  · rw [← primaryComponent_X_sub_one_eq_ker] at hw
    refine H.orthogonal_of_ne hX hk ?_ hw hv
    rw [reciprocalPolynomial_X_sub_one]
    exact hk1
  · have hbot := primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one hX
    rw [← primaryComponent_X_sub_one_eq_ker, hbot] at hw
    rw [(Submodule.mem_bot K).mp hw, map_zero, LinearMap.zero_apply]

theorem exists_decomp {x : StatedSp r K} (H : AltPrimaryData (spForm r K) (spLin r K x))
    (v : Fin r ⊕ Fin r → K) :
    ∃ u v₁ : Fin r ⊕ Fin r → K, v = u + v₁ ∧ v₁ ∈ LinearMap.ker (spEnd x - 1) ∧
      (∀ g : StatedSp r K, (∀ k ∈ primaryFactors (spEnd x), k ≠ X - 1 →
        ∀ w ∈ primaryComponent (spEnd x) k, spEnd g w = w) → spEnd g u = u) ∧
      ∀ w ∈ LinearMap.ker (spEnd x - 1), spForm r K w u = 0 := by
  classical
  have hsum := eq_sum_primaryProjection H.squarefree v
  set P := primaryFactors (spEnd x) with hP
  refine ⟨∑ k ∈ P.filter (· ≠ X - 1), primaryProjection (spEnd x) k v,
    ∑ k ∈ P.filter (fun k => ¬ k ≠ X - 1), primaryProjection (spEnd x) k v, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_filter_add_sum_filter_not]
    exact hsum
  · refine Submodule.sum_mem _ fun k hk => ?_
    obtain ⟨hkP, hk1⟩ := Finset.mem_filter.mp hk
    rw [not_not] at hk1
    rw [← primaryComponent_X_sub_one_eq_ker, ← hk1]
    exact primaryProjection_mem H.squarefree hkP v
  · intro g hg
    rw [map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkP, hk1⟩ := Finset.mem_filter.mp hk
    exact hg k hkP hk1 _ (primaryProjection_mem H.squarefree hkP v)
  · intro w hw
    rw [map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkP, hk1⟩ := Finset.mem_filter.mp hk
    exact spForm_eq_zero_of_ne H hkP hk1 hw (primaryProjection_mem H.squarefree hkP v)

theorem apply_eq_of_orthogonal {x : StatedSp r K} (H : AltPrimaryData (spForm r K) (spLin r K x))
    (hnd : ((spForm r K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate)
    {g : StatedSp r K} (hg : g ∈ spFixedFactor x) {v : Fin r ⊕ Fin r → K}
    (hv : ∀ w ∈ LinearMap.ker (spEnd x - 1), spForm r K w v = 0) : spEnd g v = v := by
  have hg' := mem_spSupported.mp hg
  obtain ⟨u, v₁, rfl, hv₁, hgu, hu⟩ := exists_decomp H v
  have hfix : ∀ k ∈ primaryFactors (spEnd x), k ≠ X - 1 →
      ∀ w ∈ primaryComponent (spEnd x) k, spEnd g w = w := fun k hk hk1 w hw =>
    hg'.2 k hk (by simpa using hk1) w hw
  have h0 : v₁ = 0 := by
    have := hnd.2 ⟨v₁, hv₁⟩ fun z => by
      change spForm r K (z : Fin r ⊕ Fin r → K) v₁ = 0
      have h1 := hv z z.2
      rw [map_add, hu z z.2, zero_add] at h1
      exact h1
    exact congrArg Subtype.val this
  rw [h0, add_zero]
  exact hgu g hfix

theorem spFixedFactor_le_of_ker_le {x x' : StatedSp r K}
    (H : AltPrimaryData (spForm r K) (spLin r K x))
    (H' : AltPrimaryData (spForm r K) (spLin r K x'))
    (hnd : ((spForm r K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate)
    (hker : LinearMap.ker (spEnd x - 1) ≤ LinearMap.ker (spEnd x' - 1)) :
    spFixedFactor x ≤ spFixedFactor x' := by
  intro g hg
  have hgx := (mem_spSupported.mp hg).1
  have hfix : ∀ k ∈ primaryFactors (spEnd x), k ≠ X - 1 →
      ∀ w ∈ primaryComponent (spEnd x) k, spEnd g w = w := fun k hk hk1 w hw =>
    (mem_spSupported.mp hg).2 k hk (by simpa using hk1) w hw
  have hx'1 : ∀ w ∈ LinearMap.ker (spEnd x - 1), spEnd x' w = w := fun w hw => by
    have := hker hw
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  have hgker : ∀ w ∈ LinearMap.ker (spEnd x - 1), spEnd g w ∈ LinearMap.ker (spEnd x - 1) := by
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
    have := congrArg (fun z => spEnd z w) hgx
    simp only [spEnd_mul, Module.End.mul_apply] at this
    rw [← this, hw]
  refine mem_spSupported.mpr ⟨?_, fun k hk hk1 v hv => ?_⟩
  · refine spLin_injective (Units.ext (LinearMap.ext fun v => ?_))
    change spEnd (g * x') v = spEnd (x' * g) v
    obtain ⟨u, v₁, rfl, hv₁, hgu, hu⟩ := exists_decomp H v
    have hgu' := hgu g hfix
    have hx'u : spEnd g (spEnd x' u) = spEnd x' u := by
      refine apply_eq_of_orthogonal H hnd hg fun w hw => ?_
      rw [← hx'1 w hw, mem_sesqUnitaryGroup.mp (spLin_mem x') w u]
      exact hu w hw
    simp only [spEnd_mul, Module.End.mul_apply, map_add]
    rw [hx'1 v₁ hv₁, hx'u, hgu', hx'1 _ (hgker v₁ hv₁)]
  · refine apply_eq_of_orthogonal H hnd hg fun w hw => ?_
    exact spForm_eq_zero_of_ne H' hk (by simpa using hk1) (hker hw) hv

end CFSG.HardMathSupport.Timmesfeld.CrossChar
