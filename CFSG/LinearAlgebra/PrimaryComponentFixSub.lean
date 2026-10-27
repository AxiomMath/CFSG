module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpace

public section

namespace CFSG.LinearAlgebra

open Polynomial
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.RankThree.PartOne.KCPrimary

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem fixes_fixSub_of_trivial_off
    (x : Module.End K V) (a : K[X]) (ha : a ∈ primaryFactors x)
    (hx : Squarefree (minpoly K x))
    (B T : Subgroup (V ≃ₗ[K] V))
    (hBtriv : ∀ g ∈ B, ∀ b ∈ primaryFactors x, b ≠ a →
      ∀ v ∈ primaryComponent x b, (g : V ≃ₗ[K] V) v = v)
    (hTcomm : ∀ t ∈ T,
      Commute ((t : V ≃ₗ[K] V) : Module.End K V) (primaryProjection x a))
    (hfixW : primaryComponent x a ⊓ fixSub T = ⊥) :
    ∀ g ∈ B, ∀ c' ∈ fixSub T, (g : V ≃ₗ[K] V) c' = c' := by
  classical
  intro g hg c' hc'
  set p : V := primaryProjection x a c' with hp
  have hpW : p ∈ primaryComponent x a := primaryProjection_mem hx ha c'
  have hpfix : p ∈ fixSub T := by
    intro t ht
    have hcomm' : Commute ((t : V ≃ₗ[K] V) : Module.End K V) (primaryProjection x a) :=
      hTcomm t ht
    have hfixc : (t : V ≃ₗ[K] V) c' = c' := mem_fixSub.mp hc' t ht
    calc ((t : V ≃ₗ[K] V) : Module.End K V) (primaryProjection x a c')
        = (((t : V ≃ₗ[K] V) : Module.End K V) * primaryProjection x a) c' := rfl
      _ = (primaryProjection x a * ((t : V ≃ₗ[K] V) : Module.End K V)) c' := by
          rw [hcomm'.eq]
      _ = primaryProjection x a ((t : V ≃ₗ[K] V) c') := rfl
      _ = primaryProjection x a c' := by
          exact congrArg (primaryProjection x a) hfixc
  have hp0 : p = 0 := by
    have : p ∈ primaryComponent x a ⊓ fixSub T := ⟨hpW, hpfix⟩
    rwa [hfixW] at this
  have hdecomp : c' = p + ∑ b ∈ (primaryFactors x).erase a,
      primaryProjection x b c' := by
    have hsum := LinearMap.congr_fun (sum_primaryProjection hx) c'
    have h' : (∑ b ∈ primaryFactors x, primaryProjection x b c') =
        p + ∑ b ∈ (primaryFactors x).erase a, primaryProjection x b c' :=
      (Finset.add_sum_erase (primaryFactors x)
        (fun b => primaryProjection x b c') ha).symm
    have hsum' : c' = ∑ b ∈ primaryFactors x, primaryProjection x b c' := by
      simpa using hsum.symm
    exact hsum'.trans h'
  rw [hdecomp, hp0, zero_add, map_sum]
  refine Finset.sum_congr rfl (fun b hb' => ?_)
  have hb : b ∈ primaryFactors x := Finset.mem_of_mem_erase hb'
  have hba : b ≠ a := Finset.ne_of_mem_erase hb'
  exact hBtriv g hg b hb hba _ (primaryProjection_mem hx hb c')

end CFSG.LinearAlgebra

end
