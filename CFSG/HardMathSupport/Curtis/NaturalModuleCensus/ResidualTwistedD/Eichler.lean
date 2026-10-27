module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeTwistedD.NaturalModule
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.BorelTits.OrthogonalModels
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.StatedOmegaScalars
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix

section

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem eq_one_of_mem_statedScalars_statedOmega_two' (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hn : 2 ≤ n) {A : StatedOmega (StatedQuadMinus n F b c)}
    (hA : (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ∈
      StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : A = 1 :=
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.eq_one_of_mem_statedScalars_statedQuadMinus_omega hirr hn hA

theorem false_of_stable_totSingular (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n)
    (hcard : Nat.card F = 2)
    {J : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))}
    {v : StatedProj (StatedOmega (StatedQuadMinus n F b c))} (hv3 : v ^ 3 = 1) (hvJ : v ∈ J)
    (hfix : ∀ g, g * v = v * g → g ∈ J)
    (W : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F))
    (hWQ : ∀ w ∈ W, StatedQuadMinus n F b c w = 0) (hWdim : 2 ≤ Module.finrank F W)
    (hWstab : ∀ y ∈ J, ∀ A : StatedOmega (StatedQuadMinus n F b c),
      (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadMinus n F b c))) = y →
      ∀ w ∈ W, ((A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈ W) :
    False := by
  obtain ⟨M0, hM0⟩ := QuotientGroup.mk_surjective v
  have hMW := fun w hw => hWstab v hvJ M0 hM0 w hw
  have hMQ := preserves_of_mem_statedOmega (Q₀ := StatedQuadMinus n F b c) M0.2
  have hM3 : (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ^ 3 = 1 := by
    have h1 : (QuotientGroup.mk (M0 ^ 3) :
        StatedProj (StatedOmega (StatedQuadMinus n F b c))) = 1 := by
      rw [QuotientGroup.mk_pow, hM0]
      exact hv3
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have := eq_one_of_mem_statedScalars_statedOmega_two' hirr (by omega) h1
    simpa using congrArg Subtype.val this
  have hC' : ∀ g ∈ StatedOmega (StatedQuadMinus n F b c),
      g * (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
        (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * g →
      ∀ w ∈ W, (g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈ W := by
    intro g hg hcomm w hw
    set gΩ : ↥(StatedOmega (StatedQuadMinus n F b c)) := ⟨g, hg⟩ with hgΩ
    have hcomm' : (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadMinus n F b c))) * v =
        v * QuotientGroup.mk gΩ := by
      rw [← hM0, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hcomm
    exact hWstab _ (hfix _ hcomm') gΩ rfl w hw
  refine false_of_invariant_totSingular_two (K := F) (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    hcard (quadMinusForm n F b c hirr) ?_ W hWQ hWdim
    (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) hMQ hM3 hMW hC'
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
