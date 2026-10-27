module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ChainsTorus
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerVTwo

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps


variable {K : Type} [Field K]

theorem innerInvolutionInput_F4_of_frameCandidates {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f)
    (hfr : ∀ x : adjointGroup .F4 K, orderOf (MulAut.conj x) = 2 →
      ∃ ψ : MulAut (adjointGroup .F4 K), ∃ y : adjointGroup .F4 K, ψ y = x ∧
        ∃ L ∈ f4FrameCandidates, ∃ e : (Fin Tag.F4.rank → ℤ) → K,
          (∀ p ∈ L, e (orbitCertRoot .F4 p) ≠ 0) ∧
            (y : ModGL .F4 K) = (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod) :
    InnerInvolutionInput (adjointGroup .F4 K) := by
  refine innerInvolutionInput_F4_of_classes'' hf hK fun x hx => ?_
  obtain ⟨ψ, y, rfl, L, hL, e, he, hy⟩ := hfr x hx
  obtain ⟨ψ', s, hs, hψ'⟩ :=
    exists_mulAut_of_mem_f4FrameCandidates_of_ne_zero hL e he (hy ▸ y.2)
  refine ⟨ψ * ψ', s, hs, ?_⟩
  rw [MulAut.mul_apply, hψ']
  congr 1
  exact Subtype.ext hy.symm

end CFSG.SeitzReduction
