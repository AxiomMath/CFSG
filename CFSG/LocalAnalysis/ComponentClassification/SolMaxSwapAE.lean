module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAP

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_mem_E_swap (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨L₀, F, N, r, θN, ρN, τ', DN, P⟩ := S.exists_pumpE hPump hN1 hn he₀E he₀1
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJH : J ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    hJM.trans (sup_le hMH (isPComponent_conj hMH hMpc htH).1)
  have hNH := P.le hn (P.normalizer_le_swap h33 h35) (P.L₀J.trans hJH)
    ((pPrimeCore_le_of_isPComponent P.NC P.Npc).trans (S.oddCore_le_of_mem_E he₀E he₀1))
  exact S.centralizer_le_of_pumpE_swap h33 h35 (by omega) hCH hMH hMpc hne hJM θ hsmall he₀E he₀1 P
    hNH

theorem centralizer_le_of_mem_four_swap (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {F : Subgroup X} (hFJ : F ≤ J)
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {DF : Finset (Fin n)} (hDF : DF.card = 4) (hFs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    {f : X} (hfF : f ∈ F) (hf1 : f ≠ 1) :
    centralizer ({f} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hW := S.completion_eq_of_four h33 h35 hFJ hF hDF hFs
  have S' := S.ofFour hFJ hF hDF hFs
  rw [← hW] at hCH hMH hMpc ⊢
  exact S'.centralizer_le_of_mem_E_swap h33 h35 hPump hN1 hn hCH hMH hMpc hne hJM θ hsmall hfF hf1

end Sig36

end CFSG.ComponentClassification.SolMax
