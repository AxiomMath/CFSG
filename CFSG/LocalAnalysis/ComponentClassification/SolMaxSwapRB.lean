module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAP
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP2

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem centralizer_le_of_mem_E_swap_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨L₀, F, N, r, θN, ρN, τ', DN, P, hNH⟩ :=
    S.exists_pumpE_eleven h33 h35 hPump hN1 hCH hMH hMpc hne hJM θ hsmall he₀E he₀1
  exact S.centralizer_le_of_pumpE_swap h33 h35 (by norm_num) hCH hMH hMpc hne hJM θ hsmall he₀E
    he₀1 P hNH

theorem centralizer_le_of_mem_four_swap_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {F : Subgroup X} (hFJ : F ≤ J)
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {DF : Finset (Fin 11)} (hDF : DF.card = 4) (hFs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 11)) : Perm (Fin 11)) ω = ω)
    {f : X} (hfF : f ∈ F) (hf1 : f ≠ 1) :
    centralizer ({f} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hW := S.completion_eq_of_four h33 h35 hFJ hF hDF hFs
  have S' := S.ofFour hFJ hF hDF hFs
  rw [← hW] at hCH hMH hMpc ⊢
  exact S'.centralizer_le_of_mem_E_swap_eleven h33 h35 hPump hN1 hCH hMH hMpc hne hJM θ hsmall
    hfF hf1

end Sig36

namespace SwapP2

theorem claimAEleven_of_inputs
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
      (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
      (M : Subgroup X), Setting t J n e E D M → n = 11 →
      ∀ F : Subgroup X, F ≤ J →
        Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ∀ DF : Finset (Fin n), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
          ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) →
      ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E := by
  intro X _ _ _ t J n e E D M hs hn F hFJ hF DF hDF hFs f hfF hf1
  subst hn
  obtain ⟨θ⟩ := hs.alt
  exact hs.sig.centralizer_le_of_mem_four_swap_eleven h33 h35 hPump hN1 hs.cent hs.le hs.pc
    hs.swap hs.diag θ hs.small hFJ hF hDF hFs hfF hf1

end SwapP2

end CFSG.ComponentClassification.SolMax
