module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_coreActionKernel_of_fixed_balance (hbal : Sol78.BalanceTwoComponentInput) [Finite X]
    {t a c e₀ : X} {J Jc : Subgroup X} {n : ℕ} (ht1 : t ≠ 1) (htt : t * t = 1)
    (hJC : J ≤ centralizer ({t} : Set X))
    (hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))))
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    (haN : a ∈ normalizer (J : Set X)) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a * t = t * a)
    (h5 : 5 ≤ n - (ρ ⟨a, haN⟩).support.card) (he₀ : e₀ ∈ J)
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    {y : X}
    (hy : y ∈ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype ⊓ centralizer ({t} : Set X))
    (hyc : y * c = c * y) : y ∈ UnbalancedLayer.coreActionKernel Jc := by
  have hyK : y ∈ UnbalancedLayer.coreActionKernel J :=
    inf_centralizer_le_coreActionKernel hbal ht1 htt hJC hJpc hρ haN ha2 ha1 hat h5 hy
  have hyN : y ∈ normalizer (J : Set X) := hyK.1
  have hyJc : y ∈ normalizer (Jc : Set X) := by
    refine mem_normalizer_of_fixed_component θ (hJcJ.trans inf_le_right) hres hinv hsubP hyN
      hyc fun x hx hxs => ?_
    rw [coreImage_conj_of_cak θ hyK hx]
    exact hxs
  exact mem_coreActionKernel_of_le (hJcJ.trans inf_le_left) hyK hyJc

end CFSG.ComponentClassification.SolMax
