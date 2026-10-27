module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36V
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36O

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_core_of_mem_coreActionKernel {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) (hm : 4 ≤ m)
    {g : X} (hgM : g ∈ M) (hgK : g ∈ UnbalancedLayer.coreActionKernel M) :
    g ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  have h1 := hρ.eq_one_of_mem_coreActionKernel hm hgK
  have h2 := hρ.apply_of_mem hm ⟨g, hgM⟩
  have h3 : ((θ ((⟨g, hgM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin m)) :
      Perm (Fin m)) = 1 := by rw [← h2]; exact h1
  have h4 : θ ((⟨g, hgM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := Subtype.ext h3
  rw [← map_one θ] at h4
  have h5 := θ.injective h4
  rw [QuotientGroup.eq_one_iff] at h5
  exact ⟨_, h5, rfl⟩

theorem isKleinFour_of_card_four [Finite X] {F : Subgroup X} (h4 : Nat.card F = 4)
    (hsq : ∀ x ∈ F, x * x = 1) : IsKleinFour F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥F := Finite.one_lt_card_iff_nontrivial.mp (by rw [h4]; norm_num)
  refine ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  exact orderOf_eq_prime (by rw [sq]; exact Subtype.ext (hsq g g.2)) hg

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem claimA_M_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) :
    ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  intro x hxM hx2 hx4
  obtain ⟨a₁, -, -, h₁, -, -, h₁₁, -⟩ := exists_three_of_klein S.klein
  have hC := S.centralizer_le_of_mem_E_of_sup h33 h35 hT13 hML hSch hPump hN1 hn hMH hMpc hJM
    hHN hsup hρ h₁ h₁₁
  have ha₁J : a₁ ∈ J := S.le h₁
  have ha₁M : a₁ ∈ M := hJM ha₁J
  have ha₁2 : a₁ * a₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 a₁ h₁
  have ha₁4 : (ρ ⟨a₁, le_normalizer ha₁M⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by omega) e hJM hsup hρ ha₁J
    rw [S.card_support_coreImage_E h₁ h₁₁] at h1
    exact h1
  have hkerM : ∀ g ∈ M, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g) :=
    fun g hg hgK => odd_orderOf_of_mem_oddCoreIn (mem_core_of_mem_coreActionKernel hρ (by omega)
      hg hgK)
  obtain ⟨c, hcM, hc⟩ := hρ.exists_conj_of_four (by omega) le_rfl hkerM (le_normalizer ha₁M)
    (le_normalizer hxM) ha₁M hxM ha₁2 hx2 ha₁4 hx4
  intro y hy
  have hy' : c⁻¹ * y * c ∈ centralizer ({a₁} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hy ⊢
    calc c⁻¹ * y * c * a₁ = c⁻¹ * (y * (c * a₁ * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a₁ * c⁻¹) * y) * c := by rw [hc, hy]
      _ = a₁ * (c⁻¹ * y * c) := by group
  have hcH := hMH hcM
  have h1 := mul_mem (mul_mem hcH (hC hy')) (inv_mem hcH)
  have h2 : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
  rwa [h2] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
