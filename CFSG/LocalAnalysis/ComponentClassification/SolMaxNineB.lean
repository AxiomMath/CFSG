module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_coreActionKernel_of_normalizer_of_sup [Finite X] {M J : Subgroup X}
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {g : X} (hgN : g ∈ normalizer (J : Set X))
    (hgK : g ∈ UnbalancedLayer.coreActionKernel M) :
    g ∈ UnbalancedLayer.coreActionKernel J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup X := (pPrimeCore 2 ↥M).map M.subtype with hOdef
  have hJM : J ≤ M := le_sup_left.trans hsup.le
  have hJO : J ⊓ O ≤ (pPrimeCore 2 ↥J).map J.subtype := by
    refine le_pPrimeCore_map inf_le_left (fun x hx => ?_) ?_
    · rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨hyJ, hyO⟩ := mem_inf.mp hy
        exact mem_inf.mpr ⟨mul_mem (mul_mem hx hyJ) (inv_mem hx),
          (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer (hJM hx))) y).mp hyO⟩
      · intro hy
        obtain ⟨hyJ, hyO⟩ := mem_inf.mp hy
        have h1 : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
        rw [h1]
        exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hx) hyJ) (inv_mem (inv_mem hx)),
          (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer (hJM (inv_mem hx))))
            _).mp hyO⟩
    · have h1 : Nat.Coprime 2 (Nat.card O) := by
        rw [hOdef, card_map_of_injective M.subtype_injective]
        exact pPrimeCore_coprime_card
      exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right) h1
  refine ⟨hgN, fun j hj => hJO (mem_inf.mpr ⟨?_, ?_⟩)⟩
  · have h1 : g⁻¹ * j * g ∈ J := by
      have h2 := (mem_normalizer_iff.mp (inv_mem hgN) j).mp hj
      rwa [inv_inv] at h2
    have h2 : j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) := by group
    rw [h2]
    exact mul_mem (inv_mem hj) h1
  · exact (UnbalancedLayer.mem_coreActionKernel.mp hgK).2 j (hJM hj)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_mem_center (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {Q : Subgroup X}
    (hQK : Q ≤ UnbalancedLayer.coreActionKernel M) (htQ : t ∈ Q) {z : X} (hz : orderOf z = 2)
    (hzQ : z ∈ Q) (hzZ : ∀ q ∈ Q, q * z = z * q) :
    centralizer ({z} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hzt : z ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr (hzZ t htQ).symm
  have hzN : z ∈ normalizer (J : Set X) := S.centralizer_le_normalizer hT13 hML hSch hzt
  exact S.centralizer_le_of_kernel h33 h35 hT13 hML hSch hz hzt
    (mem_coreActionKernel_of_normalizer_of_sup hsup hzN (hQK hzQ))

end Sig36

end CFSG.ComponentClassification.SolMax
