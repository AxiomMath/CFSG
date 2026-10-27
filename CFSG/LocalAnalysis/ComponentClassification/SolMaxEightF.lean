module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_support_eq_eight_of_mem_alternatingGroup {σ : Perm (Fin 9)} (h2 : σ * σ = 1)
    (h5 : 5 ≤ σ.support.card) (hA : σ ∈ alternatingGroup (Fin 9)) : σ.support.card = 8 := by
  have hev : 2 ∣ σ.support.card :=
    two_dvd_card_support_of_pow_two_pow (k := 1) (by rw [pow_one, sq]; exact h2)
  have hle : σ.support.card ≤ 9 := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  rcases (by omega : σ.support.card = 6 ∨ σ.support.card = 8) with h6 | h8
  · exfalso
    rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType,
      SixGen.cycleType_of_mul_self (k := 3) h2 (by norm_num) h6] at hA
    exact absurd hA (by decide)
  · exact h8

theorem signalizerNineEightFusionCaseInput_of_fusion (hR : SignalizerNineEightFusionInput)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) : SignalizerNineEightFusionCaseInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit hQt hEven
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S₀.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S₀.pair.1.1, pow_orderOf_eq_one]
  have hto : orderOf t = 2 := S₀.pair.1.1
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have htK : t ∈ UnbalancedLayer.coreActionKernel M := (hQK htQ).2
  have hQ2' : Nat.card Q = 2 := by rw [hQt, Nat.card_zpowers, hto]
  have hK2 : ∀ P : Subgroup X, P ≤ H ⊓ UnbalancedLayer.coreActionKernel M → IsPGroup 2 P →
      Nat.card P ≤ 2 := by
    intro P hPK hP2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP2
    have hdvd : 2 ^ k ∣ Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hPK
    have hkle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      Nat.card_pos.ne').mp hdvd
    have h1 : 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 = 2 := by
      rw [← hQcard, hQ2']
    rw [hk]
    calc 2 ^ k ≤ 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 :=
          Nat.pow_le_pow_right (by norm_num) hkle
      _ = 2 := h1
  obtain ⟨φ, hφs, hφo, hφt, hφρ⟩ := exists_surjective_alt_prod_two hρ hMH hHN
    (fun h hh => hEven h hh (hHN hh)) htH ht2 ht1 htK hK2
  refine hR X H φ hφs hφo t htH ht2 hφt hCt ?_ s g (hSH hsS) hgs ?_
  · intro x hx hxt h4 g' hg'
    have h4' : (ρ ⟨x, hHN hx⟩).support.card = 4 := by rw [← hφρ]; exact h4
    have hx1 : ρ ⟨x, hHN hx⟩ ≠ 1 := by
      intro h
      rw [h, Perm.support_one, Finset.card_empty] at h4'
      exact absurd h4' (by norm_num)
    exact S₀.false_of_support_le_four_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN
      hsup θ hρ (hQK.trans inf_le_left) (hQK.trans inf_le_right) hQ2 htQ hx htQ hg' htH hto htK
      hxt.symm hCt hx1 h4'.le
  · rw [hφρ]
    exact card_support_eq_eight_of_mem_alternatingGroup hρs2 h5 hsA

end CFSG.ComponentClassification.SolMax
