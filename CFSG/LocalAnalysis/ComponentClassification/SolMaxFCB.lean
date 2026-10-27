module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineJ

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerNineFusionCountInvolInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
    ∀ s ∈ S, s ∉ Q →
      (∀ s' ∈ S, s' ∉ Q → orderOf s' < orderOf s → ∀ a' ∈ Q, ∀ g' : X, g'⁻¹ * a' * g' ≠ s') →
    ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g = s → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      s ∈ normalizer (Q : Set X) → s * s = 1 →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card → False

theorem signalizerNineFusionCountInput_of_involution (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountInvolInput) : SignalizerNineFusionCountInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ Q Sc hQK hQ2 hQcard htQ hQS hSH
    hS2 hScard s hsS hsQ hmin a ha g hgs hgH hsNQ hs2Q hsN hρs2 hρs1 h5
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCQ : ∀ y ∈ Q, orderOf y = 2 → centralizer ({y} : Set X) ≤ H := fun y hyQ hyo =>
    S₀.centralizer_le_of_mem_sylow_kernel h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQK hQcard
      htQ hQS hSH hS2 hScard hyQ hyo
  by_cases hs1 : s * s = 1
  · exact hFC X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ Q Sc hQK hQ2 hQcard htQ hQS hSH
      hS2 hScard hCQ s hsS hsQ hmin a ha g hgs hgH hsNQ hs1 hsN hρs2 hρs1 h5
  ·
    have hss2 : IsPGroup 2 (zpowers (s * s)) := hS2.to_le (zpowers_le.mpr (mul_mem hsS hsS))
    have : Nontrivial (zpowers (s * s)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr fun h => hs1 (zpowers_eq_bot.mp h)
    obtain ⟨k, hk⟩ := hss2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card (zpowers (s * s)) by
      rw [hk]; exact dvd_pow_self 2 hk0)
    have hqQ : (q : X) ∈ Q := zpowers_le.mpr hs2Q q.2
    have hqo : orderOf (q : X) = 2 := by rw [Subgroup.orderOf_coe, hq]
    have hCs : centralizer ({s} : Set X) ≤ centralizer ({(q : X)} : Set X) := by
      intro x hx
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp q.2
      rw [mem_centralizer_singleton_iff, ← hm]
      have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp hx
      have hxss : x * (s * s) = s * s * x := by
        calc x * (s * s) = x * s * s := by group
          _ = s * x * s := by rw [hxs]
          _ = s * (x * s) := by group
          _ = s * (s * x) := by rw [hxs]
          _ = s * s * x := by group
      exact (Commute.zpow_right hxss m).eq
    have hs1' : s ≠ 1 := fun h => hsQ (h ▸ one_mem Q)
    obtain ⟨N, hNs, hsN', ⟨θN⟩⟩ := S₀.exists_coreSection_of_conj h33 h35 hT13 hML hSch hMH hMpc
      hHN θ hsup (hQK.trans inf_le_left) (hQK.trans inf_le_right) hQ2 htQ ha hgs hs1'
    have hNH : N ≤ H := hNs.trans (hCs.trans (hCQ q hqQ hqo))
    exact S₀.false_of_cover_of_centralizer_of_normal h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ
      (hS2.to_le (zpowers_le.mpr hsS)) (hSH hsS) hρs1 hNs hsN' θN le_rfl hNH
      (sup_eq_left.mpr (map_subtype_le _))

end CFSG.ComponentClassification.SolMax
