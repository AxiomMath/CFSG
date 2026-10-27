module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36N
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33S
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36M
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDichMain

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerClaimASmallInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → (n = 9 ∨ n = 11) → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ (M : Subgroup X) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 2)))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 2))), IsPermAction θ ρ →
      M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      (∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
        g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) →
      ∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)), x * x = 1 →
        (ρ ⟨x, hHN hx⟩).support.card = 4 →
          centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)

@[expose] def SignalizerCaseTwoFinishInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ (M : Subgroup X) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 4)))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 4))), IsPermAction θ ρ →
      M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      (∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
        g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) →
      (∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)), x * x = 1 →
        (ρ ⟨x, hHN hx⟩).support.card = 4 →
          centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ g : X, g * t * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X) →
        g ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∃ P : Sylow 2 X, (P : Subgroup X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      False

@[expose] def SignalizerCaseOneInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → 11 ≤ n → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      J ⊔ FooteLit.oddCoreIn M = M → False

@[expose] def SignalizerNineInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)) →
      J ⊔ FooteLit.oddCoreIn M = M → False

variable {X : Type} [Group X]

theorem odd_orderOf_of_mem_oddCoreIn [Finite X] {H : Subgroup X} {g : X}
    (hg : g ∈ (pPrimeCore 2 ↥H).map H.subtype) : Odd (orderOf g) := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 := orderOf_dvd_natCard (⟨h, hh⟩ : ↥(pPrimeCore 2 ↥H))
  rw [Subgroup.orderOf_mk] at h1
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card)

theorem signalizerCompletionTrivial_of_cases (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hSwap : SignalizerSwapAltExclusion) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hA : SignalizerClaimASmallInput)
    (h2 : SignalizerCaseTwoFinishInput) (h1 : SignalizerCaseOneInput)
    (h9 : SignalizerNineInput) : SignalizerCompletionTrivial := by
  intro X _ _ _ hnab hKP hunb hnU t J n hpair e E hEJ hE hD y hy hyE hyK hyJ
  obtain ⟨D, hD4, hsupp⟩ := hD
  have S : Sig36 X t J n e E D :=
    ⟨hnab, hKP, hunb, hnU, hpair, hEJ, hE, hD4, hsupp⟩
  rw [S.completion_eq_completion_self h33 hy hyE hyK hyJ]
  by_contra hW
  have hn9 := S.nine_le
  obtain ⟨M, m, hMH, hMpc, hJM, hHN, hmodd, hnm, hmn4, ⟨θ⟩, htriv, hkerO⟩ :=
    S.dichotomy h33 h35 hT13 hML hSch hSwap hPump hN1 hW
  have hcases : m = n ∨ m = n + 2 ∨ m = n + 4 := by
    obtain ⟨a, ha⟩ := hmodd
    obtain ⟨b, hb⟩ := S.pair.2.1
    omega
  have hker : n < m → ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g) := fun hlt g hg hgK =>
    odd_orderOf_of_mem_oddCoreIn (hkerO hlt (mem_inf.mpr ⟨hg, hgK⟩))
  have hCt := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  rcases hcases with hm | hm | hm
  ·
    subst hm
    rcases (show m = 9 ∨ 11 ≤ m by obtain ⟨b, hb⟩ := S.pair.2.1; omega) with h | h
    · subst h
      exact h9 X t J e E D S hW M hMH hMpc hJM hHN ⟨θ⟩ (htriv rfl)
    · exact h1 X t J m e E D S h hW M hMH hMpc hJM hHN ⟨θ⟩ (htriv rfl)
  ·
    subst hm
    obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
    have hk := hker (by omega)
    by_cases h13 : 13 ≤ n
    · exact S.false_of_add_two h33 h35 hT13 hML hSch rfl hMH hMpc hJM hHN hk hρ
        (S.claimA_add_two h33 h35 hT13 hML hSch hPump hN1 h13 rfl hMH hJM hHN hk hρ (hHN htH))
    · have hsmall : n = 9 ∨ n = 11 := by obtain ⟨b, hb⟩ := S.pair.2.1; omega
      exact S.false_of_add_two h33 h35 hT13 hML hSch rfl hMH hMpc hJM hHN hk hρ
        (hA X t J n e E D S hsmall hW M θ ρ hρ hMH hMpc hJM hHN hk)
  ·
    subst hm
    obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
    have hk := hker (by omega)
    have hkerO' := hkerO (by omega)
    have hA4 : ∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)),
        x * x = 1 → (ρ ⟨x, hHN hx⟩).support.card = 4 →
          centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
      fun x hx hx2 hx4 => S.centralizer_le_of_four_of_add_four h33 h35 hT13 hML hSch hMH
        hMpc hJM hHN rfl hkerO' hρ hx hx2 hx4
    have hfus : ∀ g : X, g * t * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X) →
        g ∈ normalizer (Sol78.signalizerCompletion E E : Set X) := fun g hg =>
      hρ.mem_of_conj_mem (by omega) hMH hHN hk hA4 ht2 hCt hg
    exact h2 X t J n e E D S hW M θ ρ hρ hMH hMpc hJM hHN hk hA4 hfus
      (exists_sylow_le_of_conj_mem htH ht2 hfus)

theorem signalizerTrivialityInput_of_cases (hmax : SolAltLit.MaximalAltComponentInput)
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hSwap : SignalizerSwapAltExclusion) (hA : SignalizerClaimASmallInput)
    (h2 : SignalizerCaseTwoFinishInput) (h1 : SignalizerCaseOneInput)
    (h9 : SignalizerNineInput) : SolAltLit.SignalizerTrivialityInput :=
  signalizerTrivialityInput_of_completion hmax
    (signalizerCompletionTrivial_of_cases
      (balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall)
      (signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall) hT13 hML hSch hSwap hPump hN1 hA
      h2 h1 h9)

end CFSG.ComponentClassification.SolMax
