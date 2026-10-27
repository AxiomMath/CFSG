module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11D
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFForm

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerCaseOneConjugateElevenFormInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)) (E : Subgroup X) (D : Finset (Fin 11)),
    Sig36 X t J 11 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)), IsPermAction θ ρ →
    ∀ Q : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
        normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
    ∀ (a g : X), a ∈ Q → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      ∀ hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g⁻¹ * a * g ∈ normalizer (Q : Set X) →
      ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨g⁻¹ * a * g, hHN hs⟩ = 1 → ρ ⟨g⁻¹ * a * g, hHN hs⟩ ≠ 1 →
    ∀ (x : X) (hx : x ∈ M), x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X)) → x * x = 1 →
      (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      FourForm (ρ ⟨g⁻¹ * a * g, hHN hs⟩) (ρ ⟨x, le_normalizer hx⟩) →
    ∀ hx' : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card = 4 ∧
        centralizer ({g * x * g⁻¹} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem strongClosure_of_conjugate_eleven_form
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hMult : TBLit.HeldTrivialMultiplier) (hR : SignalizerCaseOneConjugateElevenFormInput)
    (hW : Sol78.signalizerCompletion E E ≠ ⊥)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc) :
    ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g ∈ Sc → g⁻¹ * a * g ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hQH : Q ≤ H := hQK.trans inf_le_left
  have hQc : Q ≤ UnbalancedLayer.coreActionKernel M := hQK.trans inf_le_right
  have hA := S.claimA_M_eleven h33 h35 hT13 hML hSch hPump hN1 hMult hMH hMpc hJM hHN hsup
    hρ
  have hNT : ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ → normalizer (T : Set X) ≤ H :=
    fun T hTQ hT1 => S.normalizer_le_of_le_Q h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup hρ hA hQH
      hQc hQ2 htQ hTQ hT1
  have hQeq : ∀ y ∈ Sc, y ∈ UnbalancedLayer.coreActionKernel M → y ∈ Q := by
    intro y hyS hyK
    set P : Subgroup X := Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) with hPdef
    have hQP : Q ≤ P := le_inf hQS hQK
    have hP2 : IsPGroup 2 P := hS2.to_le inf_le_left
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hPdvd : Nat.card P ∣ Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) :=
      card_dvd_of_le inf_le_right
    have hkle : k ≤ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 := by
      rw [hk] at hPdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hPdvd
    have hcard : Nat.card P ≤ Nat.card Q := by
      rw [hk, hQcard]
      exact Nat.pow_le_pow_right (by norm_num) hkle
    have hPQ : P = Q := (Subgroup.eq_of_le_of_card_ge hQP hcard).symm
    have hyP : y ∈ P := ⟨hyS, hSH hyS, hyK⟩
    rwa [hPQ] at hyP
  intro a ha g hbS
  by_contra hbQ
  set b := g⁻¹ * a * g with hbdef
  have hbH : b ∈ H := hSH hbS
  have hbNQ : b ∈ normalizer (Q : Set X) := by
    rw [mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hQeq _ (mul_mem (mul_mem hbS (hQS hq)) (inv_mem hbS))
        (hρ.conj_mem_coreActionKernel (by omega) (hHN hbH) (hQc hq))
    · intro hq
      have h1 : q = b⁻¹ * (b * q * b⁻¹) * b⁻¹⁻¹ := by group
      rw [h1]
      exact hQeq _ (mul_mem (mul_mem (inv_mem hbS) (hQS hq)) (inv_mem (inv_mem hbS)))
        (hρ.conj_mem_coreActionKernel (by omega) (inv_mem (hHN hbH)) (hQc hq))
  have hb2 : IsPGroup 2 (zpowers b) := hS2.to_le (zpowers_le.mpr hbS)
  have hρb : ρ ⟨b, hHN hbH⟩ ≠ 1 := fun h1 =>
    hbQ (hQeq b hbS (hρ.mem_coreActionKernel _ h1))
  obtain ⟨m, hm⟩ := hb2.exists_card_eq
  have hob : orderOf b = 2 ^ m := by rw [← Nat.card_zpowers]; exact hm
  have hdvd : orderOf (ρ ⟨b, hHN hbH⟩) ∣ 2 ^ m :=
    (orderOf_map_dvd ρ _).trans (by rw [Subgroup.orderOf_mk, hob])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj1 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hρb hj
  set a' := a ^ 2 ^ (j - 1) with ha'def
  have ha'Q : a' ∈ Q := pow_mem ha _
  have hsb : g⁻¹ * a' * g = b ^ 2 ^ (j - 1) := by
    rw [hbdef, ha'def]
    have h1 : g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ := by rw [inv_inv]
    rw [h1, conj_pow, inv_inv]
  have hsH : g⁻¹ * a' * g ∈ H := by rw [hsb]; exact pow_mem hbH _
  have hsNQ : g⁻¹ * a' * g ∈ normalizer (Q : Set X) := by rw [hsb]; exact pow_mem hbNQ _
  have hρs : ρ ⟨g⁻¹ * a' * g, hHN hsH⟩ = ρ ⟨b, hHN hbH⟩ ^ 2 ^ (j - 1) := by
    have h1 : (⟨g⁻¹ * a' * g, hHN hsH⟩ : ↥(normalizer (M : Set X))) =
        ⟨b, hHN hbH⟩ ^ 2 ^ (j - 1) :=
      Subtype.ext (show g⁻¹ * a' * g = b ^ 2 ^ (j - 1) from hsb)
    rw [h1, map_pow]
  have hσ2 : ρ ⟨g⁻¹ * a' * g, hHN hsH⟩ * ρ ⟨g⁻¹ * a' * g, hHN hsH⟩ = 1 := by
    rw [hρs, ← pow_two, ← pow_mul, ← pow_succ, show j - 1 + 1 = j by omega, ← hj,
      pow_orderOf_eq_one]
  have hσ1 : ρ ⟨g⁻¹ * a' * g, hHN hsH⟩ ≠ 1 := by
    intro h1
    rw [hρs] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  by_cases hgH : g ∈ H
  ·
    apply hσ1
    have h1 := hρ.conj_mem_coreActionKernel (by omega) (inv_mem (hHN hgH)) (hQc ha'Q)
    rw [inv_inv] at h1
    exact hρ.eq_one_of_mem_coreActionKernel (by omega) h1
  ·
    have hs2 : IsPGroup 2 (zpowers (g⁻¹ * a' * g)) := by
      rw [hsb]
      exact hb2.to_le (zpowers_le.mpr (pow_mem (mem_zpowers b) _))
    obtain ⟨x, hxM, hxo, hx2, hx4, hxf⟩ :=
      hρ.exists_four_involution_of_two_form (by omega) (hHN hsH) hs2 hσ2
    have ha'1 : a' ≠ 1 := by
      intro h1
      apply hσ1
      have h2 : (⟨g⁻¹ * a' * g, hHN hsH⟩ : ↥(normalizer (M : Set X))) = 1 :=
        Subtype.ext (show g⁻¹ * a' * g = 1 by rw [h1]; group)
      rw [h2, map_one]
    have hx'o := conj_mem_oddGen_centralizer (g := g) hxo
    have h1 : g * (g⁻¹ * a' * g) * g⁻¹ = a' := by group
    rw [h1] at hx'o
    have hCa : centralizer ({a'} : Set X) ≤ H := by
      rw [← centralizer_zpowers_eq']
      exact (Subgroup.centralizer_le_normalizer _).trans
        (hNT (zpowers a') (zpowers_le.mpr ha'Q) (zpowers_ne_bot.mpr ha'1))
    have hx'H : g * x * g⁻¹ ∈ H := hCa (oddGen_le _ hx'o)
    obtain ⟨h4', hC'⟩ := hR X t J e E D S hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard
      htQ hA hNT a' g ha'Q hgH hsH hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx'H
    exact hgH (S.mem_of_conj_of_four (signalizerConjKernelExclusion_of_inputs h33 h35 hT13 hML hSch)
      (by omega) hMH hMpc hHN hsup hρ hA hxM hx2 hx4 hx'H h4' hC')

end Sig36

theorem signalizerCaseOneStrongClosureElevenInput_of_conjugateForm
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hMult : TBLit.HeldTrivialMultiplier) (hR : SignalizerCaseOneConjugateElevenFormInput) :
    SignalizerCaseOneStrongClosureElevenInput := by
  intro X _ _ _ t J e E D S hW M hMH hMpc hJM hHN hθ hsup Q Sc hQK hQ2 hQcard htQ hQS hSH hS2 _
  obtain ⟨θ⟩ := hθ
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by norm_num) (by norm_num) θ
  exact S.strongClosure_of_conjugate_eleven_form h33 h35 hT13 hML hSch hPump hN1 hMult hR hW
    hMH hMpc hJM hHN hsup hρ hQK hQ2 hQcard htQ hQS hSH hS2

end CFSG.ComponentClassification.SolMax
