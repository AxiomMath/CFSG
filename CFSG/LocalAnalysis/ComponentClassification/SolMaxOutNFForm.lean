module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutA5
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFKill
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36Y
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

section Form

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def FourForm (σ δ : Perm α) : Prop :=
  (6 ≤ σ.support.card ∧ ∃ i ∈ σ.support, ∃ i' ∈ σ.support, i' ≠ i ∧ i' ≠ σ i ∧
      δ = swap i (σ i) * swap i' (σ i')) ∨
    (σ.support.card < 6 ∧ δ.support ⊆ σ.supportᶜ)

theorem exists_four_mem_oddCentGen_form {σ : Perm α} (hσ : σ * σ = 1)
    (hcard : 9 ≤ Fintype.card α) :
    ∃ δ ∈ oddCentGen σ, δ * δ = 1 ∧ δ.support.card = 4 ∧ FourForm σ δ := by
  classical
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  by_cases h6 : 6 ≤ σ.support.card
  ·
    obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
    have h₁ : σ a₁ ≠ a₁ := Perm.mem_support.mp ha₁
    obtain ⟨a₂, ha₂, ha₂n⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a₁, σ a₁}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₂n
    have h₂ : σ a₂ ≠ a₂ := Perm.mem_support.mp ha₂
    obtain ⟨a₃, ha₃, ha₃n⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a₁, σ a₁, a₂, σ a₂}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₃n
    have h₃ : σ a₃ ≠ a₃ := Perm.mem_support.mp ha₃
    have hmem := pair_mem_oddCentGen hσ h₁ h₂ h₃ ha₂n.1 ha₂n.2 ha₃n.1 ha₃n.2.1 ha₃n.2.2.1
      ha₃n.2.2.2
    have hac : a₂ ≠ a₃ := Ne.symm ha₃n.2.2.1
    have hbc : σ a₂ ≠ a₃ := Ne.symm ha₃n.2.2.2
    have had : a₂ ≠ σ a₃ := fun h => ha₃n.2.2.2 (by rw [h, hσσ])
    have hbd : σ a₂ ≠ σ a₃ := fun h => hac (σ.injective h)
    exact ⟨_, hmem, swap_mul_swap_mul_self hac had hbc hbd,
      card_support_swap_mul_swap (Ne.symm h₂) (Ne.symm h₃) hac had hbc hbd,
      Or.inl ⟨h6, a₂, ha₂, a₃, ha₃, ha₃n.2.2.1, ha₃n.2.2.2, rfl⟩⟩
  ·
    push Not at h6
    have hF : 4 ≤ (σ.supportᶜ).card := by
      rw [Finset.card_compl]
      omega
    have hfix : ∀ x ∈ σ.supportᶜ, σ x = x := fun x hx => by
      rw [Finset.mem_compl, Perm.mem_support, not_not] at hx
      exact hx
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (σ.supportᶜ).card)
    obtain ⟨b, hb, hbn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a}) (t := σ.supportᶜ) (by rw [Finset.card_singleton]; omega)
    obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a, b}) (t := σ.supportᶜ) (lt_of_le_of_lt Finset.card_le_two (by omega))
    obtain ⟨d, hd, hdn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a, b, c}) (t := σ.supportᶜ) (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn hcn hdn
    have hab : a ≠ b := Ne.symm hbn
    have hac : a ≠ c := Ne.symm hcn.1
    have hbc : b ≠ c := Ne.symm hcn.2
    have had : a ≠ d := Ne.symm hdn.1
    have hbd : b ≠ d := Ne.symm hdn.2.1
    have hcd : c ≠ d := Ne.symm hdn.2.2
    have hsub : (swap a b * swap c d).support ⊆ σ.supportᶜ := by
      intro ω hω
      have h1 := Perm.support_mul_le (swap a b) (swap c d) hω
      rw [Finset.sup_eq_union, Finset.mem_union, Perm.support_swap hab, Perm.support_swap hcd,
        Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with (rfl | rfl) | (rfl | rfl)
      · exact ha
      · exact hb
      · exact hc
      · exact hd
    exact ⟨_, fix_pair_mem_oddCentGen (hfix a ha) (hfix b hb) (hfix c hc) (hfix d hd) hab hac had
      hbc hbd hcd, swap_mul_swap_mul_self hac had hbc hbd,
      card_support_swap_mul_swap hab hcd hac had hbc hbd, Or.inr ⟨h6, hsub⟩⟩

end Form

variable {X : Type} [Group X]

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_four_involution_of_two_form (hρ : IsPermAction θ ρ) [Finite X]
    (hr : 9 ≤ r) {s : X} (hs : s ∈ normalizer (M : Set X)) (hs2 : IsPGroup 2 (zpowers s))
    (hσ2 : ρ ⟨s, hs⟩ * ρ ⟨s, hs⟩ = 1) :
    ∃ (e : X) (he : e ∈ M), e ∈ oddGen (centralizer ({s} : Set X)) ∧ e * e = 1 ∧
      (ρ ⟨e, le_normalizer he⟩).support.card = 4 ∧
      FourForm (ρ ⟨s, hs⟩) (ρ ⟨e, le_normalizer he⟩) := by
  classical
  obtain ⟨δ, hδ, hδ2, hδ4, hδf⟩ :=
    exists_four_mem_oddCentGen_form hσ2 (by rw [Fintype.card_fin]; exact hr)
  obtain ⟨q, hq, hqo, hρq⟩ := hρ.exists_lift_oddCentGen_of_two (by omega) hs hs2 hδ
  obtain ⟨b, c, hc, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
  have heM : q ^ c ∈ M := pow_mem hq c
  have hρe : ρ ⟨q ^ c, le_normalizer heM⟩ = δ := by
    have h1 : (⟨q ^ c, le_normalizer heM⟩ : ↥(normalizer (M : Set X))) =
        ⟨q, le_normalizer hq⟩ ^ c := rfl
    rw [h1, map_pow, hρq]
    obtain ⟨j, rfl⟩ := hc
    rw [pow_succ, pow_mul, sq, hδ2, one_pow, one_mul]
  refine ⟨q ^ c, heM, pow_mem hqo c, ?_, by rw [hρe]; exact hδ4, by rw [hρe]; exact hδf⟩
  have hee : ρ ⟨q ^ c * q ^ c, le_normalizer (mul_mem heM heM)⟩ = 1 := by
    have h1 : (⟨q ^ c * q ^ c, le_normalizer (mul_mem heM heM)⟩ : ↥(normalizer (M : Set X))) =
        ⟨q ^ c, le_normalizer heM⟩ * ⟨q ^ c, le_normalizer heM⟩ := rfl
    rw [h1, map_mul, hρe, hδ2]
  have hcore : q ^ c * q ^ c ∈ (pPrimeCore 2 ↥M).map M.subtype :=
    mem_core_of_mem_coreActionKernel hρ (by omega) (mul_mem heM heM)
      (hρ.mem_coreActionKernel _ hee)
  have hodd := odd_orderOf_of_mem_oddCoreIn hcore
  have h2pow : orderOf (q ^ c * q ^ c) ∣ 2 ^ b := by
    have h1 : (q ^ c) ^ 2 ^ b = 1 := by
      rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    rw [← sq]
    exact (orderOf_pow_dvd 2).trans (orderOf_dvd_of_pow_eq_one h1)
  have h1 : orderOf (q ^ c * q ^ c) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hodd)) h2pow
  exact orderOf_eq_one_iff.mp h1

@[expose] def SignalizerCaseOneConjugateFormInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → 13 ≤ n → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)), IsPermAction θ ρ →
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

@[expose] def SignalizerCaseOneConjugateOutsideKernelFormInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → 11 ≤ n → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)), IsPermAction θ ρ →
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
      g * x * g⁻¹ ∉ M → g⁻¹ * a * g * (g⁻¹ * a * g) = 1 →
      n - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card < 5 →
    ∀ (y : X) (hy : y ∈ M), y * y = 1 → y * (g * x * g⁻¹) = g * x * g⁻¹ * y →
      ρ ⟨y, le_normalizer hy⟩ = ρ ⟨g * x * g⁻¹, hHN hx'⟩ →
      y ∈ oddGen (centralizer ({g * x * g⁻¹} : Set X) ⊓ centralizer ({a} : Set X)) →
      y * (g * x * g⁻¹) ∈ oddGen (centralizer ({a} : Set X) ⊓
        (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
          UnbalancedLayer.coreActionKernel M)) →
      centralizer ({y * (g * x * g⁻¹)} : Set X) ≤
        normalizer (Sol78.signalizerCompletion E E : Set X) →
      False

theorem signalizerCaseOneConjugateFormInput_of_kernelForm (hD2 : SignalizerConjKernelExclusion)
    (hKF : SignalizerCaseOneConjugateOutsideKernelFormInput) :
    SignalizerCaseOneConjugateFormInput := by
  intro X _ _ _ t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT a g
    ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx'
  have hn9 := S.nine_le
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  by_cases hx'M : g * x * g⁻¹ ∈ M
  · have hCx := hA x hxM hx2 hx4
    have hxno : x ∉ oddGen (centralizer ({x} : Set X)) :=
      not_mem_oddGen_of_four (le_normalizer hxM) hx2 hx4 (hCx.trans hHN)
    have hx'o : g * x * g⁻¹ ∉ oddGen (centralizer ({g * x * g⁻¹} : Set X)) := by
      intro h
      have h1 := conj_mem_oddGen_centralizer (g := g⁻¹) h
      have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [h2] at h1
      exact hxno h1
    have hx1 : x ≠ 1 := by
      rintro rfl
      have h1 : ρ ⟨1, le_normalizer hxM⟩ = 1 := map_one ρ
      rw [h1, Perm.support_one, Finset.card_empty] at hx4
      omega
    have hx'1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h4 := hρ.card_support_eq_four_of_not_mem_oddGen (by omega) hx'M hx'2 hx'1 hx'o
    exact ⟨h4, hA _ hx'M hx'2 h4⟩
  · exfalso
    have hs2 := S.mul_self_eq_one_of_conjugate hD2 hMH hMpc hHN hsup hρ hQK hQ2 hQcard hA hNT ha hs
      hsNQ hσ2 hσ1
    by_cases h5 : 5 ≤ n - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card
    · exact S.false_of_conjugate_outside_of_five hD2 (by omega) hMH hMpc hHN hsup hρ hQK hQ2 hQcard
        hA hNT ha hgH hs hsNQ hσ2 hσ1 hxM hxo hx2 hx4 hx' h5
    · have ha1 : a ≠ 1 := by
        rintro rfl
        apply hσ1
        have h1 : (⟨g⁻¹ * 1 * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 :=
          Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
        rw [h1, map_one]
      have hcard : (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card ≤ n := by
        have := Finset.card_le_univ (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support
        rwa [Fintype.card_fin] at this
      obtain ⟨y, hyM, hy2, hyx', hρy, hyo, hko, hCk⟩ := exists_kernel_involution hMH hMpc hHN
        (by omega) hρ hQK hQ2 hQcard hNT ha ha1 hxo hx2 hx' hx'M (by omega)
      exact hKF X t J n e E D S (by omega) hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ
        hA hNT a g ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 (by omega) y hyM hy2
        hyx' hρy hyo hko hCk

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem strongClosure_of_conjugateForm (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hR : SignalizerCaseOneConjugateFormInput) (hn : 13 ≤ n)
    (hW : Sol78.signalizerCompletion E E ≠ ⊥)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {Q Sc : Subgroup X}
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
  have hA := S.claimA_M_of_sup h33 h35 hT13 hML hSch hPump hN1 hn hMH hMpc hJM hHN hsup hρ
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
    obtain ⟨h4', hC'⟩ := hR X t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard
      htQ hA hNT a' g ha'Q hgH hsH hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx'H
    exact hgH (S.mem_of_conj_of_four (signalizerConjKernelExclusion_of_inputs h33 h35 hT13 hML hSch)
      (by omega) hMH hMpc hHN hsup hρ hA hxM hx2 hx4 hx'H h4' hC')

end Sig36

theorem signalizerCaseOneStrongClosureNarrowInput_of_conjugateForm
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hR : SignalizerCaseOneConjugateFormInput)
    (hR11 : SignalizerCaseOneStrongClosureElevenInput) :
    SignalizerCaseOneStrongClosureNarrowInput := by
  intro X _ _ _ t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard _ _
  by_cases h13 : 13 ≤ n
  · exact S.strongClosure_of_conjugateForm h33 h35 hT13 hML hSch hPump hN1 hR h13 hW hMH
      hMpc hJM hHN hsup hρ hQK hQ2 hQcard htQ hQS hSH hS2
  · have h11 : n = 11 := by obtain ⟨k, hk⟩ := S.pair.2.1; omega
    subst h11
    exact hR11 X t J e E D S hW M hMH hMpc hJM hHN ⟨θ⟩ hsup Q Sc hQK hQ2 hQcard htQ hQS hSH
      hS2 hScard

theorem signalizerTrivialityInput_of_residues_conjugateForm
    (hmax : SolAltLit.MaximalAltComponentInput) (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hSwap : SignalizerSwapAltExclusion)
    (hGT : Sol78.StronglyClosedResidualInput) (hA : SignalizerClaimASmallInput)
    (h2 : SignalizerCaseTwoFinishInput) (hR : SignalizerCaseOneConjugateFormInput)
    (hR11 : SignalizerCaseOneStrongClosureElevenInput) (h9 : SignalizerNineInput) :
    SolAltLit.SignalizerTrivialityInput :=
  signalizerTrivialityInput_of_residues_narrow hmax hbal hPump hN1 hsmall hT13 hML hSch hSwap hGT
    hA h2
    (signalizerCaseOneStrongClosureNarrowInput_of_conjugateForm
      (balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall)
      (signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall) hT13 hML hSch hPump hN1 hR
      hR11) h9

end CFSG.ComponentClassification.SolMax
