module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11P

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem exists_pumpG_of_data (S : Sig36 X t J n e E D) {e₀ e₁ : X} (he₁2 : e₁ * e₁ = 1)
    (he₁C : e₁ ∈ centralizer ({e₀} : Set X)) {k : ℕ} (hk : 7 ≤ k) {L₀ F : Subgroup X}
    (hL₀C : L₀ ≤ centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hL₀pc : IsPComponent 2
      (L₀.subgroupOf (centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin k)) (hFL₀ : F ≤ L₀) (hFJ : F ≤ J)
    (hF4 : Nat.card F = 4) (hFsq : ∀ x ∈ F, x * x = 1)
    (hFD : ∃ DF : Finset (Fin n), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    {DY : Finset (Fin k)} (hDY4 : DY.card = 4)
    (hFY : ∀ x : ↥L₀, (x : X) ∈ F → ∀ y ∉ DY,
      ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin k)) : Perm (Fin k)) y = y)
    {N : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hL₀N : L₀ ≤ N ⊔ N.map (MulAut.conj e₁).toMonoidHom) {r : ℕ} (hkr : k ≤ r) (hr6 : r ≠ 6)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
    (hcase : r = k ∨ (N.map (MulAut.conj e₁).toMonoidHom = N ∧
      IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({e₁} : Set X))))) :
    ∃ (ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)) (τ' : Perm (Fin r))
      (DN : Finset (Fin r)), S.PumpG e₀ e₁ k L₀ F N r θN ρN τ' DN := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N) (by omega) hr6 θN
  obtain ⟨hNsC, hNspc⟩ := isPComponent_conj hNC hNpc he₁C
  have hNsN : N.map (MulAut.conj e₁).toMonoidHom ≤ normalizer (N : Set X) := by
    by_cases hfix : N.map (MulAut.conj e₁).toMonoidHom = N
    · rw [hfix]
      exact le_normalizer
    · exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hNC hNsC hNpc hNspc
        (Ne.symm hfix) hz).1
  have hL₀NN : L₀ ≤ normalizer (N : Set X) := hL₀N.trans (sup_le le_normalizer hNsN)
  have hperf : ⁅L₀, L₀⁆ = L₀ := UnbalancedCorr.commutator_eq_of_isPComponent hL₀C hL₀pc
  have hL₀q : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Nontrivial (alternatingGroup (Fin k)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact χ.toEquiv.nontrivial
  have hL₀s : L₀ ≤ centralizer ({e₁} : Set X) := hL₀C.trans inf_le_left
  have hne := exists_ne_one_of_pump hNC hNpc he₁C hL₀N hL₀s hperf hL₀q (by omega) hρN hL₀NN
  have hcase' : r = k ∨ ∃ t' : X, t' ∈ normalizer (N : Set X) ∧ t' * t' = 1 ∧ L₀ ≤ N ∧
      L₀ ≤ centralizer ({t'} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({t'} : Set X))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨e₁, mem_normalizer_iff_map_conj_eq.mpr hfix, he₁2, ?_, hL₀s, hpc⟩
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
  obtain ⟨τ', hτ'k, ψ, hψ⟩ := exists_image_equiv hk hkr hr6 θN hρN hL₀NN
    (primeResidual_eq_top_of_isPComponent hL₀C hL₀pc) hperf (Fintype.card_fin k) χ hne hcase'
  obtain ⟨DN, hDN4, hDNfix, hDNs⟩ := exists_support_of_mulEquiv_fixAlt hk
    (Fintype.card_fin k) hτ'k (χ.symm.trans ψ) DY
  refine ⟨ρN, τ', DN, ⟨hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hNC, hNpc, hL₀N, hL₀NN, hkr, hρN,
    hcase, hτ'k, ⟨ψ, hψ⟩, by rw [hDN4, hDY4], hDNfix, ?_⟩⟩
  intro x hx ω hω
  have h1 := hDNs (χ ((⟨x, hFL₀ hx⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)) (hFY ⟨x, hFL₀ hx⟩ hx) ω hω
  have h2 : (χ.symm.trans ψ) (χ ((⟨x, hFL₀ hx⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀)) =
      ψ ((⟨x, hFL₀ hx⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    change ψ (χ.symm (χ _)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h2, hψ ⟨x, hFL₀ hx⟩] at h1
  exact h1

end Sig36

end CFSG.ComponentClassification.SolMax
