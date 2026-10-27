module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11L

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

structure PumpG (S : Sig36 X t J n e E D) (e₀ s : X) (k : ℕ) (L₀ F N : Subgroup X) (r : ℕ)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
    (ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)) (τ' : Perm (Fin r))
    (DN : Finset (Fin r)) : Prop where
  L₀C : L₀ ≤ centralizer ({s} : Set X) ⊓ centralizer ({e₀} : Set X)
  L₀pc : IsPComponent 2 (L₀.subgroupOf (centralizer ({s} : Set X) ⊓ centralizer ({e₀} : Set X)))
  FL₀ : F ≤ L₀
  FJ : F ≤ J
  F4 : Nat.card F = 4
  Fsq : ∀ x ∈ F, x * x = 1
  FD : ∃ DF : Finset (Fin n), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
    ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω
  NC : N ≤ centralizer ({e₀} : Set X)
  Npc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X)))
  L₀N : L₀ ≤ N ⊔ N.map (MulAut.conj s).toMonoidHom
  L₀NN : L₀ ≤ normalizer (N : Set X)
  kr : k ≤ r
  perm : IsPermAction θN ρN
  case : r = k ∨ (N.map (MulAut.conj s).toMonoidHom = N ∧
    IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({s} : Set X))))
  τk : r - τ'.support.card = k
  iso : ∃ ψ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* fixAlt τ', ∀ x : ↥L₀,
    (((ψ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : fixAlt τ') : alternatingGroup (Fin r)) :
      Perm (Fin r)) = ρN ⟨x, L₀NN x.2⟩
  DN4 : DN.card = 4
  DNfix : DN ⊆ τ'.supportᶜ
  Fsupp : ∀ (x : X) (hx : x ∈ F), ∀ ω ∉ DN, ρN ⟨x, L₀NN (FL₀ hx)⟩ ω = ω

theorem exists_pumpG (S : Sig36 X t J n e E D) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hn : 11 ≤ n) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 2))}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 2))} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) {e₀ e₁ : X} (he₀E : e₀ ∈ E) (he₁E : e₁ ∈ E)
    (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) :
    ∃ (L₀ F N : Subgroup X) (r : ℕ) (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
      (ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)) (τ' : Perm (Fin r))
      (DN : Finset (Fin r)), S.PumpG e₀ e₁ (n - 2) L₀ F N r θN ρN τ' DN := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L₀, F, χ, DY, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hDY4, hFY⟩ :=
    S.exists_fixed_layer_pair hn hMH hMpc hJM hρ htM he₀E he₁E he₀1 he₁1 h01
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₁2 : e₁ * e₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₁ he₁E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have he₁o : orderOf e₁ = 2 := orderOf_eq_prime (by rw [sq]; exact he₁2) he₁1
  have he₁C : e₁ ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨e₁, he₁E⟩ ⟨e₀, he₀E⟩))
  have hkodd : Odd (n - 2) := by
    obtain ⟨a, ha⟩ := S.pair.2.1
    exact ⟨a - 1, by omega⟩
  obtain ⟨N, r, hNC, hNpc, hL₀N, -, hkr, -, ⟨θN⟩, hcase⟩ :=
    exists_pump_data hPump hN1 S.nonab S.kProper S.unbal S.notU S.pair.2.2.2.1 he₀o he₁o
      he₁C hL₀C hL₀pc (by omega) hkodd χ
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N) (by omega) (by omega) θN
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
    have : Nontrivial (Fin (n - 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Nontrivial (alternatingGroup (Fin (n - 2))) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact χ.toEquiv.nontrivial
  have hL₀s : L₀ ≤ centralizer ({e₁} : Set X) := hL₀C.trans inf_le_left
  have hne := exists_ne_one_of_pump hNC hNpc he₁C hL₀N hL₀s hperf hL₀q (by omega) hρN hL₀NN
  have hcase' : r = n - 2 ∨ ∃ t' : X, t' ∈ normalizer (N : Set X) ∧ t' * t' = 1 ∧ L₀ ≤ N ∧
      L₀ ≤ centralizer ({t'} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({t'} : Set X))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨e₁, mem_normalizer_iff_map_conj_eq.mpr hfix, he₁2, ?_, hL₀s, hpc⟩
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
  obtain ⟨τ', hτ'k, ψ, hψ⟩ := exists_image_equiv (by omega) hkr (by omega) θN hρN hL₀NN
    (primeResidual_eq_top_of_isPComponent hL₀C hL₀pc) hperf (Fintype.card_fin (n - 2)) χ hne
    hcase'
  obtain ⟨DN, hDN4, hDNfix, hDNs⟩ := exists_support_of_mulEquiv_fixAlt (by omega)
    (Fintype.card_fin (n - 2)) hτ'k (χ.symm.trans ψ) DY
  refine ⟨L₀, F, N, r, θN, ρN, τ', DN, ⟨hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hNC, hNpc,
    hL₀N, hL₀NN, hkr, hρN, hcase, hτ'k, ⟨ψ, hψ⟩, by rw [hDN4, hDY4], hDNfix, ?_⟩⟩
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
