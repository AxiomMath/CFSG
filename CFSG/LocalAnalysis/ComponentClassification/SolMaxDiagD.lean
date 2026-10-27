module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36K

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem nonempty_coreQuot_of_le_centralizer [Finite X] {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {e₀ : X} (he₀H : e₀ ∈ H) (he₀2 : e₀ * e₀ = 1)
    (he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4) {k : ℕ} (hk : 5 ≤ k) (hmk : m = k + 4)
    {N : Subgroup X} (hNH : N ≤ H) (hNC : N ≤ centralizer ({e₀} : Set X)) (hN : ⁅N, N⁆ = N)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k)) :
    Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin k)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥N with hOdef
  have hNM : N ≤ normalizer (M : Set X) := hNH.trans hHN
  set f : ↥N →* Perm (Fin m) := ρ.comp (inclusion hNM) with hfdef
  have hrange :
      f.range ≤ (fixAlt (ρ ⟨e₀, hHN he₀H⟩)).map (alternatingGroup (Fin m)).subtype := by
    rintro _ ⟨y, rfl⟩
    have hy : (y : X) ∈ oddGen N := by rw [oddGen_eq_of_perfect hN]; exact y.2
    exact rho_mem_fixAlt_of_mem_oddGen (hHN he₀H) he₀2 he₀4.le hNM hNC hy (hNM y.2)
  have hmk' : m - (ρ ⟨e₀, hHN he₀H⟩).support.card = k := by omega
  have hcard1 : Nat.card f.range ≤ k.factorial / 2 := by
    have h1 := card_le_of_le hrange
    rw [card_map_of_injective (alternatingGroup (Fin m)).subtype_injective,
      card_fixAlt (by omega), hmk'] at h1
    exact h1
  have hkerO : f.ker ≤ O := by
    intro z hz
    have h1 : ρ ⟨(z : X), hHN (hNH z.2)⟩ = 1 := hz
    obtain ⟨o, ho, hoz⟩ := mem_coreNOf_of_rho_eq_one hρ hHN hker hNH z.2 h1
    have h2 : o = z := Subtype.ext hoz
    rw [← h2]
    exact ho
  have hcard2 : Nat.card f.ker ≤ Nat.card O := card_le_of_le hkerO
  have hcardN : Nat.card ↥N = Nat.card f.range * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hcardO : Nat.card ↥N = Nat.card (↥N ⧸ O) * Nat.card O :=
    card_eq_card_quotient_mul_card_subgroup O
  have hq : Nat.card (↥N ⧸ O) ≤ k.factorial / 2 := by
    have h5 : 0 < Nat.card O := Nat.card_pos
    have h6 : Nat.card (↥N ⧸ O) * Nat.card O ≤ (k.factorial / 2) * Nat.card O := by
      rw [← hcardO, hcardN]
      exact Nat.mul_le_mul hcard1 hcard2
    exact Nat.le_of_mul_le_mul_right h6 h5
  have hZ : center (↥N ⧸ O) = ⊥ := by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h1 := card_eq_card_quotient_mul_card_subgroup (center (↥N ⧸ O))
    rw [Nat.card_congr ((Sol78.coreQuotientCenterEquiv ↥N).trans ψ).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin] at h1
    have h3 : 0 < k.factorial / 2 := Nat.div_pos (by
      have := Nat.self_le_factorial k
      omega) (by norm_num)
    have h4 : (k.factorial / 2) * Nat.card (center (↥N ⧸ O)) ≤ (k.factorial / 2) * 1 := by
      rw [mul_one, ← h1]
      exact hq
    exact (Subgroup.card_le_one_iff_eq_bot _).mp (Nat.le_of_mul_le_mul_left h4 h3)
  have hZO : Open.fusionZStar ↥N = O := (Sol78.fusionZStar_eq_iff _).mpr hZ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZO).symm.trans ψ⟩

theorem nonempty_coreQuot_of_diagonal [Finite X] {M : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ)
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {e₀ e₁ : X} (he₀H : e₀ ∈ H) (he₀2 : e₀ * e₀ = 1)
    (he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4) (he₁2 : e₁ * e₁ = 1)
    (he₁C : e₁ ∈ centralizer ({e₀} : Set X))
    (hCC : centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) ≤ H)
    (hOC : coreNOf (centralizer ({e₀} : Set X)) ≤ H)
    {L₀ F : Subgroup X} (hL₀C : L₀ ≤ centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hL₀pc : IsPComponent 2
      (L₀.subgroupOf (centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7)) (hFL₀ : F ≤ L₀)
    (hF2 : IsPGroup 2 F) (hFH : normalizer (F : Set X) ≤ H) {DY : Finset (Fin 7)}
    (hDY : DY.card = 4)
    (hFY : ∀ l : ↥L₀, (l : X) ∈ F → ∀ y ∉ DY,
      ((χ (l : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y)
    {N : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hL₀N : L₀ ≤ N ⊔ N.map (MulAut.conj e₁).toMonoidHom)
    (hne : N.map (MulAut.conj e₁).toMonoidHom ≠ N)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)) :
    Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 7)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  obtain ⟨hNsC, hNspc⟩ := isPComponent_conj hNC hNpc he₁C
  have hNsK : N.map (MulAut.conj e₁).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNsC hNpc hNspc (Ne.symm hne)
  have hNsN : N.map (MulAut.conj e₁).toMonoidHom ≤ normalizer (N : Set X) :=
    fun z hz => (hNsK hz).1
  have hL₀NN : L₀ ≤ normalizer (N : Set X) := hL₀N.trans (sup_le le_normalizer hNsN)
  have hNO : coreNOf N ≤ coreNOf (centralizer ({e₀} : Set X)) :=
    pPrimeCore_le_of_isPComponent hNC hNpc
  have hOH : coreNOf N ≤ H := hNO.trans hOC
  have hL₀H : L₀ ≤ H := hL₀C.trans hCC
  have hL₀perf : ⁅L₀, L₀⁆ = L₀ := UnbalancedCorr.commutator_eq_of_isPComponent hL₀C hL₀pc
  have hres := primeResidual_eq_top_of_isPComponent hL₀C hL₀pc
  obtain ⟨ρZ, hρZ⟩ := exists_isPermActionZ (N := N) (by norm_num) (by norm_num) ψ
  obtain ⟨DN, hDN, hDNs⟩ := exists_support_of_diagonal hNC hNpc he₁C hL₀N
    (hL₀C.trans inf_le_left) hL₀perf hres hne χ hρZ hL₀NN hFL₀ hFY
  obtain ⟨c, hcZ, hcF⟩ := exists_three_element hρZ (hFL₀.trans hL₀NN) (hDN.trans hDY) hDNs
  have hcH : (c : X) ∈ H := by
    have h1 : (c : X)⁻¹ ∈ H := by
      refine mem_of_map_conj_le_sup_odd hFH (hFL₀.trans hL₀H) hOH hF2
        (fun f hf => le_normalizer_pPrimeCore (hL₀NN (hFL₀ hf))) (odd_coreNOf N) ?_
      rintro _ ⟨f, hf, rfl⟩
      have ho : (c : X)⁻¹ * (f * c * f⁻¹) ∈ coreNOf N := ⟨_, hcF f hf, rfl⟩
      have h4 : (MulAut.conj (c : X)⁻¹).toMonoidHom f = (c : X)⁻¹ * (f * c * f⁻¹) * f := by
        change (c : X)⁻¹ * f * (c : X)⁻¹⁻¹ = _
        group
      rw [h4]
      exact mul_mem (mem_sup_right ho) (mem_sup_left hf)
    simpa using inv_mem h1
  have hδ : ∀ x ∈ N, x * (e₁ * x * e₁⁻¹) ∈ H := fun x hx =>
    mul_conj_mem he₁C he₁2 hNC hNsK hNO hCC hOC hx
  have hNH : N ≤ H := le_of_conj_mem hN (by norm_num) ψ hOH
    (fun x hx y hy hyH => conj_mem_of_mul_conj_mem hNsK hOH hδ hx hy hyH) hcH hcZ
  exact nonempty_coreQuot_of_le_centralizer hρ hHN hker he₀H he₀2 he₀4 (by norm_num)
    (by norm_num) hNH hNC hN ψ

end CFSG.ComponentClassification.SolMax
