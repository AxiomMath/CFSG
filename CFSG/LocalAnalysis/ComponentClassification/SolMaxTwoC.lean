module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11B

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Nine

variable {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}

theorem false_of_two_components_of_kerZ_two (hρ : IsPermAction θ ρ) [Finite X]
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X)) {e₀ : X} (he₀H : e₀ ∈ H)
    (he₀2 : e₀ * e₀ = 1) (he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 2)
    (hOH : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype ≤ H)
    {N N' : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hN'C : N' ≤ centralizer ({e₀} : Set X))
    (hN'pc : IsPComponent 2 (N'.subgroupOf (centralizer ({e₀} : Set X)))) (hne : N ≠ N')
    (hNH : N ≤ H) (hN'H : N' ≤ H) (hNK : ¬ N ≤ UnbalancedLayer.coreActionKernel M)
    (hN'K : ¬ N' ≤ UnbalancedLayer.coreActionKernel M)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7))
    (ψ' : ↥N' ⧸ Open.fusionZStar ↥N' ≃* alternatingGroup (Fin 7)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀N : e₀ ∈ normalizer (M : Set X) := hHN he₀H
  have hNN : N ≤ normalizer (M : Set X) := hNH.trans hHN
  have hN'N : N' ≤ normalizer (M : Set X) := hN'H.trans hHN
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  have hN'perf : ⁅N', N'⁆ = N' := UnbalancedCorr.commutator_eq_of_isPComponent hN'C hN'pc
  have hρO : ∀ (o : X) (ho : o ∈ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype), ρ ⟨o, hHN (hOH ho)⟩ = 1 := fun o ho =>
    rho_eq_one_of_mem_oddCore_le hρ (by norm_num) he₀N he₀2 (by rw [he₀4]; norm_num)
      (hOH.trans hHN) ho
  set f : ↥N →* Perm (Fin 9) := ρ.comp (inclusion hNN) with hfdef
  set f' : ↥N' →* Perm (Fin 9) := ρ.comp (inclusion hN'N) with hf'def
  have hN'K' : N' ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hN'C hNpc hN'pc hne
  have hcomm : ∀ x : ↥N, ∀ x' : ↥N', f x * f' x' = f' x' * f x := by
    intro x x'
    obtain ⟨-, hK⟩ := UnbalancedLayer.mem_coreActionKernel.mp (hN'K' x'.2)
    obtain ⟨c, hc, hceq⟩ := hK (x : X) x.2
    have hcO : (x : X)⁻¹ * (x' : X)⁻¹ * x * x' ∈
        (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map (centralizer ({e₀} : Set X)).subtype :=
      pPrimeCore_le_of_isPComponent hNC hNpc ⟨c, hc, hceq⟩
    have h1 := hρO _ hcO
    have h2 : (⟨(x : X)⁻¹ * (x' : X)⁻¹ * x * x', hHN (hOH hcO)⟩ : ↥(normalizer (M : Set X))) =
        (inclusion hNN x)⁻¹ * (inclusion hN'N x')⁻¹ * inclusion hNN x * inclusion hN'N x' := rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    change ρ (inclusion hNN x) * ρ (inclusion hN'N x') =
      ρ (inclusion hN'N x') * ρ (inclusion hNN x)
    calc ρ (inclusion hNN x) * ρ (inclusion hN'N x') =
        ρ (inclusion hN'N x') * ρ (inclusion hNN x) *
          ((ρ (inclusion hNN x))⁻¹ * (ρ (inclusion hN'N x'))⁻¹ * ρ (inclusion hNN x) *
            ρ (inclusion hN'N x')) := by group
      _ = ρ (inclusion hN'N x') * ρ (inclusion hNN x) := by rw [h1, mul_one]
  set K₀ := (fixAlt (ρ ⟨e₀, he₀N⟩)).map (alternatingGroup (Fin 9)).subtype with hK₀def
  have hfK : f.range ≤ K₀ := by
    rintro _ ⟨x, rfl⟩
    have hxo : (x : X) ∈ oddGen N := by rw [oddGen_eq_of_perfect hNperf]; exact x.2
    exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 (by rw [he₀4]; norm_num) hNN hNC hxo (hNN x.2)
  have hf'K : f'.range ≤ K₀ := by
    rintro _ ⟨x, rfl⟩
    have hxo : (x : X) ∈ oddGen N' := by rw [oddGen_eq_of_perfect hN'perf]; exact x.2
    exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 (by rw [he₀4]; norm_num) hN'N hN'C hxo (hN'N x.2)
  have hK₀card : Nat.card K₀ = 2520 := by
    rw [hK₀def, card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective,
      card_fixAlt (by rw [he₀4]; norm_num), he₀4]
    rfl
  have hbig : ∀ {P : Subgroup X} (hPN : P ≤ normalizer (M : Set X)), ⁅P, P⁆ = P →
      P ≤ centralizer ({e₀} : Set X) →
      IsPComponent 2 (P.subgroupOf (centralizer ({e₀} : Set X))) →
      ¬ P ≤ UnbalancedLayer.coreActionKernel M →
      (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 7)) →
      2520 ≤ Nat.card (ρ.comp (inclusion hPN)).range := by
    intro P hPN hPperf hPC hPpc hPK ψP
    have h1 := le_card_range_of_fusionZStar hPperf (by norm_num) ψP (ρ.comp (inclusion hPN))
      (fun x hx => hρO _ (pPrimeCore_le_of_isPComponent hPC hPpc ⟨x, hx, rfl⟩)) (by
        by_contra hall
        push Not at hall
        exact hPK fun x hx => hρ.mem_coreActionKernel (hPN hx) (hall ⟨x, hx⟩))
    exact h1
  have hf2520 : 2520 ≤ Nat.card f.range := hbig hNN hNperf hNC hNpc hNK ψ
  have hf'2520 : 2520 ≤ Nat.card f'.range := hbig hN'N hN'perf hN'C hN'pc hN'K ψ'
  have hfeq : f.range = K₀ := eq_of_le_of_card_ge hfK (by rw [hK₀card]; exact hf2520)
  have hf'eq : f'.range = K₀ := eq_of_le_of_card_ge hf'K (by rw [hK₀card]; exact hf'2520)
  have hab : ∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a := by
    rintro a ⟨x, rfl⟩ b hb
    rw [hfeq, ← hf'eq] at hb
    obtain ⟨x', rfl⟩ := hb
    exact hcomm x x'
  have htriv : f.range = ⊥ := by
    have h1 : ⁅f.range, f.range⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact (hab a ha b hb).symm
    have h2 : ⁅f.range, f.range⁆ = f.range := by
      have hNc : commutator ↥N = ⊤ := by
        apply map_injective N.subtype_injective
        rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
        exact hNperf
      rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def, hNc]
    exact h2.symm.trans h1
  have h3 : Nat.card f.range = 1 := by rw [htriv, card_bot]
  omega

end Nine

end CFSG.ComponentClassification.SolMax
