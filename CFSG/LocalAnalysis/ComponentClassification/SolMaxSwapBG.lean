module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

theorem exists_permActionZ_of_diagonal [Finite X] {r e₀ : X} {A N : Subgroup X} {k : ℕ}
    (hk5 : 5 ≤ k) (hk6 : k ≠ 6) (he₀r : e₀ ∈ centralizer ({r} : Set X))
    (hAC : A ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hApc : IsPComponent 2
      (A.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥A ⧸ pPrimeCore 2 ↥A ≃* alternatingGroup (Fin k))
    (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hAN : A ≤ N ⊔ N.map (MulAut.conj e₀).toMonoidHom)
    (hdiag : N.map (MulAut.conj e₀).toMonoidHom ≠ N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k))
    (hAN' : A ≤ normalizer (N : Set X)) :
    ∃ ρ : ↥(normalizer (N : Set X)) →* Perm (Fin k), IsPermActionZ ψN ρ ∧
      (∀ σ : alternatingGroup (Fin k), ∃ z : ↥A, ρ ⟨z, hAN' z.2⟩ = σ) ∧
      (∀ (w : X) (hw : w ∈ (pPrimeCore 2 ↥A).map A.subtype),
        ρ ⟨w, hAN' (map_subtype_le _ hw)⟩ = 1) ∧
      ∀ z : ↥A, ρ ⟨z, hAN' z.2⟩ = 1 → z ∈ pPrimeCore 2 ↥A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  obtain ⟨ρ, hρ⟩ := exists_isPermActionZ (N := N) (by omega) (by omega) ψN
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAC hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAC).mp hApc
  have hne' : ∃ l : ↥A, ρ (inclusion hAN' l) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_coreActionKernel_of_pump hNC hNpc he₀r hAN (hAC.trans inf_le_right) hAperf
      (LocalCores.isQuasisimple_nontrivial hAq) hdiag
    intro l hl
    exact hρ.mem_coreActionKernel hN (hAN' hl) (hall ⟨l, hl⟩)
  have hAalt : ∀ l : ↥A, ρ (inclusion hAN' l) ∈ alternatingGroup (Fin k) := fun l =>
    IsPermAction.mem_alternatingGroup_of_perfect hAN' hAperf l.2
  let φ : ↥A →* alternatingGroup (Fin k) :=
    (ρ.comp (inclusion hAN')).codRestrict (alternatingGroup (Fin k)) hAalt
  obtain ⟨l₀, hl₀⟩ := hne'
  have hφ : φ l₀ ≠ 1 := fun h => hl₀ (congrArg Subtype.val h)
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hQc : Nat.card (⊤ : Subgroup (alternatingGroup (Fin k))) ≤ k.factorial / 2 := by
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨ψA, hψA⟩ := exists_coreQuot_equiv_of_hom hAres (by omega) χ φ ⟨l₀, hφ⟩
    (fun _ => mem_top _) hQc
  refine ⟨ρ, hρ, fun σ => ?_, ?_, fun z hz => ?_⟩
  · obtain ⟨q, hq⟩ := ψA.surjective ⟨σ, mem_top σ⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨z, ?_⟩
    have h1 := hψA z
    rw [hq] at h1
    exact (congrArg Subtype.val h1).symm
  · rintro _ ⟨w, hw, rfl⟩
    have h1 := hψA w
    rw [(QuotientGroup.eq_one_iff w).mpr hw, map_one] at h1
    have h2 : ((φ w : alternatingGroup (Fin k)) : Perm (Fin k)) = 1 := by rw [← h1]; rfl
    exact h2
  · have h1 : φ z = 1 := Subtype.ext hz
    have h2 := hψA z
    rw [h1] at h2
    have h3 : ψA (z : ↥A ⧸ pPrimeCore 2 ↥A) = 1 := Subtype.ext h2
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3

theorem le_coreActionKernel_of_commute_pumpZ [Finite X] {r e₀ : X} {A B N : Subgroup X}
    {k : ℕ} (hk5 : 5 ≤ k) (hk6 : k ≠ 6)
    (he₀r : e₀ ∈ centralizer ({r} : Set X)) (he₀o : orderOf e₀ = 2)
    (hAC : A ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hApc : IsPComponent 2
      (A.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥A ⧸ pPrimeCore 2 ↥A ≃* alternatingGroup (Fin k))
    (hBC : B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hBpc : IsPComponent 2
      (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (hBA : ∀ x ∈ B, ∀ z ∈ A, x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥A).map A.subtype)
    (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hAN : A ≤ N ⊔ N.map (MulAut.conj e₀).toMonoidHom)
    (hdiag : N.map (MulAut.conj e₀).toMonoidHom ≠ N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k)) :
    B ≤ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq, ← he₀o, pow_orderOf_eq_one]
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  set Nx := N.map (MulAut.conj e₀).toMonoidHom with hNxdef
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxK : Nx ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm hdiag)
  have hYN : N ⊔ Nx ≤ normalizer (N : Set X) := sup_le le_normalizer (fun z hz => (hNxK hz).1)
  have hAN' : A ≤ normalizer (N : Set X) := hAN.trans hYN
  obtain ⟨ρ, hρ, hsurj, hρO, -⟩ :=
    exists_permActionZ_of_diagonal hk5 hk6 he₀r hAC hApc χ hNC hNpc hAN hdiag ψN hAN'
  obtain ⟨N₃, hN₃C, hN₃pc, hBN₃, -⟩ := exists_pump_in he₀r he₀o hBC hBpc
  obtain ⟨hN₃xC, hN₃xpc⟩ := isPComponent_conj hN₃C hN₃pc he₀r
  by_cases hcov : N₃ = N ∨ N₃ = Nx
  swap
  · push Not at hcov
    have hK1 : N₃ ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hN₃C hNpc hN₃pc (Ne.symm hcov.1)
    have hcc : (N₃.map (MulAut.conj e₀).toMonoidHom).map (MulAut.conj e₀).toMonoidHom = N₃ :=
      conjBy_conjBy_of_mul_self N₃ he₀2
    have hN₃x : N₃.map (MulAut.conj e₀).toMonoidHom ≠ N := by
      intro h
      apply hcov.2
      rw [hNxdef, ← h, hcc]
    have hK2 : N₃.map (MulAut.conj e₀).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hN₃xC hNpc hN₃xpc (Ne.symm hN₃x)
    exact hBN₃.trans (sup_le hK1 hK2)
  have hBN : B ≤ normalizer (N : Set X) := by
    rcases hcov with h | h
    · rw [h] at hBN₃
      exact hBN₃.trans hYN
    · have hcc : (N.map (MulAut.conj e₀).toMonoidHom).map (MulAut.conj e₀).toMonoidHom = N :=
        conjBy_conjBy_of_mul_self N he₀2
      have h1 : N₃.map (MulAut.conj e₀).toMonoidHom = N := by
        rw [h, hNxdef, hcc]
      rw [h1, h, sup_comm] at hBN₃
      exact hBN₃.trans hYN
  intro x hx
  have hc : ∀ σ ∈ fixAlt (1 : Perm (Fin k)),
      ρ ⟨x, hBN hx⟩ * (σ : Perm (Fin k)) = σ * ρ ⟨x, hBN hx⟩ := by
    intro σ _
    obtain ⟨z, hzσ⟩ := hsurj σ
    have hw := hBA x hx z z.2
    have hw1 := hρO _ hw
    have e1 : (⟨x * z * x⁻¹ * (z : X)⁻¹, hAN' (map_subtype_le _ hw)⟩ :
        ↥(normalizer (N : Set X))) = ⟨x, hBN hx⟩ * ⟨z, hAN' z.2⟩ * (⟨x, hBN hx⟩)⁻¹ *
          (⟨z, hAN' z.2⟩)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hzσ] at hw1
    calc ρ ⟨x, hBN hx⟩ * σ = (ρ ⟨x, hBN hx⟩ * σ * (ρ ⟨x, hBN hx⟩)⁻¹ * (σ : Perm (Fin k))⁻¹) *
        (σ * ρ ⟨x, hBN hx⟩) := by group
      _ = σ * ρ ⟨x, hBN hx⟩ := by rw [hw1, one_mul]
  have h1 : ρ ⟨x, hBN hx⟩ = 1 := by
    refine Perm.ext fun ω => ?_
    rw [Perm.one_apply]
    exact apply_eq_of_commute_fixAlt (by simp; omega) hc (by simp)
  exact hρ.mem_coreActionKernel hN (hBN hx) h1

end SwapP2

end CFSG.ComponentClassification.SolMax
