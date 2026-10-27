module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBF

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

namespace SwapP2

theorem exists_image_equiv' [Finite X] {M Je : Subgroup X} {r k : ℕ} (hk : 5 ≤ k)
    (hkr : k ≤ r) (hr6 : r ≠ 6) (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ)
    (hJeN : Je ≤ normalizer (M : Set X)) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Je = ⊤)
    (hJeperf : ⁅Je, Je⁆ = Je) (χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup (Fin k))
    (hne : ∃ x : ↥Je, ρ ⟨x, hJeN x.2⟩ ≠ 1)
    (hcase : r = k ∨ ∃ t : X, t ∈ normalizer (M : Set X) ∧ t * t = 1 ∧ Je ≤ M ∧
      Je ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({t} : Set X)))) :
    ∃ τ : Perm (Fin r), r - τ.support.card = k ∧
      ∃ ψ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* fixAlt τ, ∀ x : ↥Je,
        (((ψ (x : ↥Je ⧸ pPrimeCore 2 ↥Je) : fixAlt τ) : alternatingGroup (Fin r)) :
          Perm (Fin r)) = ρ ⟨x, hJeN x.2⟩ := by
  classical
  rcases hcase with hrk | ⟨t, htM, htt, hJeM, hJeC, hJepc⟩
  · have hA : ∀ x : ↥Je, ρ (inclusion hJeN x) ∈ alternatingGroup (Fin r) := fun x =>
      IsPermAction.mem_alternatingGroup_of_perfect hJeN hJeperf x.2
    let φ : ↥Je →* alternatingGroup (Fin r) :=
      (ρ.comp (inclusion hJeN)).codRestrict (alternatingGroup (Fin r)) hA
    obtain ⟨x₀, hx₀⟩ := hne
    have hφ : φ x₀ ≠ 1 := fun h => hx₀ (congrArg Subtype.val h)
    have hQ : ∀ x, φ x ∈ fixAlt (1 : Perm (Fin r)) := by
      intro x
      rw [mem_fixAlt]
      simp
    have hQc : Nat.card (fixAlt (1 : Perm (Fin r))) ≤ k.factorial / 2 := by
      rw [card_fixAlt (by simp; omega)]
      simp [hrk]
    obtain ⟨ψ, hψ⟩ := exists_coreQuot_equiv_of_hom hres hk χ φ ⟨x₀, hφ⟩ hQ hQc
    refine ⟨1, by simp [hrk], ψ, fun x => ?_⟩
    rw [hψ x]
    rfl
  · exact exists_image_equiv_of_component hk (by omega) hr6 θM hρ hJeN hres
      (Fintype.card_fin k) χ hne htM htt hJeM hJeC hJepc

theorem le_coreActionKernel_of_commute_pump' [Finite X] {r e₀ : X} {A B N : Subgroup X} {k m : ℕ}
    (hk : 5 ≤ k) (he₀r : e₀ ∈ centralizer ({r} : Set X)) (he₀o : orderOf e₀ = 2)
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
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m)) (hkm : k ≤ m) (hmk : m ≤ k + 4)
    (hm6 : m ≠ 6)
    (hcase : m = k ∨ (N.map (MulAut.conj e₀).toMonoidHom = N ∧
      IsPComponent 2 (A.subgroupOf (N ⊓ centralizer ({e₀} : Set X))))) :
    B ≤ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq, ← he₀o, pow_orderOf_eq_one]
  have hcase' : m = k ∨ ∃ t : X, t ∈ normalizer (N : Set X) ∧ t * t = 1 ∧ A ≤ N ∧
      A ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (A.subgroupOf (N ⊓ centralizer ({t} : Set X))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨e₀, mem_normalizer_iff_map_conj_eq.mpr hfix, he₀2, ?_,
        hAC.trans inf_le_right, hpc⟩
      have h1 := hAN
      rwa [hfix, sup_idem] at h1
  set Nx := N.map (MulAut.conj e₀).toMonoidHom with hNxdef
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxN : Nx ≤ normalizer (N : Set X) := by
    by_cases h : Nx = N
    · rw [h]
      exact le_normalizer
    · exact fun z hz =>
        (GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm h) hz).1
  have hYN : N ⊔ Nx ≤ normalizer (N : Set X) := sup_le le_normalizer hNxN
  have hAN' : A ≤ normalizer (N : Set X) := hAN.trans hYN
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := N) (by omega) hm6 θN
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAC hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAC).mp hApc
  have hne := exists_ne_one_of_pump hNC hNpc he₀r hAN (hAC.trans inf_le_right) hAperf
    (LocalCores.isQuasisimple_nontrivial hAq) (r := m) (by omega) hρ hAN'
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv' (M := N) (Je := A) hk hkm hm6 θN hρ hAN' hAres
    hAperf χ hne hcase'
  have hsm : τ.support.card ≤ m := by
    have h1 := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at h1
  have h4 : τ.support.card ≤ 4 := by omega
  have h5 : 5 ≤ m - τ.support.card := by omega
  have hρO : ∀ (w : X) (hw : w ∈ (pPrimeCore 2 ↥A).map A.subtype),
      ρ ⟨w, hAN' (map_subtype_le _ hw)⟩ = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hψ w
    rw [(QuotientGroup.eq_one_iff w).mpr hw, map_one] at h1
    have h2 : ρ ⟨(w : X), hAN' w.2⟩ = 1 := by rw [← h1]; rfl
    exact h2
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
  set φ : ↥B →* Perm (Fin m) := ρ.comp (inclusion hBN) with hφdef
  have hBperf : ⁅B, B⁆ = B := UnbalancedCorr.commutator_eq_of_isPComponent hBC hBpc
  have htop : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hBperf]
  have hPperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hc : ∀ p ∈ φ.range, ∀ σ ∈ fixAlt τ, p * (σ : Perm (Fin m)) = σ * p := by
    rintro _ ⟨x, rfl⟩ σ hσ
    obtain ⟨q, hq⟩ := ψ.surjective ⟨σ, hσ⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hzσ : ρ ⟨z, hAN' z.2⟩ = (σ : Perm (Fin m)) := by rw [← hψ z, hq]
    have hw := hBA x x.2 z z.2
    have hw1 := hρO _ hw
    have e1 : (⟨(x : X) * z * (x : X)⁻¹ * (z : X)⁻¹, hAN' (map_subtype_le _ hw)⟩ :
        ↥(normalizer (N : Set X))) = ⟨x, hBN x.2⟩ * ⟨z, hAN' z.2⟩ * (⟨x, hBN x.2⟩)⁻¹ *
          (⟨z, hAN' z.2⟩)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hzσ] at hw1
    change ρ ⟨x, hBN x.2⟩ * σ = σ * ρ ⟨x, hBN x.2⟩
    calc ρ ⟨x, hBN x.2⟩ * σ = (ρ ⟨x, hBN x.2⟩ * σ * (ρ ⟨x, hBN x.2⟩)⁻¹ * (σ : Perm (Fin m))⁻¹) *
        (σ * ρ ⟨x, hBN x.2⟩) := by group
      _ = σ * ρ ⟨x, hBN x.2⟩ := by rw [hw1, one_mul]
  have hP := eq_bot_of_perfect_of_commute_fixAlt h4 h5 hPperf hc
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    have h2 : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hP, mem_bot] at h2
    exact h2
  exact hρ.mem_coreActionKernel (hBN hx) h1

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem pumpSide_of_type' (hs : Setting t J n e E D M) (hn : 9 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N₁ : Subgroup X} (hN₁C : N₁ ≤ centralizer ({r} : Set X))
    (hN₁pc : IsPComponent 2 (N₁.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N₁ ⊔ conjBy N₁ e₀) {m : ℕ}
    (θ₁ : ↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m)) (hm : n - 4 ≤ m) (hmn : m ≤ n)
    (hm6 : m ≠ 6)
    (hcase : m = n - 4 ∨ (conjBy N₁ e₀ = N₁ ∧
      IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))))) :
    ∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N₁ ⊔ conjBy N₁ e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
  classical
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein hs.sig.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  obtain ⟨hN₁xC, hN₁xpc⟩ := isPComponent_conj hN₁C hN₁pc he₀r
  have hcc : conjBy (conjBy N₁ e₀) e₀ = N₁ := conjBy_conjBy_of_mul_self N₁ he₀2
  let θ₁x : ↥(conjBy N₁ e₀) ⧸ pPrimeCore 2 ↥(conjBy N₁ e₀) ≃* alternatingGroup (Fin m) :=
    (Sol78.coreQuotCongr (N₁.equivMapOfInjective (MulAut.conj e₀).toMonoidHom
      (MulAut.conj e₀).injective)).symm.trans θ₁
  have hcovx : fixA M e₀ r ≤ conjBy N₁ e₀ ⊔ (conjBy N₁ e₀).map (MulAut.conj e₀).toMonoidHom := by
    change fixA M e₀ r ≤ conjBy N₁ e₀ ⊔ conjBy (conjBy N₁ e₀) e₀
    rw [hcc, sup_comm]
    exact hcov
  have hcasex : m = n - 4 ∨ ((conjBy N₁ e₀).map (MulAut.conj e₀).toMonoidHom = conjBy N₁ e₀ ∧
      IsPComponent 2 ((fixA M e₀ r).subgroupOf (conjBy N₁ e₀ ⊓ centralizer ({e₀} : Set X)))) := by
    rcases hcase with h | ⟨hfix, hpc⟩
    · exact Or.inl h
    · right
      change conjBy (conjBy N₁ e₀) e₀ = conjBy N₁ e₀ ∧ _
      rw [hfix]
      exact ⟨hfix, hpc⟩
  have hmk : m ≤ n - 4 + 4 := by omega
  refine pumpSide_of_commute hs hn hd he₀H hN₁C hN₁pc fun B hBC hBpc hBA => ⟨?_, ?_⟩
  · exact le_coreActionKernel_of_commute_pump' (by omega) he₀r he₀o hArle hArpc χr hBC hBpc hBA
      hN₁C hN₁pc hcov θ₁ hm hmk hm6 hcase
  · exact le_coreActionKernel_of_commute_pump' (by omega) he₀r he₀o hArle hArpc χr hBC hBpc hBA
      hN₁xC hN₁xpc hcovx θ₁x hm hmk hm6 hcasex

end SwapP2

end CFSG.ComponentClassification.SolMax
