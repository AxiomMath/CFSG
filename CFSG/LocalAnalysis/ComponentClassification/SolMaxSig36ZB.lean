module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem exists_fixComp_of_sup (S : Sig36 X t J n e E D) {H M : Subgroup X} (hMH : M ≤ H)
    (hMpc : IsPComponent 2 (M.subgroupOf H)) (hHN : H ≤ normalizer (M : Set X))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {c : X}
    (hcH : c ∈ H) (hc2 : c * c = 1) (hc4 : (ρ ⟨c, hHN hcH⟩).support.card = 4) :
    ∃ N : Subgroup X, N ≤ M ⊓ centralizer ({c} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (H ⊓ centralizer ({c} : Set X))) ∧
      (∀ (x : X) (hx : x ∈ M), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (ρ ⟨x, le_normalizer hx⟩).support ⊆ (ρ ⟨c, hHN hcH⟩).supportᶜ → x ∈ N) ∧
      (∀ x ∈ N, ∃ hx : x ∈ M,
        (ρ ⟨x, le_normalizer hx⟩).support ⊆ (ρ ⟨c, hHN hcH⟩).supportᶜ) ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin (n - 4))) := by
  classical
  have hn9 := S.nine_le
  have hσ2 : ρ ⟨c, hHN hcH⟩ * ρ ⟨c, hHN hcH⟩ = 1 := by
    rw [← map_mul, show (⟨c, hHN hcH⟩ : ↥(normalizer (M : Set X))) * ⟨c, hHN hcH⟩ = 1 from
      Subtype.ext hc2, map_one]
  have hσA := mem_alternatingGroup_of_four hσ2 hc4
  obtain ⟨q, hq⟩ := θ.surjective ⟨_, hσA⟩
  obtain ⟨e₁, rfl⟩ := QuotientGroup.mk_surjective q
  have hρe₁ : ρ ⟨e₁, le_normalizer e₁.2⟩ = ρ ⟨c, hHN hcH⟩ := by
    rw [hρ.apply_of_mem (by omega) e₁, hq]
  have hci : coreImage θ e₁.2 = ρ ⟨c, hHN hcH⟩ := by
    change ((θ ((⟨(e₁ : X), e₁.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) :
      Perm (Fin n)) = _
    rw [hq]
  have hce : c * (e₁ : X)⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
    have hmem : c * (e₁ : X)⁻¹ ∈ normalizer (M : Set X) :=
      mul_mem (hHN hcH) (inv_mem (le_normalizer e₁.2))
    refine hρ.mem_coreActionKernel hmem ?_
    have h1 : (⟨c * (e₁ : X)⁻¹, hmem⟩ : ↥(normalizer (M : Set X))) =
        ⟨c, hHN hcH⟩ * (⟨e₁, le_normalizer e₁.2⟩)⁻¹ := rfl
    rw [h1, map_mul, map_inv, hρe₁, mul_inv_cancel]
  obtain ⟨N, hN, hNpc, hinv, hsupp, χ, -⟩ := exists_fixed_component_of_acts hMH hMpc θ
    (hHN hcH) hc2 e₁.2 hce (by rw [hci, hc4]; omega)
  have hβ : Fintype.card ↥((coreImage θ e₁.2).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hci, hc4]
  refine ⟨N, hN, hNpc, fun x hx hxc hx2 hxs => ?_, fun x hx => ?_,
    ⟨χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom⟩⟩
  · refine hinv x hx hxc hx2 ?_
    have h1 := hρ.apply_of_mem (by omega) ⟨x, hx⟩
    change (θ ((⟨x, hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin n)).support ⊆ _
    rw [← h1, hci]
    exact hxs
  · obtain ⟨hxM, hxs⟩ := hsupp x hx
    refine ⟨hxM, ?_⟩
    have h1 := hρ.apply_of_mem (by omega) ⟨x, hxM⟩
    rw [hci] at hxs
    change (ρ ⟨x, le_normalizer hxM⟩).support ⊆ _
    rw [h1]
    exact hxs

theorem map_conj_eq_of_four (S : Sig36 X t J n e E D) (hD2 : SignalizerConjKernelExclusion)
    (hn : 11 ≤ n) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {x g : X} (hx'H : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1)
    (hx'4 : (ρ ⟨g * x * g⁻¹, hHN hx'H⟩).support.card = 4)
    (hCx' : centralizer ({g * x * g⁻¹} : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X)) {N N' : Subgroup X}
    (hNC : N ≤ centralizer ({x} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({x} : Set X))))
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin (n - 4))) {x₀ : X} (hx₀N : x₀ ∈ N)
    (hx₀M : x₀ ∈ M) (hx₀2 : x₀ * x₀ = 1) (hx₀4 : (ρ ⟨x₀, le_normalizer hx₀M⟩).support.card = 4)
    (hN'M : N' ≤ M) (hN'C : N' ≤ centralizer ({g * x * g⁻¹} : Set X))
    (hN'pc : IsPComponent 2 (N'.subgroupOf (centralizer ({g * x * g⁻¹} : Set X))))
    (θN' : ↥N' ⧸ pPrimeCore 2 ↥N' ≃* alternatingGroup (Fin (n - 4))) :
    N.map (MulAut.conj g).toMonoidHom = N' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set Ng := N.map (MulAut.conj g).toMonoidHom with hNgdef
  have hNgC : Ng ≤ centralizer ({g * x * g⁻¹} : Set X) := by
    rw [← map_conj_centralizer_singleton]
    exact map_mono hNC
  have hNgpc : IsPComponent 2 (Ng.subgroupOf (centralizer ({g * x * g⁻¹} : Set X))) := by
    have h1 := isPComponent_map_conj hNC hNpc g
    rwa [map_conj_centralizer_singleton] at h1
  have hNgH : Ng ≤ H := hNgC.trans hCx'
  have hN'H : N' ≤ H := hN'M.trans hMH
  have hNgperf : ⁅Ng, Ng⁆ = Ng := UnbalancedCorr.commutator_eq_of_isPComponent hNgC hNgpc
  have hN'perf : ⁅N', N'⁆ = N' := UnbalancedCorr.commutator_eq_of_isPComponent hN'C hN'pc
  let θNg : ↥Ng ⧸ pPrimeCore 2 ↥Ng ≃* alternatingGroup (Fin (n - 4)) :=
    (Sol78.coreQuotCongr
      (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm.trans θN
  have hNgnotK : ¬ Ng ≤ UnbalancedLayer.coreActionKernel M := by
    intro hNgK
    have hTg : (zpowers x₀).map (MulAut.conj g).toMonoidHom ≤ Ng := map_mono (zpowers_le.mpr hx₀N)
    exact hD2 X t J n e E D S M hMH hMpc hHN hsup θ ρ hρ x₀ hx₀M (le_normalizer hx₀M) hx₀2 hx₀4
      (hA x₀ hx₀M hx₀2 hx₀4) g (hTg.trans hNgH) (hTg.trans hNgK)
  have hN'notK : ¬ N' ≤ UnbalancedLayer.coreActionKernel M := by
    intro hN'K
    have hN'O : N' ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
      mem_core_of_mem_coreActionKernel hρ (by omega) (hN'M hz) (hN'K hz)
    have h1 : Nat.card N' ∣ Nat.card ((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le hN'O
    rw [card_map_of_injective M.subtype_injective] at h1
    have h2 := card_eq_of_alt (by omega) θN'
    have h3 : 2 ∣ (n - 4).factorial / 2 := by
      have h4 : (4 : ℕ).factorial ∣ (n - 4).factorial := Nat.factorial_dvd_factorial (by omega)
      have h5 : (4 : ℕ).factorial = 4 * 6 := rfl
      obtain ⟨k, hk⟩ := h4
      rw [hk, h5]
      exact ⟨6 * k, by omega⟩
    have h6 : 2 ∣ Nat.card N' := by rw [h2]; exact Dvd.dvd.mul_right h3 _
    exact absurd (Nat.Coprime.coprime_dvd_right (h6.trans h1) pPrimeCore_coprime_card)
      (by decide)
  have hNgk := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hNgH.trans hHN) (by omega) θNg hNgperf
    hNgnotK
  have hN'k := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hN'H.trans hHN) (by omega) θN' hN'perf
    hN'notK
  by_contra hne
  have hOH : (pPrimeCore 2 ↥(centralizer ({g * x * g⁻¹} : Set X))).map
      (centralizer ({g * x * g⁻¹} : Set X)).subtype ≤ H := (map_subtype_le _).trans hCx'
  exact false_of_two_components_of_ker hρ (by omega) hHN hx'H hx'2 hx'4 hOH hN'C hN'pc hNgC
    hNgpc (Ne.symm hne) hN'H hNgH (by omega) (by omega) hN'k hNgk θN' θNg

theorem mem_of_conj_of_four (S : Sig36 X t J n e E D) (hD2 : SignalizerConjKernelExclusion)
    (hn : 11 ≤ n) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {x g : X} (hxM : x ∈ M) (hx2 : x * x = 1) (hx4 : (ρ ⟨x, le_normalizer hxM⟩).support.card = 4)
    (hx'H : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hx'4 : (ρ ⟨g * x * g⁻¹, hHN hx'H⟩).support.card = 4)
    (hCx' : centralizer ({g * x * g⁻¹} : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X)) :
    g ∈ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hxH : x ∈ H := hMH hxM
  have hCx : centralizer ({x} : Set X) ≤ H := hA x hxM hx2 hx4
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨Nx, hNx, hNxpc, hNxinv, -, ⟨θNx⟩⟩ := S.exists_fixComp_of_sup hMH hMpc hHN hρ hxH hx2
    hx4
  rw [inf_eq_right.mpr hCx] at hNxpc
  have hτc : (ρ ⟨x, hHN hxH⟩).support.card ≤ n := by
    have := Finset.card_le_univ (ρ ⟨x, hHN hxH⟩).support
    rwa [Fintype.card_fin] at this
  obtain ⟨δ, hδA, hδ2, hδ4, hδs, hδc⟩ := exists_four_of_fix (ρ ⟨x, hHN hxH⟩) (by omega)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hδ4
    omega
  obtain ⟨f, hfM, hfx, hf2, hρf⟩ := hρ.exists_involution_lift (by omega) (hHN hxH) hx2 hδA hδ2
    hδ1 hδc
  have hfNx : f ∈ Nx := by
    refine hNxinv f hfM (mem_centralizer_singleton_iff.mp hfx) ⟨1, by rw [pow_one, sq]; exact hf2⟩
      ?_
    rw [hρf]
    exact hδs
  have hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by rw [hρf]; exact hδ4
  obtain ⟨Nx', hNx', hNx'pc, -, -, ⟨θNx'⟩⟩ := S.exists_fixComp_of_sup hMH hMpc hHN hρ hx'H hx'2
    hx'4
  rw [inf_eq_right.mpr hCx'] at hNx'pc
  have heq := S.map_conj_eq_of_four hD2 hn hMH hMpc hHN hsup hρ hA hx'H hx'2 hx'4 hCx'
    (hNx.trans inf_le_right) hNxpc θNx hfNx hfM hf2 hf4 (hNx'.trans inf_le_left)
    (hNx'.trans inf_le_right) hNx'pc θNx'
  have hf'M : g * f * g⁻¹ ∈ M := by
    have h1 : g * f * g⁻¹ ∈ Nx.map (MulAut.conj g).toMonoidHom := ⟨f, hfNx, rfl⟩
    rw [heq] at h1
    exact (hNx'.trans inf_le_left) h1
  have hf'2 : g * f * g⁻¹ * (g * f * g⁻¹) = 1 := by
    calc g * f * g⁻¹ * (g * f * g⁻¹) = g * (f * f) * g⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have hf1 : f ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, le_normalizer hfM⟩ = 1 := map_one ρ
    rw [h1] at hρf
    exact hδ1 hρf.symm
  have hf'1 : g * f * g⁻¹ ≠ 1 := by
    intro h
    apply hf1
    calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hfo : f ∉ oddGen (centralizer ({f} : Set X)) :=
    not_mem_oddGen_of_four (le_normalizer hfM) hf2 hf4 ((hA f hfM hf2 hf4).trans hHN)
  have hf'o : g * f * g⁻¹ ∉ oddGen (centralizer ({g * f * g⁻¹} : Set X)) := by
    intro h
    have h1 := conj_mem_oddGen_centralizer (g := g⁻¹) h
    have h2 : g⁻¹ * (g * f * g⁻¹) * g⁻¹⁻¹ = f := by group
    rw [h2] at h1
    exact hfo h1
  have hf'4 := hρ.card_support_eq_four_of_not_mem_oddGen (by omega) hf'M hf'2 hf'1 hf'o
  have hkerM : ∀ y ∈ M, y ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf y) :=
    fun y hy hyK => odd_orderOf_of_mem_oddCoreIn (mem_core_of_mem_coreActionKernel hρ (by omega)
      hy hyK)
  obtain ⟨c, hcM, hc⟩ := hρ.exists_conj_of_four (by omega) le_rfl hkerM (le_normalizer hfM)
    (le_normalizer hf'M) hfM hf'M hf2 hf'2 hf4 hf'4
  have hcg : c⁻¹ * g ∈ centralizer ({f} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * g * f = c⁻¹ * (g * f * g⁻¹) * g := by group
      _ = c⁻¹ * (c * f * c⁻¹) * g := by rw [hc]
      _ = f * (c⁻¹ * g) := by group
  have h1 := mul_mem (hMH hcM) (hA f hfM hf2 hf4 hcg)
  rwa [mul_inv_cancel_left] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
