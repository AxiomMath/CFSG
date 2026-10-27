module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem le_coreActionKernel_of_exact_pump_seven [Finite X] {M Je X₀ : Subgroup X} {r : ℕ}
    {t a j : X} (hr9 : 9 ≤ r) (hrodd : Odd r)
    (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r))
    (htN : t ∈ normalizer (M : Set X)) (htt : t * t = 1) (hJeM : Je ≤ M)
    (hJeC : Je ≤ centralizer ({t} : Set X))
    (hJepc : IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({t} : Set X))))
    (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Je = ⊤) (hJeperf : ⁅Je, Je⁆ = Je)
    {β : Type*} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = 7)
    (χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup β)
    (haN : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1) (hj : j ∈ Je)
    (haj : a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Je)
    (hjs : ((χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) : alternatingGroup β) :
      Perm β).support.card ≤ 4)
    (hodd : Odd (Nat.card X₀)) (hX₀N : X₀ ≤ normalizer (M : Set X))
    (hX₀O : X₀ ≤ (pPrimeCore 2 (centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype)
    (htX : ∀ x ∈ X₀, t * x * t⁻¹ ∈ X₀)
    (hY : ∀ y ∈ X₀, t * y = y * t → y ∈ UnbalancedLayer.coreActionKernel Je) :
    X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θM
  have hJeN : Je ≤ normalizer (M : Set X) := hJeM.trans le_normalizer
  have hJeq : Nontrivial (↥Je ⧸ pPrimeCore 2 ↥Je) := by
    have : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have : Nontrivial (alternatingGroup β) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_eq_fintype_card]; omega)
    exact χ.toEquiv.nontrivial
  have hne : ∃ x : ↥Je, ρ ⟨x, hJeN x.2⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_coreActionKernel_of_le hJeM hJeperf hJeq
    intro l hl
    exact hρ.mem_coreActionKernel (hJeN hl) (hall ⟨l, hl⟩)
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv (le_refl 7) (by omega) (by omega) θM hρ hJeN hres
    hJeperf hβ χ hne (Or.inr ⟨t, htN, htt, hJeM, hJeC, hJepc⟩)
  have hfixτ : ∀ (c : X) (hcN : c ∈ normalizer (M : Set X)),
      c ∈ UnbalancedLayer.coreActionKernel Je → ∀ v ∉ τ.support, ρ ⟨c, hcN⟩ v = v :=
    fun c hcN hcK => apply_eq_of_mem_cak_of_image hJeN (by omega) ψ hψ hcN hcK
  have htfix := hfixτ t htN (mem_coreActionKernel_of_le_centralizer hJeC)
  have hjN : j ∈ normalizer (M : Set X) := hJeN hj
  have hajN : a * j⁻¹ ∈ normalizer (M : Set X) := mul_mem haN (inv_mem hjN)
  have hgfix := hfixτ _ hajN haj
  have hsplit : ρ ⟨a, haN⟩ = ρ ⟨a * j⁻¹, hajN⟩ * ρ ⟨j, hjN⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change a = a * j⁻¹ * j
    group
  have hρj := hψ ⟨j, hj⟩
  have hsupj : (ρ ⟨j, hjN⟩).support.card ≤ 4 := by
    have h1 := card_support_of_le_fixAlt (le_refl 7) hτk le_rfl hβ (χ.symm.trans ψ)
      (χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je))
    have h2 : (χ.symm.trans ψ) (χ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je)) =
        ψ ((⟨j, hj⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) := by
      change ψ (χ.symm (χ _)) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h2, hρj] at h1
    change (ρ ⟨j, hjN⟩).support.card = _ at h1
    omega
  by_cases h5 : 5 ≤ r - (ρ ⟨a, haN⟩).support.card
  · exact hρ.le_coreActionKernel_of_fix haN ha2 h5 hX₀N hX₀O
  have ha2' : ρ ⟨a, haN⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, haN⟩ : ↥(normalizer (M : Set X))) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq]
      exact ha2)
    rw [this, map_one]
  have hev : 2 ∣ (ρ ⟨a, haN⟩).support.card := Perm.two_dvd_card_support ha2'
  have hle : (ρ ⟨a, haN⟩).support.card ≤ r := by
    simpa using (ρ ⟨a, haN⟩).support.card_le_univ
  set F₀ := τ.supportᶜ \ (ρ ⟨j, hjN⟩).support with hF₀def
  have hF₀fix : F₀ ⊆ (ρ ⟨a, haN⟩).supportᶜ := by
    intro v hv
    rw [hF₀def, Finset.mem_sdiff, Finset.mem_compl] at hv
    rw [Finset.mem_compl, Perm.notMem_support, hsplit, Perm.mul_apply,
      Perm.notMem_support.mp hv.2, hgfix v hv.1]
  have hF₀card : 3 ≤ F₀.card := by
    have h1 : τ.supportᶜ.card - (ρ ⟨j, hjN⟩).support.card ≤ F₀.card := by
      rw [hF₀def]
      exact Finset.le_card_sdiff _ _
    have h2 : τ.supportᶜ.card = 7 := by
      rw [Finset.card_compl, Fintype.card_fin]
      exact hτk
    omega
  have hcompl : (ρ ⟨a, haN⟩).supportᶜ.card = r - (ρ ⟨a, haN⟩).support.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hF₀eq : F₀ = (ρ ⟨a, haN⟩).supportᶜ := by
    refine Finset.eq_of_subset_of_card_le hF₀fix ?_
    obtain ⟨m, hm⟩ := hrodd
    obtain ⟨q, hq⟩ := hev
    omega
  have hmoved : ∀ v ∈ τ.support, v ∈ (ρ ⟨a, haN⟩).support := by
    intro v hv
    by_contra hva
    have h1 : v ∈ F₀ := by
      rw [hF₀eq]
      exact Finset.mem_compl.mpr hva
    rw [hF₀def, Finset.mem_sdiff, Finset.mem_compl] at h1
    exact h1.1 hv
  have hXfix : ∀ (x : X) (hx : x ∈ X₀), ∀ v ∈ τ.support, ρ ⟨x, hX₀N hx⟩ v = v :=
    fun x hx v hv => hρ.apply_eq_of_mem_oddCore haN ha2 hX₀N hX₀O hx v (hmoved v hv)
  have hcommt : ∀ (x : X) (hx : x ∈ X₀),
      ρ ⟨t, htN⟩ * ρ ⟨x, hX₀N hx⟩ = ρ ⟨x, hX₀N hx⟩ * ρ ⟨t, htN⟩ := by
    intro x hx
    have hd : Perm.Disjoint (ρ ⟨t, htN⟩) (ρ ⟨x, hX₀N hx⟩) := by
      intro v
      by_cases hv : v ∈ τ.support
      · exact Or.inr (hXfix x hx v hv)
      · exact Or.inl (htfix v hv)
    exact hd.commute.eq
  set K : Subgroup X := ρ.ker.map (normalizer (M : Set X)).subtype with hKdef
  have hmemK : ∀ (g : X) (hg : g ∈ normalizer (M : Set X)), ρ ⟨g, hg⟩ = 1 → g ∈ K :=
    fun g hg h => ⟨⟨g, hg⟩, h, rfl⟩
  have hKmem : ∀ g ∈ K, ∃ hg : g ∈ normalizer (M : Set X), ρ ⟨g, hg⟩ = 1 := by
    rintro _ ⟨⟨g, hg⟩, h, rfl⟩
    exact ⟨hg, h⟩
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro k hk
    obtain ⟨hkN, hk1⟩ := hKmem k hk
    have hc : t * k * t⁻¹ ∈ normalizer (M : Set X) := mul_mem (mul_mem htN hkN) (inv_mem htN)
    refine hmemK _ hc ?_
    have h1 : (⟨t * k * t⁻¹, hc⟩ : ↥(normalizer (M : Set X))) =
        ⟨t, htN⟩ * ⟨k, hkN⟩ * (⟨t, htN⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hk1]
    group
  intro x hx
  have hxK : x ∈ K := by
    refine mem_of_conj_mem hodd htt htX htK (fun y hy hyt => ?_) hx ?_
    · refine hmemK y (hX₀N hy) (Equiv.ext fun v => ?_)
      rw [Perm.one_apply]
      by_cases hv : v ∈ τ.support
      · exact hXfix y hy v hv
      · exact hfixτ y (hX₀N hy) (hY y hy hyt) v hv
    · have hxN := hX₀N hx
      have hc : x⁻¹ * (t * x * t⁻¹) ∈ normalizer (M : Set X) :=
        mul_mem (inv_mem hxN) (mul_mem (mul_mem htN hxN) (inv_mem htN))
      refine hmemK _ hc ?_
      have h1 : (⟨x⁻¹ * (t * x * t⁻¹), hc⟩ : ↥(normalizer (M : Set X))) =
          (⟨x, hxN⟩ : ↥(normalizer (M : Set X)))⁻¹ *
            (⟨t, htN⟩ * ⟨x, hxN⟩ * (⟨t, htN⟩ : ↥(normalizer (M : Set X)))⁻¹) := rfl
      rw [h1, map_mul, map_inv, map_mul, map_mul, map_inv, hcommt x hx]
      group
  obtain ⟨hxN, hx1⟩ := hKmem x hxK
  exact hρ.mem_coreActionKernel hxN hx1

end CFSG.ComponentClassification.SolMax
