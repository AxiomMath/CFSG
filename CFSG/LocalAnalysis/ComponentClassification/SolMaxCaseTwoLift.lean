module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace CaseTwo

theorem mem_of_conj_mem_of_sylow [Finite X] {H : Subgroup X} {t : X} (ht : orderOf t = 2)
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ H → g ∈ H) (hS : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ H) :
    t ∈ H := by
  obtain ⟨S, hSH⟩ := hS
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hP⟩ := hz2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S P
  have htP : t ∈ (P : Subgroup X) := hP (mem_zpowers t)
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at htP
  have h1 : g⁻¹ * t * g ∈ H := hSH (by simpa [MulAut.conj_apply, mul_assoc] using htP)
  have h2 : g⁻¹ ∈ H := hfus g⁻¹ (by rwa [inv_inv])
  have h3 := H.mul_mem (H.mul_mem (H.inv_mem h2) h1) h2
  rwa [show g⁻¹⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t by group] at h3

theorem existsUnique_fixed {H : Subgroup X} {w : X} (hwH : w ∈ H)
    (h : ∀ g : X, g⁻¹ * w * g ∈ H → g ∈ H) : ∃! ω : X ⧸ H, w • ω = ω := by
  have key : ∀ g : X, w • (QuotientGroup.mk g : X ⧸ H) = QuotientGroup.mk g ↔
      g⁻¹ * w * g ∈ H := fun g => by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, ← H.inv_mem_iff]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  refine ⟨QuotientGroup.mk 1, ?_, fun ω hω => ?_⟩
  · show w • (QuotientGroup.mk 1 : X ⧸ H) = QuotientGroup.mk 1
    rw [key]
    simpa using hwH
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    have hg := h g ((key g).mp hω)
    exact QuotientGroup.eq.mpr (by rw [mul_one]; exact H.inv_mem hg)

theorem existsUnique_fixed_conj {Ω : Type*} [MulAction X Ω] {w : X} (a : X)
    (h : ∃! ω : Ω, w • ω = ω) : ∃! ω : Ω, (a * w * a⁻¹) • ω = ω := by
  obtain ⟨ω₀, h₀, hu⟩ := h
  refine ⟨a • ω₀, ?_, fun ω hω => ?_⟩
  · show (a * w * a⁻¹) • (a • ω₀) = a • ω₀
    rw [mul_smul, mul_smul, inv_smul_smul, h₀]
  · have hω' : (a * w * a⁻¹) • ω = ω := hω
    have h1 : w • (a⁻¹ • ω) = a⁻¹ • ω := by
      have h2 := congrArg (fun x : Ω => a⁻¹ • x) hω'
      simpa [mul_smul] using h2
    rw [← hu _ h1, smul_inv_smul]

end CaseTwo

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.mem_of_conj_mem_of_centralizer_le (hρ : IsPermAction θ ρ) [Finite X]
    (hr : 9 ≤ r) {H : Subgroup X} (hMH : M ≤ H) (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) {t : X}
    (htH : t ∈ H) (ht2 : t * t = 1) (ht4 : (ρ ⟨t, hHN htH⟩).support.card = 4)
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ H → g ∈ H) {w : X} (hw2 : w * w = 1)
    (hCw : centralizer ({w} : Set X) ≤ H) {g : X} (hg : g⁻¹ * w * g ∈ H) : g ∈ H := by
  have hs2 : g⁻¹ * w * g * (g⁻¹ * w * g) = 1 := by
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw2]; group
  obtain ⟨e, heM, heo, he2, he4⟩ := hρ.exists_four_involution hr (hHN hg) hs2
  have hes : e * (g⁻¹ * w * g) = g⁻¹ * w * g * e :=
    mem_centralizer_singleton_iff.mp (oddGen_le _ heo)
  obtain ⟨c, hcH, hc⟩ := hρ.exists_conj_of_four (by omega) hMH hker (hHN htH) (le_normalizer heM)
    htH (hMH heM) ht2 he2 ht4 he4
  have hgeg : g * e * g⁻¹ ∈ centralizer ({w} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g * e * g⁻¹ * w = g * (e * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * w * g * e) * g⁻¹ := by rw [hes]
      _ = w * (g * e * g⁻¹) := by group
  have hgc : g * c ∈ H := by
    refine hfus (g * c) ?_
    rw [show g * c * t * (g * c)⁻¹ = g * (c * t * c⁻¹) * g⁻¹ by group, hc]
    exact hCw hgeg
  have h1 := H.mul_mem hgc (H.inv_mem hcH)
  rwa [mul_inv_cancel_right] at h1

theorem IsPermAction.exists_eight_involution (hρ : IsPermAction θ ρ) [Finite X] (hr : 8 ≤ r) :
    ∃ (y : X) (hy : y ∈ M), orderOf y = 2 ∧ (ρ ⟨y, le_normalizer hy⟩).support.card = 8 := by
  set σ : Perm (Fin r) := Sol78.dblTransposition hr * Sol78.dblTransposition' hr with hσdef
  have hσA : σ ∈ alternatingGroup (Fin r) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσdef, Perm.sign_mul, Sol78.sign_dbl, Sol78.sign_dbl',
      mul_one]
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, mul_assoc, ← mul_assoc (Sol78.dblTransposition' hr),
      ← (Sol78.dbl_dbl'_disjoint hr).commute.eq, mul_assoc, Sol78.dbl'_mul_self, mul_one,
      Sol78.dbl_mul_self]
  have hσ8 : σ.support.card = 8 := by
    rw [hσdef, (Sol78.dbl_dbl'_disjoint hr).card_support_mul, Sol78.card_support_dbl,
      Sol78.card_support_dbl']
  obtain ⟨q, hq⟩ := θ.surjective ⟨σ, hσA⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hx2 : (x : ↥M ⧸ pPrimeCore 2 ↥M) ^ 2 = 1 := by
    apply θ.injective
    rw [map_pow, hq, map_one, sq]
    exact Subtype.ext hσ2
  have hx1 : (x : ↥M ⧸ pPrimeCore 2 ↥M) ≠ 1 := by
    intro h
    rw [h, map_one] at hq
    have h1 : σ = 1 := (congrArg Subtype.val hq).symm
    rw [h1, Perm.support_one, Finset.card_empty] at hσ8
    omega
  obtain ⟨k, hk2, hkx⟩ := exists_involution_of_mk hodd hx2 hx1
  refine ⟨((x ^ k : ↥M) : X), (x ^ k).2, by rw [Subgroup.orderOf_coe]; exact hk2, ?_⟩
  rw [hρ.apply_of_mem (by omega) (x ^ k), hkx, hq]
  exact hσ8

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem card_support_t_of_add_four (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y) (hMpc : IsPComponent 2 (M.subgroupOf Y))
    (htM : t ∈ normalizer (M : Set X)) (hJM : J ≤ M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 4))}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 4))} (hρ : IsPermAction θ ρ) :
    (ρ ⟨t, htM⟩).support.card = 4 := by
  have hn9 := S.nine_le
  obtain ⟨θ', ρ', hρ', hcard⟩ :=
    S.exists_isPermAction_of_pumped hT13 hML hSch hMY hMpc htM hJM (by omega) θ
  have h := hρ.card_support_eq hρ' (by omega) (by omega) ⟨t, htM⟩
  omega

end Sig36

end CFSG.ComponentClassification.SolMax
