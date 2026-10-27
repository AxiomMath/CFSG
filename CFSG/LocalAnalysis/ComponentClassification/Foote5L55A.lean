module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L54
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53F

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem inner_of_conj_mem_Q {w d : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2)
    (hwd : d⁻¹ * w * d ∈ Q) (hyS : d * t * d⁻¹ ∈ S)
    (hyw : d * t * d⁻¹ * w = w * (d * t * d⁻¹)) : actG L ε (d * t * d⁻¹) ∈ innAut5 𝕊 := by
  have hwd2 : orderOf (d⁻¹ * w * d) = 2 := by
    rw [show d⁻¹ * w * d = d⁻¹ * w * d⁻¹⁻¹ by rw [inv_inv], orderOf_conj', hw2]
  obtain ⟨hfix, -, -, -, -, -⟩ := h.footeF_data hwd hwd2
  have htF : t ∈ footeF L₀ (d⁻¹ * w * d) := by
    rw [← hfix]
    exact h.R_le_footeFixed hwd h.tR
  rw [footeF_conj h.sec4.huniq, mem_conjugate_iff] at htF
  obtain ⟨εw, hεw⟩ := h.exists_actG_footeF_eq ε hwQ hw2
  rw [← hεw _ (h.S_le hyS) (mem_centralizer_singleton_iff.mpr hyw), actG_of_mem_self εw htF]
  exact ⟨_, rfl⟩

include ε in
theorem inner_of_centralizes_R (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {w d : G} (hwQ : w ∈ Q)
    (hw2 : orderOf w = 2) (hR : ∀ r ∈ S ⊓ L, r * (d⁻¹ * w * d) = d⁻¹ * w * d * r)
    (hyS : d * t * d⁻¹ ∈ S) (hyw : d * t * d⁻¹ * w = w * (d * t * d⁻¹)) :
    actG L ε (d * t * d⁻¹) ∈ innAut5 𝕊 := by
  obtain ⟨-, hLw, hLwF, -, -, -⟩ := h.footeF_data hwQ hw2
  have hRN : conjugate (S ⊓ L) d⁻¹ ≤ normalizer (footeF L₀ w : Set G) := by
    refine le_trans ?_ (le_normalizer_of_mem_footeFamilyOf h.sec4.huniq hLw hLwF)
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 := hR _ hx
    calc x * w = d * ((d⁻¹ * x * d) * (d⁻¹ * w * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * w * d) * (d⁻¹ * x * d)) * d⁻¹ := by rw [h1]
      _ = w * x := by group
  obtain ⟨εw, hεw⟩ := h.exists_actG_footeF_eq ε hwQ hw2
  have h2 := mem_innAut_of_mem_commutator hD εw hRN
    (conj_mem_commutator_conjugate (a := d) (h.t_mem_commutator_R ε hD hna))
  rwa [hεw _ (h.S_le hyS) (mem_centralizer_singleton_iff.mpr hyw)] at h2

theorem commute_Q_of_pgl (hD : Foote5AutData 𝕊 Lin)
    (hgood : ∀ w ∈ Q, orderOf w = 2 → Good53 S L Q w)
    (hQ51 : ∀ u ∈ Q, (∀ s ∈ S, s * u = u * s) → ∀ y, (∀ s ∈ S, s * y = y * s) →
      IsConj u y → y ∈ Q)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L)
    (hST : IsSylowOf 2 S ⊤) {c : G} (hyS : c * t * c⁻¹ ∈ S)
    (hinn : actG L ε (c * t * c⁻¹) ∉ innAut5 𝕊) :
    ∀ q ∈ Q, q * (c * t * c⁻¹) = c * t * c⁻¹ * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, c * t * c⁻¹ = y₀ := ⟨_, rfl⟩
  rw [hy₀] at hyS hinn ⊢
  have hy₀2 : y₀ * y₀ = 1 := by
    rw [← hy₀, show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, ht22]; group
  have hty₀ : IsConj t y₀ := isConj_iff.mpr ⟨c, hy₀⟩
  by_contra hnc
  push Not at hnc
  obtain ⟨w, hwQ, hw1, hwy, c', -, hc'⟩ :=
    exists_conj_mul_of_not_commute h.isPGroup_Q hy₀2 (h.S_le_normalizer_Q hyS) hnc
  have hww : w * w = 1 := by
    have h1 : y₀ * w * (y₀ * w) = 1 := by
      rw [← hc', show c'⁻¹ * y₀ * c' * (c'⁻¹ * y₀ * c') = c'⁻¹ * (y₀ * y₀) * c' by group,
        hy₀2]; group
    calc w * w = y₀ * y₀ * (w * w) := by rw [hy₀2, one_mul]
      _ = y₀ * w * (y₀ * w) := by
          rw [show y₀ * w * (y₀ * w) = y₀ * (w * y₀) * w by group, hwy]; group
      _ = 1 := h1
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
  have hwt : ¬ IsConj w t := fun h1 =>
    hw1 (h.conj_t_mem_R_of_mem_QR hgood ht51 h1.symm hwQ (one_mem _) (mul_one w).symm)
  have hSt : IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    hST.of_le (fun s hs => mem_centralizer_singleton_iff.mpr (h.tZ s hs)) le_top
  have hwc : c⁻¹ * w * c ∈ centralizer ({t} : Set G) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    have hwy' := hwy
    rw [← hy₀] at hwy'
    calc c⁻¹ * w * c * t = c⁻¹ * (w * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * w) * c := by rw [hwy']
      _ = t * (c⁻¹ * w * c) := by group
  have hzp : IsPGroup 2 (zpowers (c⁻¹ * w * c)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, show c⁻¹ * w * c = c⁻¹ * w * c⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj', hw2]
  obtain ⟨y₁, hy₁C, hy₁⟩ := exists_conj_le_of_isSylowOf hSt (zpowers_le.mpr hwc) hzp
  obtain ⟨d, hd⟩ : ∃ d, c * y₁ = d := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, d⁻¹ * w * d = ω := ⟨_, rfl⟩
  have hωS : ω ∈ S := by
    rw [← hω, ← hd, show (c * y₁)⁻¹ * w * (c * y₁) = y₁⁻¹ * (c⁻¹ * w * c) * y₁ by group]
    exact hy₁ _ (mem_zpowers _)
  have hy₁t : y₁ * t = t * y₁ := mem_centralizer_singleton_iff.mp hy₁C
  have hdt : d * t * d⁻¹ = y₀ := by
    rw [← hd, ← hy₀]
    calc c * y₁ * t * (c * y₁)⁻¹ = c * (y₁ * t) * y₁⁻¹ * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [hy₁t]; group
  have hωω : ω * ω = 1 := by
    rw [← hω, show d⁻¹ * w * d * (d⁻¹ * w * d) = d⁻¹ * (w * w) * d by group, hww]; group
  have hwω : IsConj w ω := isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv, hω]⟩
  have hωR : ∀ r ∈ S ⊓ L, r * ω = ω * r := by
    by_contra hall
    push Not at hall
    obtain ⟨c₁, -, hc₁⟩ := h.exists_conj_mul_t ε hD hωS hωω hall
    have h1 : IsConj ω (ω * t) := isConj_iff.mpr ⟨c₁⁻¹, by rw [inv_inv, hc₁]⟩
    have h2 : IsConj (ω * t) (w * y₀) := isConj_iff.mpr ⟨d, by rw [← hω, ← hdt]; group⟩
    have h3 : IsConj (w * y₀) y₀ := by
      rw [hwy]
      exact (isConj_iff.mpr ⟨c'⁻¹, by rw [inv_inv, hc']⟩).symm
    exact hwt (hwω.trans (h1.trans (h2.trans (h3.trans hty₀.symm))))
  have hωfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε ω ρ = ρ :=
    (h.actG_fix_iff ε hωS).mpr fun r hr => (hωR r hr).symm
  have hωd : d * t * d⁻¹ * w = w * (d * t * d⁻¹) := by rw [hdt]; exact hwy.symm
  have hdy : d * t * d⁻¹ ∈ S := by rw [hdt]; exact hyS
  have hωN := h.S_le hωS
  have hsq : actG L ε ω * actG L ε ω = 1 := by rw [← actG_mul ε hωN hωN, hωω, actG_one]
  by_cases hωinn : actG L ε ω ∈ innAut5 𝕊
  ·
    obtain ⟨q, hq, r, hr, hqr⟩ := h.exists_mul_of_inner ε hωS hωinn
    have hr1 := h.conj_mem_Q_of_mem_QR hgood hQ51 hwQ hw2 hwω hq hr hqr
    rw [hr1, mul_one] at hqr
    have hωQ : d⁻¹ * w * d ∈ Q := by rw [hω, hqr]; exact hq
    apply hinn
    rw [← hdt]
    exact h.inner_of_conj_mem_Q ε hwQ hw2 hωQ hdy hωd
  by_cases hωlin : actG L ε ω ∈ Lin
  ·
    have hfix2 := hD.pgl_fixed (h.Rbar ε) _ hωlin hωinn hsq (h.actG_map_Rbar ε hωS)
    have hle : (h.Rbar ε : Subgroup 𝕊) ≤ (h.Rbar ε : Subgroup 𝕊) ⊓
        MonoidHom.eqLocus (actG L ε ω).toMonoidHom (MonoidHom.id 𝕊) :=
      le_inf le_rfl fun ρ' hρ' => hωfix ρ' hρ'
    have h3 := card_le_of_le hle
    rw [h.card_Rbar ε] at h3
    have h4 := h.four_le_card_R
    omega
  ·
    have hna := h.nonabelian_R_of_fix ε hD hωlin hsq hωfix
    apply hinn
    rw [← hdt]
    exact h.inner_of_centralizes_R ε hD hna hwQ hw2 (fun r hr => by rw [hω]; exact hωR r hr)
      hdy hωd

end Sec5

end CFSG.ComponentClassification.Foote5
