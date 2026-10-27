module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53L

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

theorem false_of_pgl_conj (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q)
    (hST : IsSylowOf 2 S ⊤) {w n b y : G} (hB : BadData L Q S z t ε Lin w n b)
    (hyS : y ∈ S) (hty : IsConj t y) (hylin : actG L ε y ∈ Lin)
    (hyinn : actG L ε y ∉ innAut5 𝕊) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw22 : w * w = 1 := by rw [← sq, ← hB.w2, pow_orderOf_eq_one]
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := fun h1 => by have := hB.w2; rw [h1, orderOf_one] at this; omega
  have hcwz : w * z = z * w := h.zS w (h.QS hB.wQ)
  have hy2 : y * y = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hty
    rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, ht22]; group
  have hyN := h.S_le hyS
  have hzt_not : ¬ IsConj z t := fun h2 => h.t_not_mem_Q (hz51 t h.tZ h2)
  obtain ⟨hζS₀, hζc⟩ := h.conj_z_mem_center hB.wQ hB.b_mem
  have hyw : w * y ≠ y * w := by
    intro hyw
    have hyS₀ : y ∈ S ⊓ centralizer ({w} : Set G) :=
      mem_inf.mpr ⟨hyS, mem_centralizer_singleton_iff.mpr hyw.symm⟩
    have hζN := h.S_le (mem_inf.mp hζS₀).1
    have hsqy : actG L ε y * actG L ε y = 1 := by rw [← actG_mul ε hyN hyN, hy2, actG_one]
    have hsqζ : actG L ε (b⁻¹ * z * b) * actG L ε (b⁻¹ * z * b) = 1 := by
      rw [← actG_mul ε hζN hζN, show b⁻¹ * z * b * (b⁻¹ * z * b) = b⁻¹ * (z * z) * b by group,
        hz22, show b⁻¹ * 1 * b = 1 by group, actG_one]
    apply hD.not_commute _ _ hylin hyinn hsqy hB.zb hsqζ
    rw [← actG_mul ε hyN hζN, hζc y hyS₀, actG_mul ε hζN hyN]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup_S) ⟨w * y, mul_mem (h.QS hB.wQ) hyS⟩
  rw [Subgroup.orderOf_mk] at hk
  obtain ⟨x, hx1, hvv, hxw, hxy, hvw, hvy, hvmem⟩ := exists_dihedral_center hw22 hy2 hyw hk
  have hwyQ : w * y * (w * y) ∈ Q := by
    have h1 := h.conj_mem_Q hyS hB.wQ
    rw [show w * y * (w * y) = w * (y * w * y⁻¹) by rw [inv_eq_of_mul_eq_one_right hy2]; group]
    exact mul_mem hB.wQ h1
  have hvQ : x * x ∈ Q := zpowers_le.mpr hwyQ hvmem
  have hvz : x * x = z := by
    rcases h.mem_W hB.wQ hw22 hw1 hB.wz hvQ hvv hvw.symm with h1 | h1 | h1 | h1
    · exact absurd h1 hx1
    · exfalso
      rw [h1] at hvy
      exact hyw hvy.symm
    · exact h1
    · exfalso
      apply hB.not_central z h.zS
      refine isConj_iff.mpr ⟨x, ?_⟩
      rw [hxw, h1, mul_assoc, ← hcwz, ← mul_assoc, hw22, one_mul]
  have hyz : IsConj y (z * y) := isConj_iff.mpr ⟨x, by rw [hxy, hvz]⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hty
  have hSt : IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    hST.of_le (fun s hs => mem_centralizer_singleton_iff.mpr (h.tZ s hs)) le_top
  have hzc : c⁻¹ * z * c ∈ centralizer ({t} : Set G) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 := h.zS y hyS
    rw [← hc] at h1
    calc c⁻¹ * z * c * t = c⁻¹ * (z * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * z) * c := by rw [h1]
      _ = t * (c⁻¹ * z * c) := by group
  have hzp : IsPGroup 2 (zpowers (c⁻¹ * z * c)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, show c⁻¹ * z * c = c⁻¹ * z * c⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj', h.z2]
  obtain ⟨y₁, hy₁C, hy₁⟩ := exists_conj_le_of_isSylowOf hSt (zpowers_le.mpr hzc) hzp
  have hzdS : y₁⁻¹ * (c⁻¹ * z * c) * y₁ ∈ S := hy₁ _ (mem_zpowers _)
  obtain ⟨d, hd⟩ : ∃ d, c * y₁ = d := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ, d⁻¹ * z * d = ζ := ⟨_, rfl⟩
  have hζS : ζ ∈ S := by
    rw [← hζ, ← hd, show (c * y₁)⁻¹ * z * (c * y₁) = y₁⁻¹ * (c⁻¹ * z * c) * y₁ by group]
    exact hzdS
  have hy₁t : y₁ * t = t * y₁ := mem_centralizer_singleton_iff.mp hy₁C
  have hdt : d * t * d⁻¹ = y := by
    rw [← hd, ← hc]
    calc c * y₁ * t * (c * y₁)⁻¹ = c * (y₁ * t) * y₁⁻¹ * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [hy₁t]; group
  have hζζ : ζ * ζ = 1 := by
    rw [← hζ, show d⁻¹ * z * d * (d⁻¹ * z * d) = d⁻¹ * (z * z) * d by group, hz22]; group
  have hζR : ∃ r ∈ S ⊓ L, r * ζ ≠ ζ * r := by
    by_contra hall
    push Not at hall
    have hRN : conjugate (S ⊓ L) d⁻¹ ≤ normalizer (L : Set G) := by
      intro x hx
      rw [mem_conjugate_iff, inv_inv] at hx
      have h1 := hall _ hx
      refine h.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr ?_)
      rw [← hζ] at h1
      calc x * z = d * ((d⁻¹ * x * d) * (d⁻¹ * z * d)) * d⁻¹ := by group
        _ = d * ((d⁻¹ * z * d) * (d⁻¹ * x * d)) * d⁻¹ := by rw [h1]
        _ = z * x := by group
    have h2 := mem_innAut_of_mem_commutator hD ε hRN
      (conj_mem_commutator_conjugate (a := d) (h.t_mem_commutator_R ε hD hna))
    rw [hdt] at h2
    exact hyinn h2
  obtain ⟨c₁, -, hc₁⟩ := h.exists_conj_mul_t ε hD hζS hζζ hζR
  have h1 : IsConj z ζ := isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv, hζ]⟩
  have h2 : IsConj ζ (ζ * t) := isConj_iff.mpr ⟨c₁⁻¹, by rw [inv_inv, hc₁]⟩
  have h3 : IsConj (ζ * t) (z * y) := isConj_iff.mpr ⟨d, by rw [← hζ, ← hdt]; group⟩
  exact hzt_not (h1.trans (h2.trans (h3.trans (hyz.symm.trans hty.symm))))

include ε in
theorem good53 (hD : Foote5AutData 𝕊 Lin) (h𝕊 : FooteSimpleType 𝕊)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L)
    (hB4 : GoldschmidtCorB4) (hST : IsSylowOf 2 S ⊤) {w : G} (hwQ : w ∈ Q)
    (hw2 : orderOf w = 2) : Good53 S L Q w := by
  by_contra hng
  obtain ⟨-, -, w', n, b, -, hB⟩ := h.exists_badData ε hD h𝕊 hz51 ht51 hwQ hw2 hng
  have hna := h.nonabelian_R_of_zb ε hD hB.wQ hB.b_mem hB.zb
  have hss : ∀ y q r : G, IsConj t y → q ∈ Q → r ∈ S ⊓ L → y = q * r → q = 1 :=
    fun y q r hty hq hr hy => h.conj_t_mem_QR (fun u hu hu2 => h.star ε hD h𝕊 hz51 ht51 hu hu2)
      hna ht51 hty hq hr hy
  obtain ⟨g, hgS, hgR⟩ := h.exists_conj_t_not_mem_R hB4 hST
  have hty : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
  by_cases hinn : actG L ε (g⁻¹ * t * g) ∈ innAut5 𝕊
  · obtain ⟨q, hq, r, hr, hqr⟩ := h.exists_mul_of_inner ε hgS hinn
    have h1 := hss _ q r hty hq hr hqr
    rw [h1, one_mul] at hqr
    rw [hqr] at hgR
    exact hgR hr
  by_cases hlin : actG L ε (g⁻¹ * t * g) ∈ Lin
  · exact h.false_of_pgl_conj ε hD hna hz51 hST hB hgS hty hlin hinn
  · exact h.false_of_field_conj ε hD hna hss hST hgS hty hlin

end Sec5

end CFSG.ComponentClassification.Foote5
