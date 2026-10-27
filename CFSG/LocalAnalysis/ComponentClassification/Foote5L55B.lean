module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L55A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53M

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

include ε in
theorem exists_mem_QR_of_four (h𝕊 : FooteSimpleType 𝕊) {V : Subgroup G} (hVS : V ≤ S)
    (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1) :
    ∃ v ∈ V, v ≠ 1 ∧ ∃ q ∈ Q, ∃ r ∈ S ⊓ L, v = q * r := by
  have hVN : V ≤ normalizer (L : Set G) := hVS.trans h.S_le
  by_cases hVC : V ⊓ coreActionKernel L = ⊥
  · have hcard := card_eq_card_inf_mul_card_actImage ε hVN
    rw [hVC, card_bot, one_mul, hV4] at hcard
    have hsq : ∀ α ∈ actImage L ε V, α * α = 1 := by
      intro α hα
      obtain ⟨e, he, rfl⟩ := (mem_actImage ε hVN).mp hα
      rw [← actG_mul ε (hVN he) (hVN he), hV2 e he, actG_one]
    have hne := fourgroup_inf_innAut_ne_bot h𝕊 hcard.symm hsq
    obtain ⟨α, hα1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    obtain ⟨e, he, hαe⟩ := (mem_actImage ε hVN).mp (mem_inf.mp α.2).1
    have hinn : actG L ε e ∈ innAut5 𝕊 := hαe ▸ (mem_inf.mp α.2).2
    refine ⟨e, he, fun he1 => hα1 (Subtype.ext (by rw [← hαe, he1, actG_one]; rfl)), ?_⟩
    exact h.exists_mul_of_inner ε (hVS he) hinn
  · obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVC
    have hvQ : (v : G) ∈ Q := by
      rw [← h.inf_coreActionKernel]
      exact mem_inf.mpr ⟨hVS (mem_inf.mp v.2).1, (mem_inf.mp v.2).2⟩
    exact ⟨v, (mem_inf.mp v.2).1, fun h1 => hv1 (Subtype.ext h1), v, hvQ, 1, one_mem _,
      (mul_one _).symm⟩

include ε in
theorem false_of_isSylowOf_top (hD : Foote5AutData 𝕊 Lin) (h𝕊 : FooteSimpleType 𝕊)
    (hQ51 : ∀ u ∈ Q, (∀ s ∈ S, s * u = u * s) → ∀ y, (∀ s ∈ S, s * y = y * s) →
      IsConj u y → y ∈ Q)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L)
    (hB4 : GoldschmidtCorB4) (hST : IsSylowOf 2 S ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hgood : ∀ w ∈ Q, orderOf w = 2 → Good53 S L Q w := fun w hw hw2 =>
    h.good53 ε hD h𝕊 (hQ51 z h.zQ h.zS) ht51 hB4 hST hw hw2
  have hss : ∀ y q r : G, IsConj t y → q ∈ Q → r ∈ S ⊓ L → y = q * r → q = 1 :=
    fun y q r hty hq hr hy => h.conj_t_mem_R_of_mem_QR hgood ht51 hty hq hr hy
  obtain ⟨g, hgS, hgR⟩ := h.exists_conj_t_not_mem_R hB4 hST
  have hty : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
  have hgN := h.S_le hgS
  have hinn : actG L ε (g⁻¹ * t * g) ∉ innAut5 𝕊 := by
    intro hinn
    obtain ⟨q, hq, r, hr, hqr⟩ := h.exists_mul_of_inner ε hgS hinn
    have h1 := hss _ q r hty hq hr hqr
    rw [h1, one_mul] at hqr
    rw [hqr] at hgR
    exact hgR hr
  have hlin : actG L ε (g⁻¹ * t * g) ∈ Lin := by
    by_contra hlin
    have hsq : actG L ε (g⁻¹ * t * g) * actG L ε (g⁻¹ * t * g) = 1 := by
      rw [← actG_mul ε hgN hgN, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group,
        ht22, show g⁻¹ * 1 * g = 1 by group, actG_one]
    obtain ⟨γ, hγ⟩ := hD.conj_centralizer (h.Rbar ε) _ hlin hsq
    have hna := h.nonabelian_R_of_fix ε hD
      (β := MulAut.conj γ * actG L ε (g⁻¹ * t * g) * (MulAut.conj γ)⁻¹)
      (fun h2 => hlin (by
        have h3 := hD.normal.conj_mem _ h2 (MulAut.conj γ)⁻¹
        rwa [show (MulAut.conj γ)⁻¹ * (MulAut.conj γ * actG L ε (g⁻¹ * t * g) *
          (MulAut.conj γ)⁻¹) * (MulAut.conj γ)⁻¹⁻¹ = actG L ε (g⁻¹ * t * g) by group] at h3))
      (by rw [show MulAut.conj γ * actG L ε (g⁻¹ * t * g) * (MulAut.conj γ)⁻¹ *
          (MulAut.conj γ * actG L ε (g⁻¹ * t * g) * (MulAut.conj γ)⁻¹) =
          MulAut.conj γ * (actG L ε (g⁻¹ * t * g) * actG L ε (g⁻¹ * t * g)) *
            (MulAut.conj γ)⁻¹ by group, hsq]
          group) hγ
    exact h.false_of_field_conj ε hD hna hss hST hgS hty hlin
  have hcQ := h.commute_Q_of_pgl ε hD hgood hQ51 ht51 hST (c := g⁻¹) (by rwa [inv_inv])
    (by rwa [inv_inv])
  simp only [inv_inv] at hcQ
  have hSt : IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    hST.of_le (fun s hs => mem_centralizer_singleton_iff.mpr (h.tZ s hs)) le_top
  have hQc : conjugate Q g⁻¹ ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 := hcQ _ hx
    calc x * t = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = t * x := by group
  obtain ⟨y₁, hy₁C, hy₁⟩ := exists_conj_le_of_isSylowOf hSt hQc (h.isPGroup_Q.map _)
  obtain ⟨d, hd⟩ : ∃ d, g⁻¹ * y₁ = d := ⟨_, rfl⟩
  have hQdS : conjugate Q d ≤ S := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 : y₁ * x * y₁⁻¹ ∈ conjugate Q g⁻¹ := by
      rw [mem_conjugate_iff, inv_inv,
        show g⁻¹ * (y₁ * x * y₁⁻¹) * g = d * x * d⁻¹ by rw [← hd]; group]
      exact hx
    have h2 := hy₁ _ h1
    rwa [show y₁⁻¹ * (y₁ * x * y₁⁻¹) * y₁ = x by group] at h2
  have hy₁t : y₁ * t = t * y₁ := mem_centralizer_singleton_iff.mp hy₁C
  have hdt : d * t * d⁻¹ = g⁻¹ * t * g := by
    rw [← hd]
    calc g⁻¹ * y₁ * t * (g⁻¹ * y₁)⁻¹ = g⁻¹ * (y₁ * t) * y₁⁻¹ * g := by group
      _ = g⁻¹ * t * g := by rw [hy₁t]; group
  obtain ⟨E, hEQ, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := Q) (k := 2) (by rw [h.open_pRank_Q])
  have hVS : conjugate E d ≤ S := le_trans (map_mono hEQ) hQdS
  have hV4 : Nat.card (conjugate E d) = 4 := by rw [card_conjugate_eq_card, hEc]; norm_num
  have hV2 : ∀ v ∈ conjugate E d, v * v = 1 := by
    intro v hv
    rw [mem_conjugate_iff] at hv
    have h1 := hE.2 _ hv
    have h2 : d * (v * v) * d⁻¹ = 1 := by rw [← h1, sq]; group
    calc v * v = d⁻¹ * (d * (v * v) * d⁻¹) * d := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨v, hvV, hv1, q, hq, r, hr, hvqr⟩ := h.exists_mem_QR_of_four ε h𝕊 hVS hV4 hV2
  rw [mem_conjugate_iff] at hvV
  obtain ⟨w, hw⟩ : ∃ w, d * v * d⁻¹ = w := ⟨_, rfl⟩
  rw [hw] at hvV
  have hwQ : w ∈ Q := hEQ hvV
  have hw1 : w ≠ 1 := fun h1 => hv1 (by
    calc v = d⁻¹ * (d * v * d⁻¹) * d := by group
      _ = 1 := by rw [hw, h1]; group)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (hE.2 w hvV) hw1
  have hvw : v = d⁻¹ * w * d := by rw [← hw]; group
  have hwv : IsConj w v := isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv, hvw]⟩
  have hr1 := h.conj_mem_Q_of_mem_QR hgood hQ51 hwQ hw2 hwv hq hr hvqr
  rw [hr1, mul_one] at hvqr
  have hwd : d⁻¹ * w * d ∈ Q := by rw [← hvw, hvqr]; exact hq
  apply hinn
  rw [← hdt]
  exact h.inner_of_conj_mem_Q ε hwQ hw2 hwd (by rw [hdt]; exact hgS)
    (by rw [hdt]; exact (hcQ w hwQ).symm)

theorem not_isSylowOf_top (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) : ¬ IsSylowOf 2 S ⊤ := by
  intro hST
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  have hQ51 : ∀ u ∈ Q, (∀ s ∈ S, s * u = u * s) → ∀ y, (∀ s ∈ S, s * y = y * s) →
      IsConj u y → y ∈ Q := by
    intro u huQ huZ y hyZ huy
    obtain ⟨c, rfl⟩ := isConj_iff.mp huy
    have h1 := h.conj_mem_Q_of_center hGH hKG hB4 hAut hST (g := c⁻¹) huQ huZ
      (by rwa [inv_inv])
    rwa [inv_inv] at h1
  have ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L := by
    intro y hyZ hty
    obtain ⟨c, rfl⟩ := isConj_iff.mp hty
    have h1 := h.conj_t_mem_R_of_center hGH hKG hB4 hAut hST (g := c⁻¹) (by rwa [inv_inv])
    rwa [inv_inv] at h1
  exact h.false_of_isSylowOf_top ε hD h.sec4.footeFamilyType hQ51 ht51 hB4 hST

end Sec5

end CFSG.ComponentClassification.Foote5
