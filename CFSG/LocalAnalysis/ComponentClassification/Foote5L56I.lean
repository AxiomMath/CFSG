module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53D
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51

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

theorem exists_eq_four_of_abelian (hab : ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L, a * b = b * a) :
    ∃ r ∈ S ⊓ L, r * r = 1 ∧ r ≠ 1 ∧ r ≠ t ∧
      ∀ y ∈ S ⊓ L, y = 1 ∨ y = t ∨ y = r ∨ y = t * r := by
  classical
  obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
  have hsq : ∀ y ∈ S ⊓ L, y * y = 1 := by
    intro y hy
    obtain ⟨a₁, ha₁, a₂, ha₂, ha₁2, ha₂2, rfl⟩ := exists_mul_of_dihedral e hy
    rw [show a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ by group, ← hab a₁ ha₁ a₂ ha₂,
      show a₁ * (a₁ * a₂) * a₂ = (a₁ * a₁) * (a₂ * a₂) by group, ha₁2, ha₂2, one_mul]
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hex : ∃ r ∈ S ⊓ L, r ≠ 1 ∧ r ≠ t := by
    by_contra hno
    push Not at hno
    have h1 := SmallLocal.card_le_of_forall_mem_finset ({1, t} : Finset G) fun y hy => by
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Finset.mem_insert_self _ _
      · rw [hno y hy hy1]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h2 : ({1, t} : Finset G).card ≤ 2 := Finset.card_le_two
    have h3 := h.four_le_card_R
    omega
  obtain ⟨r, hr, hr1, hrt⟩ := hex
  refine ⟨r, hr, hsq r hr, hr1, hrt, fun y hy => ?_⟩
  rcases mem_four_of_pRank_le_two h.open_pRank_R_le h.tR hr hy ht22 (hsq r hr) (hsq y hy)
    h.t_ne_one hr1 (Ne.symm hrt) (hab t h.tR r hr) (hab y hy t h.tR) (hab y hy r hr)
    with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem mul_mem_centralizer_R {r : G} (hr : r ∈ S ⊓ L) (hr1 : r ≠ 1) (hrt : r ≠ t)
    (hR : ∀ y ∈ S ⊓ L, y = 1 ∨ y = t ∨ y = r ∨ y = t * r) {g g' : G} (hg : g ∈ S)
    (hg' : g' ∈ S) (hgK : g ∉ centralizer ((S ⊓ L : Subgroup G) : Set G))
    (hg'K : g' ∉ centralizer ((S ⊓ L : Subgroup G) : Set G)) :
    g * g' ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) := by
  have hcent : ∀ c ∈ S, c * r = r * c → c ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro c hc hcr
    refine mem_centralizer_iff.mpr fun y hy => ?_
    have hct := h.tZ c hc
    rcases hR y hy with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hct.symm
    · exact hcr.symm
    · rw [mul_assoc, ← hcr, ← mul_assoc, ← hct, mul_assoc]
  have hswap : ∀ c ∈ S, c ∉ centralizer ((S ⊓ L : Subgroup G) : Set G) →
      c * r * c⁻¹ = t * r := by
    intro c hc hcK
    have h1 := h.conj_mem_R hc hr
    rcases hR _ h1 with h2 | h2 | h2 | h2
    · exact absurd (by
        calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
          _ = 1 := by rw [h2]; group) hr1
    · exact absurd (by
        calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
          _ = c⁻¹ * t * c := by rw [h2]
          _ = t := by rw [mul_assoc, ← h.tZ c hc, ← mul_assoc, inv_mul_cancel, one_mul]) hrt
    · exact absurd (hcent c hc (by
        calc c * r = c * r * c⁻¹ * c := by group
          _ = r * c := by rw [h2])) hcK
    · exact h2
  have h1 := hswap g hg hgK
  have h2 := hswap g' hg' hg'K
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hgt : g * t * g⁻¹ = t := by rw [h.tZ g hg, mul_inv_cancel_right]
  have h3 : g * g' * r * (g * g')⁻¹ = r := by
    calc g * g' * r * (g * g')⁻¹ = g * (g' * r * g'⁻¹) * g⁻¹ := by group
      _ = g * (t * r) * g⁻¹ := by rw [h2]
      _ = (g * t * g⁻¹) * (g * r * g⁻¹) := by group
      _ = t * (t * r) := by rw [hgt, h1]
      _ = r := by rw [← mul_assoc, ht22, one_mul]
  refine hcent _ (mul_mem hg hg') ?_
  calc g * g' * r = g * g' * r * (g * g')⁻¹ * (g * g') := by group
    _ = r * (g * g') := by rw [h3]

include ε in
theorem card_S_le_of_abelian (hD : Foote5AutData 𝕊 Lin)
    (hab : ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L, a * b = b * a) : Nat.card S ≤ 8 * Nat.card Q := by
  classical
  obtain ⟨r, hr, -, hr1, hrt, hR⟩ := h.exists_eq_four_of_abelian hab
  have hK₀N : S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
    inf_le_left.trans h.S_le
  have hK₀card : Nat.card ↥(S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)) ≤
      4 * Nat.card Q := by
    have h1 := card_eq_card_inf_mul_card_actImage ε hK₀N
    have h2 : Nat.card ↥(S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓
        coreActionKernel L) ≤ Nat.card Q := by
      refine card_le_of_le ?_
      rw [← h.inf_coreActionKernel]
      exact inf_le_inf_right _ inf_le_left
    have hfix : ∀ α ∈ actImage L ε (S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)),
        ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
      intro α hα ρ hρ
      obtain ⟨k, hk, rfl⟩ := (mem_actImage ε hK₀N).mp hα
      exact (h.actG_fix_iff ε (mem_inf.mp hk).1).mpr
        (fun r' hr' => (mem_centralizer_iff.mp (mem_inf.mp hk).2 r' hr').symm) ρ hρ
    have h3 := (hD.centralizer_sylow (h.Rbar ε) _
      (isPGroup_actImage ε (h.isPGroup_S.to_le inf_le_left)) hfix).2
    rw [h1]
    calc _ ≤ Nat.card Q * 4 := Nat.mul_le_mul h2 h3
      _ = 4 * Nat.card Q := mul_comm _ _
  have hSK : Nat.card S ≤ 2 * Nat.card ↥(S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)) := by
    by_cases hall : ∀ g ∈ S, g ∈ centralizer ((S ⊓ L : Subgroup G) : Set G)
    · have h1 : S ≤ S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
        fun g hg => mem_inf.mpr ⟨hg, hall g hg⟩
      have h2 := card_le_of_le h1
      omega
    push Not at hall
    obtain ⟨g₀, hg₀S, hg₀K⟩ := hall
    have hsurj : Function.Surjective fun i : Bool =>
        (QuotientGroup.mk (if i then (⟨g₀, hg₀S⟩ : S) else 1) :
          S ⧸ (S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)).subgroupOf S) := by
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      by_cases hb : (b : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G)
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [QuotientGroup.eq, inv_one, one_mul, mem_subgroupOf]
        exact mem_inf.mpr ⟨b.2, hb⟩
      · refine ⟨true, ?_⟩
        simp only [↓reduceIte]
        rw [QuotientGroup.eq, mem_subgroupOf]
        show g₀⁻¹ * (b : G) ∈ S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)
        have h1 := h.mul_mem_centralizer_R hr hr1 hrt hR (inv_mem hg₀S) b.2
          (fun h2 => hg₀K (by have h3 := inv_mem h2; rwa [inv_inv] at h3)) hb
        exact mem_inf.mpr ⟨mul_mem (inv_mem hg₀S) b.2, h1⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    have hb2 : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [hb2] at h1
    have h2 := card_eq_card_quotient_mul_card_subgroup
      ((S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)).subgroupOf S)
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h2
    calc Nat.card S = _ := h2
      _ ≤ 2 * Nat.card ↥(S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)) :=
          Nat.mul_le_mul_right _ h1
  omega

end Sec5

end CFSG.ComponentClassification.Foote5
