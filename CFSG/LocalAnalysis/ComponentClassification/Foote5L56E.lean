module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56D

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace WreathCfg

variable {T X X' : Subgroup G} {x a s : G} (h : WreathCfg T X X' x a s)
include h

omit [Finite G] in
theorem N_le_centralizer :
    X ⊔ X' ⊔ zpowers s ≤ centralizer ({x * (s * x * s)} : Set G) := by
  refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr ?_)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
  · calc y * (x * (s * x * s)) = (y * x) * (s * x * s) := (mul_assoc _ _ _).symm
      _ = (x * y) * (s * x * s) := by rw [h.x_center hy]
      _ = x * (y * (s * x * s)) := mul_assoc _ _ _
      _ = x * ((s * x * s) * y) := by rw [h.x'_center hy]
      _ = x * (s * x * s) * y := (mul_assoc _ _ _).symm
  · have hxx := h.x'_center (mem_sup_left h.xX)
    calc s * (x * (s * x * s)) = s * ((s * x * s) * x) := by rw [hxx]
      _ = (s * s) * x * s * x := by group
      _ = x * s * x := by rw [h.s2, one_mul]
      _ = x * (s * x * s) * s := by
          rw [show x * (s * x * s) * s = x * s * x * (s * s) by group, h.s2, mul_one]

theorem mem_N_of_commute {y : G} (hyT : y ∈ T)
    (hy : y * (x * (s * x * s)) = x * (s * x * s) * y) : y ∈ X ⊔ X' ⊔ zpowers s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNT : X ⊔ X' ⊔ zpowers s ≤ T := sup_le h.le_T (zpowers_le.mpr h.sT)
  have hNM : X ⊔ X' ⊔ zpowers s ≤ T ⊓ centralizer ({x * (s * x * s)} : Set G) :=
    le_inf hNT h.N_le_centralizer
  by_contra hyN
  have hlt : X ⊔ X' ⊔ zpowers s < T ⊓ centralizer ({x * (s * x * s)} : Set G) := by
    refine lt_of_le_of_ne hNM fun h1 => hyN ?_
    rw [h1]
    exact mem_inf.mpr ⟨hyT, mem_centralizer_singleton_iff.mpr hy⟩
  obtain ⟨y₀, hy₀M, hy₀N, hy₀nor⟩ :=
    exists_mem_normalizer_not_mem_of_lt (h.isPGroup.to_le inf_le_left) hlt
  have hy₀T := (mem_inf.mp hy₀M).1
  have hy₀c := mem_centralizer_singleton_iff.mp (mem_inf.mp hy₀M).2
  obtain ⟨u, hu⟩ : ∃ u, y₀ * x * y₀⁻¹ = u := ⟨_, rfl⟩
  have huN : u ∈ X ⊔ X' ⊔ zpowers s := by
    rw [← hu]
    exact (mem_normalizer_iff.mp hy₀nor x).mp (mem_sup_left (mem_sup_left h.xX))
  have hu1 : u ≠ 1 := fun h1 => h.x1 (by
    calc x = y₀⁻¹ * (y₀ * x * y₀⁻¹) * y₀ := by group
      _ = 1 := by rw [hu, h1]; group)
  have hux : u ≠ x := fun h1 => hy₀N (by
    have h2 : y₀ * x = x * y₀ := by
      calc y₀ * x = y₀ * x * y₀⁻¹ * y₀ := by group
        _ = x * y₀ := by rw [hu, h1]
    exact mem_sup_left (h.Cx y₀ hy₀T h2))
  have hux' : u ≠ s * x * s := fun h1 => hy₀N (by
    have h2 : s * y₀ * x = x * (s * y₀) := by
      calc s * y₀ * x = s * (y₀ * x * y₀⁻¹) * y₀ := by group
        _ = s * (s * x * s) * y₀ := by rw [hu, h1]
        _ = x * (s * y₀) := by
            rw [show s * (s * x * s) * y₀ = (s * s) * x * (s * y₀) by group, h.s2, one_mul]
    have h3 := h.Cx _ (mul_mem h.sT hy₀T) h2
    rw [show y₀ = s * (s * y₀) by rw [← mul_assoc, h.s2, one_mul]]
    exact mul_mem (mem_sup_right (mem_zpowers s)) (mem_sup_left h3))
  have huxx' : u ≠ x * (s * x * s) := fun h1 => by
    have h3 : y₀ * (x * (s * x * s)) * y₀⁻¹ = x * (s * x * s) := by
      rw [hy₀c, mul_inv_cancel_right]
    have h2 : y₀ * (s * x * s) * y₀⁻¹ = 1 := by
      calc y₀ * (s * x * s) * y₀⁻¹ =
          (y₀ * x * y₀⁻¹)⁻¹ * (y₀ * (x * (s * x * s)) * y₀⁻¹) := by group
        _ = (x * (s * x * s))⁻¹ * (x * (s * x * s)) := by rw [hu, h1, h3]
        _ = 1 := inv_mul_cancel _
    have h4 : s * x * s = 1 := by
      calc s * x * s = y₀⁻¹ * (y₀ * (s * x * s) * y₀⁻¹) * y₀ := by group
        _ = 1 := by rw [h2]; group
    apply h.x1
    calc x = s * (s * x * s) * s := (h.conj_conj x).symm
      _ = 1 := by rw [h4, mul_one, h.s2]
  have hKmem : ∀ k, k ∈ conjugate (X ⊔ X') y₀⁻¹ ↔ y₀⁻¹ * k * y₀ ∈ X ⊔ X' := fun k => by
    rw [mem_conjugate_iff, inv_inv]
  have hKN : conjugate (X ⊔ X') y₀⁻¹ ≤ X ⊔ X' ⊔ zpowers s := by
    intro k hk
    have h2 := (mem_normalizer_iff.mp hy₀nor _).mp (mem_sup_left ((hKmem k).mp hk))
    rwa [show y₀ * (y₀⁻¹ * k * y₀) * y₀⁻¹ = k by group] at h2
  have hKC : ∀ k ∈ conjugate (X ⊔ X') y₀⁻¹, k * u = u * k := by
    intro k hk
    have h1 := h.x_center ((hKmem k).mp hk)
    rw [← hu]
    calc k * (y₀ * x * y₀⁻¹) = y₀ * ((y₀⁻¹ * k * y₀) * x) * y₀⁻¹ := by group
      _ = y₀ * (x * (y₀⁻¹ * k * y₀)) * y₀⁻¹ := by rw [h1]
      _ = y₀ * x * y₀⁻¹ * k := by group
  have hKle : (X ⊔ X') ⊓ conjugate (X ⊔ X') y₀⁻¹ ≤ (X ⊔ X') ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_left _ fun k hk => mem_centralizer_singleton_iff.mpr (hKC k hk)
  have hC32 : 32 ≤ Nat.card ↥((X ⊔ X') ⊓ centralizer ({u} : Set G)) := by
    have h1 := h.card_le_two_mul_inf hKN
    rw [card_conjugate_eq_card, h.card_S] at h1
    have h3 := card_le_of_le hKle
    omega
  by_cases huS : u ∈ X ⊔ X'
  swap
  · have h1 := h.card_centralizer_le_of_not_mem huN huS
    omega
  obtain ⟨q₁, hq₁, q₂, hq₂, hq⟩ := exists_mul_of_mem_sup_commute h.comm huS
  have hna : ∃ c ∈ X, ∃ d ∈ X, c * d ≠ d * c := by
    obtain ⟨d, hd, hda⟩ := h.anc
    exact ⟨d, hd, a, h.aX, hda⟩
  by_cases hTT : (∀ d ∈ X, d * q₁ = q₁ * d) ∧ (∀ d ∈ X', d * q₂ = q₂ * d)
  · obtain ⟨hc₁, hc₂⟩ := hTT
    rcases eq_one_or_eq_of_mem_center_eight h.card hna h.xX h.x1 h.xZ hq₁ hc₁ with e₁ | e₁ <;>
      rcases h.eq_of_mem_center_X' hq₂ hc₂ with e₂ | e₂ <;> rw [e₁, e₂] at hq
    · exact hu1 (by rw [hq, one_mul])
    · exact hux' (by rw [hq, one_mul])
    · exact hux (by rw [hq, mul_one])
    · exact huxx' hq
  have hKS : ¬ conjugate (X ⊔ X') y₀⁻¹ ≤ X ⊔ X' := by
    intro hKS
    apply hTT
    have h1 : conjugate (X ⊔ X') y₀⁻¹ ≤ (X ⊔ X') ⊓ centralizer ({u} : Set G) :=
      le_inf hKS fun k hk => mem_centralizer_singleton_iff.mpr (hKC k hk)
    have h2 := card_le_of_le h1
    rw [card_conjugate_eq_card, h.card_S] at h2
    have h3 : (X ⊔ X') ⊓ centralizer ({u} : Set G) = X ⊔ X' :=
      eq_of_le_of_card_ge inf_le_left (by rw [h.card_S]; omega)
    have hall : ∀ d ∈ X ⊔ X', d * u = u * d := fun d hd => by
      have hd' : d ∈ (X ⊔ X') ⊓ centralizer ({u} : Set G) := by rw [h3]; exact hd
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp hd').2
    refine ⟨fun d hd => ?_, fun d hd => ?_⟩
    · have hdu := hall d (mem_sup_left hd)
      rw [hq] at hdu
      have h4 : d * q₁ * q₂ = q₁ * d * q₂ := by
        calc d * q₁ * q₂ = d * (q₁ * q₂) := mul_assoc _ _ _
          _ = q₁ * q₂ * d := hdu
          _ = q₁ * (q₂ * d) := mul_assoc _ _ _
          _ = q₁ * (d * q₂) := by rw [h.comm d hd q₂ hq₂]
          _ = q₁ * d * q₂ := (mul_assoc _ _ _).symm
      exact mul_right_cancel h4
    · have hdu := hall d (mem_sup_right hd)
      rw [hq] at hdu
      have h4 : q₁ * (d * q₂) = q₁ * (q₂ * d) := by
        calc q₁ * (d * q₂) = d * (q₁ * q₂) := by
              rw [← mul_assoc, h.comm q₁ hq₁ d hd, mul_assoc]
          _ = q₁ * q₂ * d := hdu
          _ = q₁ * (q₂ * d) := mul_assoc _ _ _
      exact mul_left_cancel h4
  obtain ⟨v, hvK, hvS⟩ := IsConcreteLE.not_le_iff_exists.mp hKS
  have hiff := h.center_iff_of_commute hq₁ hq₂ (hKN hvK) hvS (by rw [← hq]; exact hKC v hvK)
  have hn₁ : ∃ d ∈ X, d * q₁ ≠ q₁ * d := by
    by_contra hno
    push Not at hno
    exact hTT ⟨hno, hiff.mp hno⟩
  have hn₂ : ∃ d ∈ X', d * q₂ ≠ q₂ * d := by
    by_contra hno
    push Not at hno
    exact hTT ⟨hiff.mpr hno, hno⟩
  have h16 := h.card_centralizer_le_of_noncentral hq₁ hq₂ hn₁ hn₂
  rw [← hq] at h16
  omega

end WreathCfg

end CFSG.ComponentClassification.Foote5
