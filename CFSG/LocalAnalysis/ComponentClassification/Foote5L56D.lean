module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56C

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G]

namespace WreathCfg

variable {T X X' : Subgroup G} {x a s : G} (h : WreathCfg T X X' x a s)
include h

theorem conj_swap {v : G} (hvN : v ∈ X ⊔ X' ⊔ zpowers s) (hvS : v ∉ X ⊔ X') :
    (∀ q ∈ X, v * q * v⁻¹ ∈ X') ∧ (∀ q ∈ X', v * q * v⁻¹ ∈ X) ∧
      (∀ q ∈ X, v⁻¹ * q * v ∈ X') ∧ (∀ q ∈ X', v⁻¹ * q * v ∈ X) := by
  have hc : v * s ∈ X ⊔ X' := (h.mem_or_mul_mem_of_mem_N hvN).resolve_left hvS
  have hv : v = v * s * s := by rw [mul_assoc, h.s2, mul_one]
  have e₁ : ∀ q, v * q * v⁻¹ = (v * s) * (s * q * s) * (v * s)⁻¹ := fun q => by
    calc v * q * v⁻¹ = v * s * s * q * (v * s * s)⁻¹ := by rw [← hv]
      _ = (v * s) * (s * q * s⁻¹) * (v * s)⁻¹ := by group
      _ = (v * s) * (s * q * s) * (v * s)⁻¹ := by rw [h.s_inv]
  have e₂ : ∀ q, v⁻¹ * q * v = s * ((v * s)⁻¹ * q * (v * s)) * s := fun q => by
    calc v⁻¹ * q * v = (v * s * s)⁻¹ * q * (v * s * s) := by rw [← hv]
      _ = s⁻¹ * ((v * s)⁻¹ * q * (v * s)) * s := by group
      _ = s * ((v * s)⁻¹ * q * (v * s)) * s := by rw [h.s_inv]
  have hcX := h.S_le_normalizer_X hc
  have hcX' := h.S_le_normalizer_X' hc
  have hcX₁ : ∀ q ∈ X, (v * s)⁻¹ * q * (v * s) ∈ X := fun q hq => by
    have h1 := (mem_normalizer_iff.mp (h.S_le_normalizer_X (inv_mem hc)) q).mp hq
    rwa [inv_inv] at h1
  have hcX'₁ : ∀ q ∈ X', (v * s)⁻¹ * q * (v * s) ∈ X' := fun q hq => by
    have h1 := (mem_normalizer_iff.mp (h.S_le_normalizer_X' (inv_mem hc)) q).mp hq
    rwa [inv_inv] at h1
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [e₁]
    exact (mem_normalizer_iff.mp hcX' _).mp (h.sX q hq)
  · rw [e₁]
    exact (mem_normalizer_iff.mp hcX _).mp (h.sX' q hq)
  · rw [e₂]
    exact h.sX _ (hcX₁ q hq)
  · rw [e₂]
    exact h.sX' _ (hcX'₁ q hq)

theorem card_centralizer_le_of_not_mem [Finite G] {u : G}
    (huN : u ∈ X ⊔ X' ⊔ zpowers s) (huS : u ∉ X ⊔ X') :
    Nat.card ↥((X ⊔ X') ⊓ centralizer ({u} : Set G)) ≤ 8 := by
  obtain ⟨hswap, -, -, -⟩ := h.conj_swap huN huS
  have hdisj : Disjoint X ((X ⊔ X') ⊓ centralizer ({u} : Set G)) := by
    rw [disjoint_iff, eq_bot_iff]
    intro q hq
    have hqX := (mem_inf.mp hq).1
    have hqu := mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hq).2).2
    have h1 : u * q * u⁻¹ = q := by rw [← hqu, mul_inv_cancel_right]
    have h2 : q ∈ X ⊓ X' := mem_inf.mpr ⟨hqX, h1 ▸ hswap q hqX⟩
    rwa [h.bot] at h2
  have h1 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X
    ((X ⊔ X') ⊓ centralizer ({u} : Set G)) (inf_le_left.trans h.S_le_normalizer_X) hdisj
  have h2 := card_le_of_le (sup_le (le_sup_left : X ≤ X ⊔ X')
    (inf_le_left : (X ⊔ X') ⊓ centralizer ({u} : Set G) ≤ X ⊔ X'))
  rw [h1, h.card, h.card_S] at h2
  omega

theorem card_centralizer_le_of_noncentral [Finite G] {q₁ q₂ : G} (hq₁ : q₁ ∈ X)
    (hq₂ : q₂ ∈ X') (hn₁ : ∃ d ∈ X, d * q₁ ≠ q₁ * d) (hn₂ : ∃ d ∈ X', d * q₂ ≠ q₂ * d) :
    Nat.card ↥((X ⊔ X') ⊓ centralizer ({q₁ * q₂} : Set G)) ≤ 16 := by
  set C₁ := X ⊓ centralizer ({q₁} : Set G) with hC₁
  set C₂ := X' ⊓ centralizer ({q₂} : Set G) with hC₂
  have h1 : Nat.card C₁ ≤ 4 := card_inf_centralizer_le_four h.card hn₁
  have h2 : Nat.card C₂ ≤ 4 := card_inf_centralizer_le_four h.card_X' hn₂
  have hle : (X ⊔ X') ⊓ centralizer ({q₁ * q₂} : Set G) ≤ C₁ ⊔ C₂ := by
    intro y hy
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := exists_mul_of_mem_sup_commute h.comm (mem_inf.mp hy).1
    have hyu := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    have h3 : r₁ * q₁ * (r₂ * q₂) = q₁ * r₁ * (q₂ * r₂) := by
      calc r₁ * q₁ * (r₂ * q₂) = r₁ * (q₁ * r₂) * q₂ := by group
        _ = r₁ * (r₂ * q₁) * q₂ := by rw [h.comm q₁ hq₁ r₂ hr₂]
        _ = r₁ * r₂ * (q₁ * q₂) := by group
        _ = q₁ * q₂ * (r₁ * r₂) := hyu
        _ = q₁ * (q₂ * r₁) * r₂ := by group
        _ = q₁ * (r₁ * q₂) * r₂ := by rw [h.comm r₁ hr₁ q₂ hq₂]
        _ = q₁ * r₁ * (q₂ * r₂) := by group
    obtain ⟨h4, h5⟩ := eq_of_mul_eq_mul_of_disjoint h.bot (mul_mem hr₁ hq₁) (mul_mem hq₁ hr₁)
      (mul_mem hr₂ hq₂) (mul_mem hq₂ hr₂) h3
    exact mul_mem_sup (mem_inf.mpr ⟨hr₁, mem_centralizer_singleton_iff.mpr h4⟩)
      (mem_inf.mpr ⟨hr₂, mem_centralizer_singleton_iff.mpr h5⟩)
  have hdisj : Disjoint C₁ C₂ := by
    rw [disjoint_iff, eq_bot_iff, ← h.bot]
    exact inf_le_inf inf_le_left inf_le_left
  have hN : C₂ ≤ normalizer (C₁ : Set G) :=
    le_normalizer_of_commute fun c hc d hd => h.comm c (mem_inf.mp hc).1 d (mem_inf.mp hd).1
  have h6 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C₁ C₂ hN hdisj
  have h7 := card_le_of_le hle
  rw [h6] at h7
  calc Nat.card ↥((X ⊔ X') ⊓ centralizer ({q₁ * q₂} : Set G)) ≤ Nat.card C₁ * Nat.card C₂ := h7
    _ ≤ 4 * 4 := Nat.mul_le_mul h1 h2
    _ = 16 := by norm_num

theorem center_iff_of_commute {q₁ q₂ v : G} (hq₁ : q₁ ∈ X) (hq₂ : q₂ ∈ X')
    (hvN : v ∈ X ⊔ X' ⊔ zpowers s) (hvS : v ∉ X ⊔ X')
    (hv : v * (q₁ * q₂) = q₁ * q₂ * v) :
    (∀ d ∈ X, d * q₁ = q₁ * d) ↔ (∀ d ∈ X', d * q₂ = q₂ * d) := by
  obtain ⟨hs₁, hs₂, hs₃, hs₄⟩ := h.conj_swap hvN hvS
  have h1 : v * q₂ * v⁻¹ * (v * q₁ * v⁻¹) = q₁ * q₂ := by
    calc v * q₂ * v⁻¹ * (v * q₁ * v⁻¹) = v * q₁ * v⁻¹ * (v * q₂ * v⁻¹) :=
          h.comm _ (hs₂ q₂ hq₂) _ (hs₁ q₁ hq₁)
      _ = v * (q₁ * q₂) * v⁻¹ := by group
      _ = q₁ * q₂ := by rw [hv, mul_inv_cancel_right]
  obtain ⟨h2, h3⟩ := eq_of_mul_eq_mul_of_disjoint h.bot (hs₂ q₂ hq₂) hq₁ (hs₁ q₁ hq₁) hq₂ h1
  constructor
  · intro hc d hd
    have h4 := hc _ (hs₄ d hd)
    rw [← h3]
    calc d * (v * q₁ * v⁻¹) = v * ((v⁻¹ * d * v) * q₁) * v⁻¹ := by group
      _ = v * (q₁ * (v⁻¹ * d * v)) * v⁻¹ := by rw [h4]
      _ = v * q₁ * v⁻¹ * d := by group
  · intro hc d hd
    have h4 := hc _ (hs₃ d hd)
    rw [← h2]
    calc d * (v * q₂ * v⁻¹) = v * ((v⁻¹ * d * v) * q₂) * v⁻¹ := by group
      _ = v * (q₂ * (v⁻¹ * d * v)) * v⁻¹ := by rw [h4]
      _ = v * q₂ * v⁻¹ * d := by group

end WreathCfg

end CFSG.ComponentClassification.Foote5
