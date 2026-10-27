module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53H
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

theorem commute_of_inf_conjugate_eq_bot_of_le {P : Subgroup G} (hPS : P ≤ S)
    (hRP : S ⊓ L ≤ P) {y : G} (hy : y ∈ normalizer (P : Set G))
    (hRy : S ⊓ L ⊓ conjugate (S ⊓ L) y = ⊥) {r a : G} (hr : r ∈ S ⊓ L)
    (ha : a ∈ conjugate (S ⊓ L) y) : a * r = r * a := by
  have haS : a ∈ S := hPS (conjugate_le_of_mem_normalizer hy hRP ha)
  have h1 : a * r * a⁻¹ * r⁻¹ ∈ S ⊓ L := mul_mem (h.conj_mem_R haS hr) (inv_mem hr)
  have h2 : a * r * a⁻¹ * r⁻¹ ∈ conjugate (S ⊓ L) y := by
    have h3 : r * a⁻¹ * r⁻¹ ∈ conjugate (S ⊓ L) y := by
      rw [mem_conjugate_iff] at ha ⊢
      have hyr : y * r * y⁻¹ ∈ S := hPS ((mem_normalizer_iff.mp hy r).mp (hRP hr))
      rw [show y * (r * a⁻¹ * r⁻¹) * y⁻¹ =
        (y * r * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * r * y⁻¹)⁻¹ by group]
      exact h.conj_mem_R hyr (inv_mem ha)
    rw [show a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) by group]
    exact mul_mem ha h3
  have h4 : a * r * a⁻¹ * r⁻¹ ∈ S ⊓ L ⊓ conjugate (S ⊓ L) y := mem_inf.mpr ⟨h1, h2⟩
  rw [hRy, mem_bot] at h4
  calc a * r = a * r * a⁻¹ * r⁻¹ * (r * a) := by group
    _ = r * a := by rw [h4, one_mul]

theorem inf_conjugate_R_eq_bot_of_le {P : Subgroup G} (hPS : P ≤ S) (hRP : S ⊓ L ≤ P)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {y : G}
    (hy : y ∈ normalizer (P : Set G)) (hyt : y * t * y⁻¹ ≠ t) :
    S ⊓ L ⊓ conjugate (S ⊓ L) y = ⊥ := by
  by_contra hne
  have hN : P ≤ normalizer ((S ⊓ L ⊓ conjugate (S ⊓ L) y : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun s hs v hv =>
      mem_inf.mpr ⟨h.conj_mem_R (hPS hs) hv.1, ?_⟩
    have hv2 := mem_conjugate_iff.mp (mem_inf.mp hv).2
    rw [mem_conjugate_iff]
    have hys : y * s * y⁻¹ ∈ S := hPS ((mem_normalizer_iff.mp hy s).mp hs)
    rw [show y * (s * v * s⁻¹) * y⁻¹ = (y * s * y⁻¹) * (y * v * y⁻¹) * (y * s * y⁻¹)⁻¹ by
      group]
    exact h.conj_mem_R hys hv2
  obtain ⟨u, huN, hu2, huS⟩ :=
    exists_involution_center (h.isPGroup_S.to_le hPS) (inf_le_left.trans hRP) hN hne
  have hne1 : ∀ {v : G}, orderOf v = 2 → v ≠ 1 := fun hv h1 => by
    rw [h1, orderOf_one] at hv
    omega
  have huR : u ∈ S ⊓ L := (mem_inf.mp huN).1
  have hut : u = t := by
    rcases h.center_R hna huR (fun r hr => (huS r (hRP hr)).symm) with h1 | h1
    · exact absurd h1 (hne1 hu2)
    · exact h1
  have hytR : y * t * y⁻¹ ∈ S ⊓ L := hut ▸ mem_conjugate_iff.mp (mem_inf.mp huN).2
  have hytZ : ∀ r ∈ S ⊓ L, y * t * y⁻¹ * r = r * (y * t * y⁻¹) := by
    intro r hr
    have h1 := h.tZ _ (hPS (conj_mem_of_mem_normalizer hy (hRP hr)))
    calc y * t * y⁻¹ * r = y * (t * (y⁻¹ * r * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * r * y) * t) * y⁻¹ := by rw [h1]
      _ = r * (y * t * y⁻¹) := by group
  rcases h.center_R hna hytR hytZ with h1 | h1
  · exact hne1 (by rw [orderOf_conj', h.t2]) h1
  · exact hyt h1

include ε in
theorem conj_t_eq_of_b (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q) {w b n : G}
    (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z)
    (hnw : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w y) (hn : n * w * n⁻¹ = w * z)
    (hb : b ∈ normalizer ((S ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G)) :
    b⁻¹ * t * b = t := by
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
  by_contra hbt
  have hbt' : b * t * b⁻¹ ≠ t := fun h1 => hbt (by
    calc b⁻¹ * t * b = b⁻¹ * (b * t * b⁻¹) * b := by rw [h1]
      _ = t := by group)
  have hRP := h.R_le_centralizer hwQ
  have hRb := h.inf_conjugate_R_eq_bot_of_le inf_le_left hRP hna hb hbt'
  have hcomm : ∀ a ∈ conjugate (S ⊓ L) b, ∀ r ∈ S ⊓ L, a * r = r * a := fun a ha r hr =>
    h.commute_of_inf_conjugate_eq_bot_of_le inf_le_left hRP hb hRb hr ha
  have hPS : conjugate (S ⊓ L) b ≤ S :=
    (conjugate_le_of_mem_normalizer hb hRP).trans inf_le_left
  obtain ⟨y₀, hy₀R, hy₀2, hnc⟩ := h.exists_noncentral_involution_R hna
  obtain ⟨c₀, hc₀R, hc₀⟩ := h.exists_conj_mul_t ε hD (mem_inf.mp hy₀R).1 hy₀2 hnc
  have hA : b⁻¹ * y₀⁻¹ * b ∈ conjugate (S ⊓ L) b := by
    rw [mem_conjugate_iff, show b * (b⁻¹ * y₀⁻¹ * b) * b⁻¹ = y₀⁻¹ by group]
    exact inv_mem hy₀R
  have hB : b⁻¹ * c₀⁻¹ * b ∈ conjugate (S ⊓ L) b := by
    rw [mem_conjugate_iff, show b * (b⁻¹ * c₀⁻¹ * b) * b⁻¹ = c₀⁻¹ by group]
    exact inv_mem hc₀R
  have htQ : b⁻¹ * t * b ∈ Q := by
    have h1 := h.commutator_mem_Q_of_centralizes ε hD hPS hcomm hA hB
    have h2 : t = y₀⁻¹ * (c₀⁻¹ * y₀ * c₀) := by rw [hc₀]; group
    rwa [show b⁻¹ * y₀⁻¹ * b * (b⁻¹ * c₀⁻¹ * b) * (b⁻¹ * y₀⁻¹ * b)⁻¹ * (b⁻¹ * c₀⁻¹ * b)⁻¹ =
      b⁻¹ * (y₀⁻¹ * (c₀⁻¹ * y₀ * c₀)) * b by group, ← h2] at h1
  have htS₀ : b⁻¹ * t * b ∈ S ⊓ centralizer ({w} : Set G) :=
    conj_mem_of_mem_normalizer hb (hRP h.tR)
  have htt : b⁻¹ * t * b * (b⁻¹ * t * b) = 1 := by
    rw [show b⁻¹ * t * b * (b⁻¹ * t * b) = b⁻¹ * (t * t) * b by group, ht22]; group
  have htc : IsConj t (b⁻¹ * t * b) := isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv]⟩
  have hwzw : IsConj w (w * z) := isConj_iff.mpr ⟨n, hn⟩
  rcases h.mem_W hwQ hw22 hw1 hwz htQ htt
      (mem_centralizer_singleton_iff.mp (mem_inf.mp htS₀).2) with h1 | h1 | h1 | h1 <;>
    rw [h1] at htc
  · exact h.t_ne_one (isConj_one_left.mp htc)
  · exact hnw t h.tZ htc.symm
  · exact h.t_not_mem_Q (hz51 t h.tZ htc.symm)
  · exact hnw t h.tZ (hwzw.trans htc.symm)

end Sec5

end CFSG.ComponentClassification.Foote5
