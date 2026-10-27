module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511I
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511H

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

theorem card_centralizer_Q_le_two_of_field (hKF : Foote5FieldCentralizerC)
    (h𝕊 : FooteSimpleType 𝕊) (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {s : G}
    (hsN : s ∈ normalizer (S : Set G)) (hRs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥)
    (hz : z = s⁻¹ * t * s) {r : G} (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : r * r = 1)
    (hrinn : actG L ε r ∉ innAut5 𝕊) :
    Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_self
  have ht2 := h.t_mul_self
  have hrS : r ∈ S := conjugate_le_of_mem_normalizer hsN inf_le_left hr
  have hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r := fun ρ hρ =>
    h.commute_of_inf_conjugate_eq_bot hsN hRs hρ hr
  have hrz : r * z = z * r := h.zS r hrS
  have hzS := h.zS_mem
  have hz1 : actG L ε z = 1 := (h.actG_eq_one_iff_mem_Q ε hzS).mpr h.zQ
  set r' := s * r * s⁻¹ with hr'def
  have hr' : r' ∈ S ⊓ L := mem_conjugate_iff.mp hr
  have hr'2 : r' * r' = 1 := by
    rw [hr'def, show s * r * s⁻¹ * (s * r * s⁻¹) = s * (r * r) * s⁻¹ by group, hr2]
    group
  have hrr' : r = s⁻¹ * r' * s := by rw [hr'def]; group
  have hr'1 : r' ≠ 1 := fun h1 => hrinn (by
    rw [hrr', h1, show s⁻¹ * 1 * s = 1 by group, actG_one]
    exact one_mem _)
  have hr't : r' ≠ t := fun h1 => hrinn (by
    rw [hrr', h1, ← hz, hz1]
    exact one_mem _)
  obtain ⟨d₀, hd₀, hd₀c⟩ := h.exists_conj_mul_t_R hna hr' hr'2 hr'1 hr't
  obtain ⟨y₀, hy₀r, hy₀t⟩ := h.exists_conj_t_of_noncentral hna hr' hr'2 hr'1 hr't
  have hd₀t : d₀ * t = t * d₀ := h.tZ d₀ (mem_inf.mp hd₀).1
  set d := s⁻¹ * d₀ * s with hd
  set y := s⁻¹ * y₀ * s with hy
  have hdz : d * z * d⁻¹ = z := by
    rw [hd, hz, show s⁻¹ * d₀ * s * (s⁻¹ * t * s) * (s⁻¹ * d₀ * s)⁻¹ =
      s⁻¹ * (d₀ * t * d₀⁻¹) * s by group, hd₀t, mul_inv_cancel_right]
  have hdr : d * r * d⁻¹ = z * r := by
    rw [hd, hrr', hz, show s⁻¹ * d₀ * s * (s⁻¹ * r' * s) * (s⁻¹ * d₀ * s)⁻¹ =
      s⁻¹ * (d₀ * r' * d₀⁻¹) * s by group, hd₀c]
    group
  have hyr : y * r * y⁻¹ = r := by
    rw [hy, hrr', show s⁻¹ * y₀ * s * (s⁻¹ * r' * s) * (s⁻¹ * y₀ * s)⁻¹ =
      s⁻¹ * (y₀ * r' * y₀⁻¹) * s by group, hy₀r]
  have hyz : y * z * y⁻¹ = r * z := by
    rw [hy, hz, hrr', show s⁻¹ * y₀ * s * (s⁻¹ * t * s) * (s⁻¹ * y₀ * s)⁻¹ =
      s⁻¹ * (y₀ * t * y₀⁻¹) * s by group, hy₀t]
    group
  set n₀ := d * y with hn₀
  have hn₀z : n₀ * z * n₀⁻¹ = r := by
    calc n₀ * z * n₀⁻¹ = d * (y * z * y⁻¹) * d⁻¹ := by rw [hn₀]; group
      _ = (d * r * d⁻¹) * (d * z * d⁻¹) := by rw [hyz]; group
      _ = z * r * z := by rw [hdr, hdz]
      _ = r := by rw [mul_assoc, hrz, ← mul_assoc, hz2, one_mul]
  have hn₀r : n₀ * r * n₀⁻¹ = r * z := by
    calc n₀ * r * n₀⁻¹ = d * (y * r * y⁻¹) * d⁻¹ := by rw [hn₀]; group
      _ = r * z := by rw [hyr, hdr, hrz]
  set W := kleinFourOfCommutingInvolutions r z hr2 hz2 hrz with hWdef
  have hWmem : ∀ w ∈ W, w = r * z ∨ w = r ∨ w = z ∨ w = 1 := fun w hw =>
    (mem_kleinFour_iff hr2 hz2 hrz).mp hw
  have hmemW : ∀ w : G, (w = r * z ∨ w = r ∨ w = z ∨ w = 1) → w ∈ W := fun w hw =>
    (mem_kleinFour_iff hr2 hz2 hrz).mpr hw
  have hn₀rz : n₀ * (r * z) * n₀⁻¹ = z := by
    rw [show n₀ * (r * z) * n₀⁻¹ = (n₀ * r * n₀⁻¹) * (n₀ * z * n₀⁻¹) by group, hn₀r, hn₀z,
      mul_assoc, ← hrz, ← mul_assoc, hr2, one_mul]
  have hn₀W : ∀ w ∈ W, n₀⁻¹ * w * n₀ ∈ W := by
    intro w hw
    rcases hWmem w hw with hw' | hw' | hw' | hw'
    · rw [hw']
      refine hmemW _ (Or.inr (Or.inl ?_))
      calc n₀⁻¹ * (r * z) * n₀ = n₀⁻¹ * (n₀ * r * n₀⁻¹) * n₀ := by rw [hn₀r]
        _ = r := by group
    · rw [hw']
      refine hmemW _ (Or.inr (Or.inr (Or.inl ?_)))
      calc n₀⁻¹ * r * n₀ = n₀⁻¹ * (n₀ * z * n₀⁻¹) * n₀ := by rw [hn₀z]
        _ = z := by group
    · rw [hw']
      refine hmemW _ (Or.inl ?_)
      calc n₀⁻¹ * z * n₀ = n₀⁻¹ * (n₀ * (r * z) * n₀⁻¹) * n₀ := by rw [hn₀rz]
        _ = r * z := by group
    · rw [hw']
      exact hmemW _ (Or.inr (Or.inr (Or.inr (by group))))
  have hCW : conjugate (centralizer (W : Set G)) n₀⁻¹ = centralizer (W : Set G) := by
    refine eq_of_le_of_card_ge (fun c hc => ?_) (by rw [card_conjugate_eq_card])
    rw [mem_conjugate_iff, inv_inv] at hc
    refine mem_centralizer_iff.mpr fun w hw => ?_
    have h1 := mem_centralizer_iff.mp hc _ (hn₀W w hw)
    calc w * c = n₀ * ((n₀⁻¹ * w * n₀) * (n₀⁻¹ * c * n₀)) * n₀⁻¹ := by group
      _ = n₀ * ((n₀⁻¹ * c * n₀) * (n₀⁻¹ * w * n₀)) * n₀⁻¹ := by rw [h1]
      _ = c * w := by group
  have hXW : Q ⊓ centralizer ({r} : Set G) ≤ centralizer (W : Set G) := by
    intro x hx
    have hxr : x * r = r * x := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    have hxz : x * z = z * x := h.zS x (h.QS (mem_inf.mp hx).1)
    refine mem_centralizer_iff.mpr fun w hw => ?_
    rcases hWmem w hw with hw' | hw' | hw' | hw' <;> rw [hw']
    · rw [mul_assoc, ← hxz, ← mul_assoc, ← hxr, mul_assoc]
    · exact hxr.symm
    · exact hxz.symm
    · rw [one_mul, mul_one]
  obtain ⟨S₁, hS₁, hXS₁⟩ := exists_isSylowOf_ge_of_le hXW
    (h.isPGroup_Q.to_le inf_le_left)
  have hS₁' : IsSylowOf 2 (conjugate S₁ n₀⁻¹) (centralizer (W : Set G)) := by
    have h1 := Foote47.isSylowOf_conjugate hS₁ n₀⁻¹
    rwa [hCW] at h1
  obtain ⟨c, hcW, hc⟩ := hS₁.exists_mem_conj hS₁'
  set n := c⁻¹ * n₀ with hn
  have hnS₁ : n ∈ normalizer (S₁ : Set G) := by
    refine mem_normalizer_iff.mpr fun x => ?_
    have hx' : n * x * n⁻¹ = c⁻¹ * (n₀ * x * n₀⁻¹) * c := by rw [hn]; group
    have hconj : n₀ * x * n₀⁻¹ ∈ conjugate S₁ n₀⁻¹ ↔ x ∈ S₁ := by
      rw [mem_conjugate_iff, show n₀⁻¹ * (n₀ * x * n₀⁻¹) * n₀⁻¹⁻¹ = x by group]
    rw [hx', ← hc, hconj]
  have hcr : c * r = r * c :=
    (mem_centralizer_iff.mp hcW r (hmemW r (Or.inr (Or.inl rfl)))).symm
  have hcrz : c * (r * z) = (r * z) * c :=
    (mem_centralizer_iff.mp hcW _ (hmemW _ (Or.inl rfl))).symm
  have hnz : n * z * n⁻¹ = r := by
    rw [hn, show c⁻¹ * n₀ * z * (c⁻¹ * n₀)⁻¹ = c⁻¹ * (n₀ * z * n₀⁻¹) * c by group, hn₀z,
      mul_assoc, ← hcr, ← mul_assoc, inv_mul_cancel, one_mul]
  have hnr : n * r * n⁻¹ = r * z := by
    rw [hn, show c⁻¹ * n₀ * r * (c⁻¹ * n₀)⁻¹ = c⁻¹ * (n₀ * r * n₀⁻¹) * c by group, hn₀r,
      mul_assoc, ← hcrz, ← mul_assoc, inv_mul_cancel, one_mul]
  exact h.card_centralizer_Q_le_two ε hKF h𝕊 hrS hr2 hrinn hrR hrz hS₁.isPGroup hS₁.le hXS₁
    hnS₁ hnz hnr

end Sec5

end CFSG.ComponentClassification.Foote5
