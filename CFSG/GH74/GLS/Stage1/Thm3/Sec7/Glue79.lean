module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue79a

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem interchanges_mul {K₁ K₂ : Subgroup G} {t s : G} (ht : Interchanges t K₁ K₂)
    (hs₁ : s ∈ normalizer (K₁ : Set G)) (hs₂ : s ∈ normalizer (K₂ : Set G)) :
    Interchanges (t * s) K₁ K₂ := by
  obtain ⟨h1, h2⟩ := (interchanges_iff t).1 ht
  refine (interchanges_iff (t * s)).2 ⟨?_, ?_⟩
  · rw [← M.cj_cj t s K₁, h1]
    exact M.cj_eq_iff_normalizer.2 hs₂
  · rw [← M.cj_cj t s K₂, h2]
    exact M.cj_eq_iff_normalizer.2 hs₁

namespace Cfg7

theorem hyp4A (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : Hyp4A S z := by
  intro x hx hxc
  apply h.std.nonfused x _ hxc
  unfold Rz at hx
  rw [h.std.hQ] at hx
  exact sup_le le_rfl (zpowers_le.2 (h.z_mem_Pz hII)) hx

theorem t_mul_swap (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {s : G} (hs : s ∈ S1 S K₁) :
    Interchanges (t * s) K₁ K₂ :=
  interchanges_mul h.ch.t_swap hs.2 (h.S1_norm₂ hII hs)

theorem t_mul_nS1 (h : Cfg7 G z S K₁ K₂ t u q) {s : G} (hs : s ∈ S1 S K₁) : t * s ∉ S1 S K₁ := by
  intro hh
  apply h.t_nS1
  have := (S1 S K₁).mul_mem hh ((S1 S K₁).inv_mem hs)
  simpa using this

end Cfg7

theorem lemma_7_9 (hII : II4_4_4_center) (h12d : IVK_1_2d_lifted) (h31c : IVK_3_1c_lifted)
    (hg : IG_10_32_P) (hL79 : L79_C_S_u) (hL45 : Lemma4_5) : Lemma7_9 := by
  intro G _ _ z S K₁ K₂ t u q h hc73 hc74 hidx D hD hdih y hyD hyP hyo
  have hyS₁ : y ∈ S1 S K₁ := hD.le hyD
  have hyS : y ∈ S := hyS₁.1
  have htS : t ∈ S := h.ch.t_mem
  have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 (hDE hyD).2
  have hty : t * y = y * t := hyt.symm
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hyS)
  have hy2 : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hyo
  have hy1 : y ≠ 1 := ne_one_of_orderOf_eq_two hyo
  have hz2 := h.z_sq
  have hzP := h.z_mem_Pz hII
  have hzS := h.z_mem_S hII
  have c78 := lemma_7_8 hII h12d G z S K₁ K₂ t u q h hc73 hc74 hidx D hD hdih y hyD hyP hyo
  have cy : Concl72abcf z S K₁ K₂ t q y := c78 y (by simp)
  have hsq : ∀ s ∈ S, s * s ∈ Pz S z :=
    h.sq_mem_P hII hy2 hty cy.2.2.2.1.2 (sup_le (zpowers_le.2 htS) (zpowers_le.2 hyS))
  have hxy : ∃ p ∈ Pz S z, IsConj z (p * y) :=
    h.exists_conj_in_coset hII hL79 hc73 hc74 cy hy1 hsq hyS hy2 hy1 hyP
  have hty_S₁ : t * y ∉ S1 S K₁ := h.t_mul_nS1 hyS₁
  have htyS : t * y ∈ S := S.mul_mem htS hyS
  have hty2 : (t * y) * (t * y) = 1 := by
    calc t * y * (t * y) = t * (y * t) * y := by group
      _ = t * (t * y) * y := by rw [hty]
      _ = (t * t) * (y * y) := by group
      _ = 1 := by rw [h.t_sq, hy2, mul_one]
  have hty1 : t * y ≠ 1 := by
    intro hh
    apply hty_S₁
    rw [hh]
    exact one_mem _
  have htyP : t * y ∉ Pz S z := fun hh => hty_S₁ (h.Pz_le_S1 hII hh)
  have hxty : ∃ p ∈ Pz S z, IsConj z (p * (t * y)) :=
    h.exists_conj_in_coset hII hL79 hc73 hc74 cy hy1 hsq htyS hty2 hty1 htyP
  obtain ⟨p, hp, hpy⟩ := hxy
  have hpyS : p * y ∈ S := S.mul_mem (h.Pz_le_S1 hII hp).1 hyS
  have hpyo : orderOf (p * y) = 2 := orderOf_eq_two_of_isConj h.std.std.orderOf_z hpy
  have h1P : y * y⁻¹ ∈ Pz S z := by
    rw [mul_inv_cancel]
    exact one_mem _
  have hyconj : IsConj z y := by
    obtain ⟨c, -, hc⟩ := h31c G z S K₁ K₂ t u q y h cy hy1 (p * y) hpyS y hyS (by simpa using hp) h1P
      hpyo hyo
    exact hpy.trans (isConj_iff.2 ⟨c, hc⟩)
  have hyzconj : IsConj z (y * z) := by
    have hyzS : y * z ∈ S := S.mul_mem hyS hzS
    have hyz2 : (y * z) * (y * z) = 1 := by
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hyz]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy2, hz2, mul_one]
    have hyz1 : y * z ≠ 1 := by
      intro hh
      apply hyP
      have : y = z⁻¹ := eq_inv_of_mul_eq_one_left hh
      rw [this]
      exact (Pz S z).inv_mem hzP
    have hyzo : orderOf (y * z) = 2 := orderOf_eq_prime (by simpa [pow_two] using hyz2) hyz1
    have hyzP : y * z * y⁻¹ ∈ Pz S z := by
      have : y * z * y⁻¹ = z := by
        calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [hyz]
          _ = z := by group
      rw [this]
      exact hzP
    obtain ⟨c, -, hc⟩ := h31c G z S K₁ K₂ t u q y h cy hy1 (y * z) hyzS y hyS hyzP h1P hyzo hyo
    exact hyconj.trans (isConj_iff.2 ⟨c, hc⟩).symm
  refine ⟨⟨hyconj, hyzconj⟩, ?_⟩
  obtain ⟨p', hp', hpty⟩ := hxty
  have hv : orderOf (p' * (t * y)) = 2 := orderOf_eq_two_of_isConj h.std.std.orderOf_z hpty
  have htyo : orderOf (t * y) = 2 := orderOf_eq_prime (by simpa [pow_two] using hty2) hty1
  have hint : Interchanges (t * y) K₁ K₂ := h.t_mul_swap hII hyS₁
  obtain ⟨c, -, hc⟩ := hg G z S K₁ K₂ h.std.std (t * y) htyS htyo hint (p' * (t * y))
    (by rw [mul_inv_cancel_right]; exact hp') hv
  rcases hc with hc | hc
  ·
    have hconjty : IsConj z (t * y) := hpty.trans (isConj_iff.2 ⟨c, hc⟩).symm
    have hne : t * y ≠ z := by
      intro hh
      apply hty_S₁
      rw [hh]
      exact h.Pz_le_S1 hII hzP
    exact ⟨y, by simp, hconjty,
      (hL45 G z S K₁ K₂ h.std.std (h.hyp4A hII) (t * y) htyS hconjty hne hint).2.2⟩
  ·
    have hyzS₁ : y * z ∈ S1 S K₁ := (S1 S K₁).mul_mem hyS₁ (h.Pz_le_S1 hII hzP)
    have hconjtyz : IsConj z (t * (y * z)) := by
      rw [← mul_assoc]
      exact hpty.trans (isConj_iff.2 ⟨c, hc⟩).symm
    have hne : t * (y * z) ≠ z := by
      intro hh
      apply h.t_mul_nS1 hyzS₁
      rw [hh]
      exact h.Pz_le_S1 hII hzP
    have htyzS : t * (y * z) ∈ S := S.mul_mem htS (S.mul_mem hyS hzS)
    exact ⟨y * z, by simp, hconjtyz,
      (hL45 G z S K₁ K₂ h.std.std (h.hyp4A hII) (t * (y * z)) htyzS hconjtyz hne
        (h.t_mul_swap hII hyzS₁)).2.2⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
