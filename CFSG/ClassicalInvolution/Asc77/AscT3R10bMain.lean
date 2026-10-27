module

public import CFSG.ClassicalInvolution.Asc77.AscT3R10bSwap
public import CFSG.ClassicalInvolution.Asc77.AscT3R10bFour

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Pure

variable {G : Type} [Group G]

theorem pow_odd_mul_self {b : G} (hb4 : b ^ 4 = 1) {n : ℕ} (hn : Odd n) :
    b ^ n * b ^ n = b * b := by
  obtain ⟨k, rfl⟩ := hn
  rw [← pow_add, show 2 * k + 1 + (2 * k + 1) = 4 * k + 2 by ring, pow_add, pow_mul, hb4,
    one_pow, one_mul, pow_two]

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.r10b_SX_le_N (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z) :
    (S : Subgroup G) ⊓ sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (K : Set G) := by
  rw [d.late_SX c3]
  exact sup_le (sup_le (d.hR.1.trans Subgroup.le_normalizer) (d.hR'.1.trans d.late_K'_le))
    (d.hVW.trans d.late_W_le_N_K)

theorem Std20.r10b_not_conj_swap (d : Std20 p f K K' J S R R' W V z t) {b c h : G}
    (hb : b ∈ (S : Subgroup G)) (hbK : conjSub b K = K')
    (hb2 : b * b = t ∨ b * b = z * t) (hb4 : b ^ 4 = 1) (hc2 : c * c ≠ 1)
    (hc4 : (c * c) * (c * c) = 1) (hcN : conjSub c K = K) (hcM : c * c = z ∨ c ∈ W) {n : ℕ}
    (hn : Odd n) (hbc : b ^ n = h * c * h⁻¹) : False := by
  obtain ⟨L₀, hL₀Ω, hL₀i, hcL₀⟩ : ∃ L₀ ∈ CoreAssembly.conjClass K,
      IsUniqueInvolution L₀ (c * c) ∧ conjSub c L₀ = L₀ := by
    rcases hcM with hcc | hW
    · exact ⟨K, d.late_mem_K, hcc ▸ d.viol.hzK, hcN⟩
    · obtain ⟨m, -, hme, hmem⟩ := d.late_W_four_mem hW hc2 hc4
      obtain ⟨hL₁, hL₂, -, hL₁i, hL₂i⟩ := d.late_member_data m
      rcases hmem with h' | h'
      · exact ⟨conjSub m K, hL₁, hme ▸ hL₁i, conjSub_eq_self_of_mem h'⟩
      · exact ⟨conjSub m K', hL₂, hme ▸ hL₂i, conjSub_eq_self_of_mem h'⟩
  have hL₁Ω : conjSub h L₀ ∈ CoreAssembly.conjClass K := d.hyp.conjInvariant h L₀ hL₀Ω
  have hbb : b * b = h * (c * c) * h⁻¹ := by
    rw [← pow_odd_mul_self hb4 hn, hbc]
    group
  have hL₁i : IsUniqueInvolution (conjSub h L₀) (b * b) := by
    rw [hbb]
    exact hL₀i.conj h
  have hbnN : b ^ n ∈ Subgroup.normalizer ((conjSub h L₀ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, hbc, conjSub_mul (h * c) h⁻¹, conjSub_inv_conjSub,
      conjSub_mul, hcL₀]
  have hbN : b ∈ Subgroup.normalizer ((conjSub h L₀ : Subgroup G) : Set G) := by
    have h1 : (b ^ n) ^ n = b := by
      obtain ⟨k, rfl⟩ := hn
      rw [← pow_mul, show (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 by ring, pow_add,
        pow_mul, hb4, one_pow, one_mul, pow_one]
    rw [← h1]
    exact Subgroup.pow_mem _ hbnN n
  have ha₀ : b * b = z ∨ b * b = t ∨ b * b = z * t := by
    rcases hb2 with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  obtain ⟨m₀, -, hme₀⟩ := d.late_exists_m ha₀
  have hL := d.late_members_of_inv hme₀ hL₁Ω hL₁i
  have hσa : b * (b * b) * b⁻¹ = b * b := by group
  exact d.late_swap_not_N_member hb hbK hσa hme₀ ha₀ hL (mem_normalizer_iff_conjSub_eq.mp hbN)

end Std

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Res10bP1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Nat.card R = 8 →
          ∀ a ∈ (S : Subgroup G), ∀ g : G, g * z * g⁻¹ = a →
            a ∈ sec20X (CoreAssembly.conjClass K) z K K'

theorem c20_10b_of_P1 (h1 : Res10bP1 p f) : C20_10b p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 h8
  have hTX := d.r10b_TX c8 h8
  obtain ⟨b, hbS, hbK, hb2⟩ := d.late_exists_b h8 c3 hTX
  have hz2 := d.viol.hzK.sq
  have ht2 := d.viol.hzJ.sq
  have hzt := d.late_zt_comm
  have hb4 : (b * b) * (b * b) = 1 := by
    rcases hb2 with h | h
    · rw [h]
      exact ht2
    · rw [h]
      calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hz2, ht2, one_mul]
  have hb4' : b ^ 4 = 1 := by
    rw [show b ^ 4 = (b * b) * (b * b) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hb4
  have hbb1 : b * b ≠ 1 := by
    rcases hb2 with h | h
    · rw [h]
      exact d.viol.hzJ.ne_one
    · rw [h]
      intro h1
      apply d.late_ne_inv
      have h3 : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right hz2
  have hnc : ∃ x y : G, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply d.ne
    have h3 : conjSub b K = K := by
      ext x
      rw [mem_conjSub_iff]
      have : b⁻¹ * x * b = x := by
        rw [mul_assoc, hcon x b, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
    exact hbK.symm.trans h3
  have ha₀ : b * b = z ∨ b * b = t ∨ b * b = z * t := by
    rcases hb2 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨m₀, -, hme₀⟩ := d.late_exists_m ha₀
  rcases d.swap_fusion hnc hbS hbK hb4 with ⟨n, h, c, hn, hcS, hcK, hcform⟩ |
    ⟨h, c, hcS, hcK, hcform⟩
  · have hcX : c ∈ sec20X (CoreAssembly.conjClass K) z K K' := hTX c hcS hcK
    have hcc : c * c = h⁻¹ * (b * b) * h := by
      have h3 : c * c = h⁻¹ * (b ^ n * b ^ n) * h := by rw [hcform]; group
      rw [h3, pow_odd_mul_self hb4' hn]
    have hc2 : c * c ≠ 1 := by
      intro h0
      apply hbb1
      have h3 : b * b = h * (c * c) * h⁻¹ := by rw [hcc]; group
      rw [h3, h0]
      group
    have hc4 : (c * c) * (c * c) = 1 := by
      rw [hcc]
      calc h⁻¹ * (b * b) * h * (h⁻¹ * (b * b) * h) = h⁻¹ * ((b * b) * (b * b)) * h := by group
        _ = 1 := by rw [hb4]; group
    have hbc : b ^ n = h * c * h⁻¹ := by rw [hcform]; group
    exact d.r10b_not_conj_swap hbS hbK hb2 hb4' hc2 hc4 hcK
      (d.r10b_four c3 c8 h8 hcS hcX hc2 hc4) hn hbc
  · have hcz : (h⁻¹ * m₀) * z * (h⁻¹ * m₀)⁻¹ = c := by rw [hcform, ← hme₀]; group
    have hcX := h1 G K K' J S R R' W V z t d c3 c4 c5 c7 c8 h8 c hcS _ hcz
    exact hcK (mem_normalizer_iff_conjSub_eq.mp (d.r10b_SX_le_N c3 ⟨hcS, hcX⟩))

end CFSG.ClassicalInvolution.Asc77.T3CII
