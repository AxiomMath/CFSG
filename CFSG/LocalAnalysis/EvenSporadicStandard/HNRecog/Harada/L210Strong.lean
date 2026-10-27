module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Weak
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.GoldCorCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

theorem L210_strongly_closed (h : L210Hyp A) :
    ∃ T : Sylow 2 X, (T : Subgroup X) ≤ normalizer (A : Set X) ∧ A ≤ (T : Subgroup X) ∧
      ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (T : Subgroup X) → g⁻¹ * a * g ∈ A := by
  obtain ⟨T, hTN, hG⟩ := L210_exists_sylow h
  refine ⟨T, hTN, hG.le, ?_⟩
  intro a ha g ht
  by_contra htA
  have ha2 : a * a = 1 := by
    have := h.elemAb.2 a ha
    simpa [pow_two] using this
  have ht2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    rw [show (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group]
    rw [ha2]
    group
  have hg : g * (g⁻¹ * a * g) * g⁻¹ ∈ A := by
    have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rwa [this]
  have hC : Nat.card ↥(A ⊓ centralizer ({(g⁻¹ * a * g)} : Set X)) ≤ 16 :=
    h.centralizer_le (g⁻¹ * a * g) (hTN ht) htA ht2
  obtain ⟨B, hBT, hBe, hineq⟩ := goldschmidt_cor_four hG ht ht2 hg
  obtain ⟨D, hDB, hDF, hcard⟩ :=
    exists_complement_of_isElemAbelian hBe (inf_le_left : B ⊓ A ≤ B)
  have hFpos : 0 < Nat.card ↥(B ⊓ A) := Nat.card_pos
  have hineq2 : 2 ^ 8 * Nat.card ↥(B ⊓ A) ≤ 16 * (Nat.card D * Nat.card ↥(B ⊓ A)) := by
    calc 2 ^ 8 * Nat.card ↥(B ⊓ A)
        = Nat.card A * Nat.card ↥(B ⊓ A) := by rw [h.card]
      _ ≤ Nat.card ↥(A ⊓ centralizer ({(g⁻¹ * a * g)} : Set X)) * Nat.card B := hineq
      _ ≤ 16 * Nat.card B := Nat.mul_le_mul_right (Nat.card B) hC
      _ = 16 * (Nat.card D * Nat.card ↥(B ⊓ A)) := by rw [← hcard]
  have hineq3 : 2 ^ 8 * Nat.card ↥(B ⊓ A) ≤ (16 * Nat.card D) * Nat.card ↥(B ⊓ A) := by
    calc 2 ^ 8 * Nat.card ↥(B ⊓ A) ≤ 16 * (Nat.card D * Nat.card ↥(B ⊓ A)) := hineq2
      _ = (16 * Nat.card D) * Nat.card ↥(B ⊓ A) := by rw [Nat.mul_assoc]
  have h256 : 2 ^ 8 ≤ 16 * Nat.card D := Nat.le_of_mul_le_mul_right hineq3 hFpos
  have h16 : 16 ≤ Nat.card D := by
    have h256' : (256 : ℕ) ≤ 16 * Nat.card D := by
      have : (2 : ℕ) ^ 8 = 256 := by norm_num
      rwa [this] at h256
    omega
  have hDN : D ≤ normalizer (A : Set X) := hDB.trans (hBT.trans hTN)
  have hDe : IsElemAbelian 2 D := hBe.mono hDB
  have hDA : D ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxF : x ∈ D ⊓ (B ⊓ A) := ⟨hx.1, hDB hx.1, hx.2⟩
    rw [hDF] at hxF
    exact hxF
  have hle8 : Nat.card D ≤ 8 := h.noE16 D hDN hDe hDA
  omega

end CFSG.EvenSporadicStandard.HNRecog.Harada
