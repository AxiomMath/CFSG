module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9
public import CFSG.LocalAnalysis.GLTheoremB.GammaBasic

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Comm

variable {X : Type*} [Group X]

theorem commutator_le_normalizer_of_perm {Y B : Subgroup X} {L : Subgroup X}
    (hBL : B ≤ Subgroup.normalizer (L : Set X))
    (h : ∀ z ∈ Y, B ≤ Subgroup.normalizer (GLBConj z L : Set X) ∨
      Y ≤ Subgroup.normalizer (GLBConj z L : Set X)) :
    ⁅Y, B⁆ ≤ Subgroup.normalizer (L : Set X) := by
  have hA : ∀ z ∈ Y, B ≤ Subgroup.normalizer (GLBConj z L : Set X) := by
    intro z hz
    rcases h z hz with hb | hy
    · exact hb
    · have hzN : z ∈ Subgroup.normalizer (GLBConj z L : Set X) := hy hz
      rw [mem_normalizer_iff_gLBConj_eq] at hzN
      have e : GLBConj z L = L := by
        have := congrArg (GLBConj z⁻¹) hzN
        rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this
      rw [e]
      exact hBL
  rw [Subgroup.commutator_le]
  intro y hy b hb
  have h1 : b ∈ Subgroup.normalizer (GLBConj y L : Set X) := hA y hy hb
  rw [mem_normalizer_iff_gLBConj_eq] at h1
  have h2 : y * b * y⁻¹ ∈ Subgroup.normalizer (L : Set X) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have : GLBConj (y * b * y⁻¹) L = GLBConj y⁻¹ (GLBConj (y * b) L) := by
      rw [gLBConj_gLBConj]
    rw [this, ← gLBConj_gLBConj, h1, gLBConj_inv_gLBConj]
  have e : ⁅y, b⁆ = (y * b * y⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ (hBL hb))

end Comm

theorem le_pPrimeCoreOf_centralizer_of_isSCp {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) {B : Subgroup X} (hB : IsSCp p ⊤ B) {H : Subgroup X}
    (hHC : H ≤ Subgroup.centralizer (B : Set X)) (hH : Nat.Coprime p (Nat.card H)) :
    H ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hN, hNc, hq⟩ := hasNormalPComplement_centralizer_of_isSCp hp hodd hB
  intro h hh
  have hN' : N ≤ GLAPPrimeCore p ↥(Subgroup.centralizer (B : Set X)) := le_sSup ⟨hN, hNc⟩
  set h' : ↥(Subgroup.centralizer (B : Set X)) := ⟨h, hHC hh⟩ with hh'
  have hmem : h' ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    obtain ⟨k, hk⟩ := hq (h' : ↥(Subgroup.centralizer (B : Set X)) ⧸ N)
    have h1 : orderOf (h' : ↥(Subgroup.centralizer (B : Set X)) ⧸ N) ∣ orderOf h' :=
      orderOf_map_dvd (QuotientGroup.mk' N) h'
    have h2 : orderOf h' ∣ Nat.card H := by
      have : orderOf h' = orderOf (⟨h, hh⟩ : H) := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      rw [this]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (h' : ↥(Subgroup.centralizer (B : Set X)) ⧸ N) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have h4 : Nat.Coprime (orderOf (h' : ↥(Subgroup.centralizer (B : Set X)) ⧸ N)) p :=
      (Nat.Coprime.coprime_dvd_left (h1.trans h2) hH.symm)
    have h5 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h4) h3
    exact orderOf_eq_one_iff.1 h5
  exact ⟨h', hN' hmem, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
