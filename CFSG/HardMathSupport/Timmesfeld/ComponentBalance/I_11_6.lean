module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Reduction
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Glue
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists
public import CFSG.HardMathSupport.Timmesfeld.Proving.NormalizerPPowerEq
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem partII (hT : KernelT) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X}
    (hB : IsSCp p ⊤ B) {L : Subgroup X} (hL : GLAPComponent p ⊤ L)
    (hBL : B ≤ Subgroup.normalizer (L : Set X)) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (L : Set X) := by
  obtain ⟨x, hxL, hxB, hxord, hxnc⟩ := exists_noncentral_normalizing_elt hT hX hp hodd hO hB hL hBL
  exact CFSG.HardMathSupport.Timmesfeld.Proving.normalizes_pPrimeCore_centralizer_of_pPower_eq_one
    hp hO hL hxL hxB hxord hxnc

theorem input11_6Reduced_of_kernels (hK : Kernel11_2) (hT : KernelT) : Input11_6Reduced := by
  intro X _ _ hX p hp hodd hO B hB hrank Y hYc hBY L hL
  have hBpg : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2.1.2 g.1 g.2)⟩
  have hconj : ∀ z : X, GLAPComponent p ⊤ (GLBConj z L) := fun z => by
    have h := glaPComponent_gLBConj hL z
    have htop : GLBConj z (⊤ : Subgroup X) = ⊤ := by
      ext y; simp [mem_gLBConj]
    rwa [htop] at h
  by_cases hBL : B ≤ Subgroup.normalizer (L : Set X)
  · have hcomm : ⁅Y, B⁆ ≤ Subgroup.normalizer (L : Set X) :=
      commutator_le_normalizer_of_perm hBL (fun z _ => by
        by_cases hB' : B ≤ Subgroup.normalizer (GLBConj z L : Set X)
        · exact Or.inl hB'
        · exact Or.inr (partI hK hX hp hodd hO hB hrank hYc hBY (hconj z) hB'))
    have hYcop : Nat.Coprime p (Nat.card (Y ⊓ Subgroup.centralizer (B : Set X) : Subgroup X)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hYc
    have hcent : Y ⊓ Subgroup.centralizer (B : Set X) ≤ Subgroup.normalizer (L : Set X) :=
      (le_pPrimeCoreOf_centralizer_of_isSCp hp hodd hB inf_le_right hYcop).trans
        (partII hT hX hp hodd hO hB hL hBL)
    have : Fact p.Prime := ⟨hp⟩
    exact (le_sup_centralizer_commutator hBpg hBY hYc).trans (sup_le hcent hcomm)
  · exact partI hK hX hp hodd hO hB hrank hYc hBY hL hBL

theorem input11_6_of_kernels (hK : Kernel11_2) (hT : KernelT) : Input11_6 :=
  input11_6_of_reduced (input11_6Reduced_of_kernels hK hT)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
