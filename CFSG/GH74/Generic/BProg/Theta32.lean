module

public import CFSG.GH74.GLS.C3.Layer1.Th2Sig10
public import CFSG.GH74.GLS.C3.Layer1.Th2Theta

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74.GLS Subgroup

variable {G : Type} [Group G]

theorem pPrimeCoreOf_map_conj (n : G) (H : Subgroup G) :
    pPrimeCoreOf 2 (H.map (MulAut.conj n).toMonoidHom) =
      (pPrimeCoreOf 2 H).map (MulAut.conj n).toMonoidHom :=
  Th2.pPrimeCoreOf_cj n H

theorem thetaHalf_map_conj [Finite G] (k : ℕ) (n : G) (B : Subgroup G) :
    thetaHalf k (B.map (MulAut.conj n).toMonoidHom) =
      (thetaHalf k B).map (MulAut.conj n).toMonoidHom :=
  Th2.thetaHalf_cj k n B

theorem normalizer_le_normalizer_thetaHalf_one [Finite G] {A B : Subgroup G} (hA : IsE 3 ⊤ A)
    (hbal : IsKBal 2 A) (hweak : IsWeakKBal 1 A) (hB : IsE 2 A B) :
    normalizer (B : Set G) ≤ normalizer (thetaHalf 1 A : Set G) := by
  intro n hn
  have hEq : thetaHalf 1 B = thetaHalf 1 A := b_ig_21_10 G 1 le_rfl A B hA hbal hweak hB
  have hBn : B.map (MulAut.conj n).toMonoidHom = B := Th2.cj_eq_of_mem_normalizer hn
  refine Th2.mem_normalizer_of_cj_eq ?_
  show (thetaHalf 1 A).map (MulAut.conj n).toMonoidHom = thetaHalf 1 A
  calc (thetaHalf 1 A).map (MulAut.conj n).toMonoidHom
      = (thetaHalf 1 B).map (MulAut.conj n).toMonoidHom := by rw [hEq]
    _ = thetaHalf 1 (B.map (MulAut.conj n).toMonoidHom) := (thetaHalf_map_conj 1 n B).symm
    _ = thetaHalf 1 B := by rw [hBn]
    _ = thetaHalf 1 A := hEq

theorem gammaK_le_normalizer_thetaHalf_one [Finite G] {A : Subgroup G} (hA : IsE 3 ⊤ A)
    (hbal : IsKBal 2 A) (hweak : IsWeakKBal 1 A) :
    gammaK 2 A 2 ≤ normalizer (thetaHalf 1 A : Set G) :=
  iSup_le fun _ => iSup_le fun hQA => iSup_le fun hQr =>
    normalizer_le_normalizer_thetaHalf_one hA hbal hweak
      ⟨hQA, Th2Sig6.isElementaryAbelian_of_le hA.2.1 hQA, hQr⟩

@[expose] def thetaHalfPrime (B : Subgroup G) : Subgroup G :=
  ⨆ (D : Subgroup G) (_ : IsE 2 B D) (_ : pRank 2 ↥D = 2), thetaHalf 1 D

theorem thetaHalfPrime_le_thetaHalf_one [Finite G] {A : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hbal : IsKBal 2 A) :
    thetaHalfPrime A ≤ thetaHalf 1 A :=
  iSup_le fun _ => iSup_le fun hD => iSup_le fun _ => Th2Sig10.thetaHalf_le_of_le hAe hbal hD

theorem thetaHalf_one_le_thetaHalfPrime [Finite G] {A : Subgroup G} (hA : IsE 3 ⊤ A)
    (hbal : IsKBal 2 A) (hweak : IsWeakKBal 1 A) : thetaHalf 1 A ≤ thetaHalfPrime A := by
  obtain ⟨D, hDA, hDcard⟩ := Th2Sig6.exists_sub_card hA.2.1 (k := 2) (le_trans (by norm_num) hA.2.2)
  have hDE : IsE 2 A D := Th2Sig6.isE_of_card hA.2.1 hDA hDcard
  have := hDE.2.1
  have hDr : pRank 2 ↥D = 2 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hDcard
  have hEq : thetaHalf 1 D = thetaHalf 1 A := b_ig_21_10 G 1 le_rfl A D hA hbal hweak hDE
  exact hEq.symm.le.trans (le_iSup₂_of_le D hDE (le_iSup_of_le hDr le_rfl))

theorem thetaHalf_one_eq_thetaHalfPrime [Finite G] {A : Subgroup G} (hA : IsE 3 ⊤ A)
    (hbal : IsKBal 2 A) (hweak : IsWeakKBal 1 A) : thetaHalf 1 A = thetaHalfPrime A :=
  le_antisymm (thetaHalf_one_le_thetaHalfPrime hA hbal hweak)
    (thetaHalfPrime_le_thetaHalf_one hA.2.1 hbal)

theorem thetaHalf_one_ne_bot_iff_thetaHalfPrime_ne_bot [Finite G] {A : Subgroup G}
    (hA : IsE 3 ⊤ A) (hbal : IsKBal 2 A) (hweak : IsWeakKBal 1 A) :
    thetaHalf 1 A ≠ ⊥ ↔ thetaHalfPrime A ≠ ⊥ := by
  rw [thetaHalf_one_eq_thetaHalfPrime hA hbal hweak]

end CFSG.GH74.Generic.BProg
