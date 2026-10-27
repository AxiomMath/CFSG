module

public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup

variable {G : Type} [Group G]

theorem le_iSup_centralizer_hyperplanes [Finite G] {B Y : Subgroup G}
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hr : 2 ≤ pRank 2 ↥B) (hBY : B ≤ normalizer (Y : Set G))
    (hY : Odd (Nat.card ↥Y)) :
    Y ≤ ⨆ (E : Subgroup G) (_ : E ≤ B) (_ : pRank 2 ↥B - 1 ≤ pRank 2 ↥E),
      Y ⊓ centralizer (E : Set G) := by
  have hcard : Nat.card ↥B = 2 ^ pRank 2 ↥B :=
    CFSG.GH74.GLS.C3.Layer1.Back.card_eq_two_pow_pRank hB
  obtain ⟨hab, hsq⟩ := CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hElem : CFSG.Open.IsElemAbelian 2 B := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    rw [sq]
    exact hsq x hx
  have hlarge : 2 ^ (pRank 2 ↥B - 1 + 1) ≤ Nat.card ↥B := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcop : Nat.Coprime 2 (Nat.card ↥Y) := Nat.coprime_two_left.2 hY
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
    (pRank 2 ↥B - 1) Nat.prime_two B Y hElem hlarge hBY hcop
  refine le_of_eq_of_le hgen.symm ?_
  refine iSup_le fun S => iSup_le fun hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  have hSel : CFSG.IsElementaryAbelian 2 ↥S :=
    CFSG.GH74.GLS.C3.Layer1.Back.isElementaryAbelian_of_forall
      (fun u hu v hv => hab u (hSB hu) v (hSB hv)) (fun u hu => hsq u (hSB hu))
  have hrank : pRank 2 ↥S = pRank 2 ↥B - 1 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hScard
  exact le_iSup_of_le S (le_iSup_of_le hSB (le_iSup_of_le hrank.ge le_rfl))

end CFSG.GH74.Generic.BProg.B2
