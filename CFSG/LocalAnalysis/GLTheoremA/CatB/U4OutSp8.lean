module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsSp
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem u4Out_index_sp8two {P : Type} [Group P] [Finite P] (h : catalogIs P S9.isSp8two) :
    (innerAut P).index = 1 ∨ (innerAut P).index = 2 := by
  haveI : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) DFunLike.coe_injective
  obtain ⟨e1⟩ := KFacts.bridge_sp8two h
  obtain ⟨e2⟩ := KFacts.nonempty_sp82_equiv
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  have hK : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, hF]
  have hle1 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_outer_statedSp_le (r := 4)
    (K := GaloisField 2 1) (by norm_num) hK
  have hle2 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_ringEquiv_le (GaloisField 2 1)
  have hO : Nat.card (MulAut P ⧸ innerAut P) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (StatedProj (StatedSp 4 (GaloisField 2 1)))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e1.trans (e2.trans (CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 4 (GaloisField 2 1))))).toEquiv
  have hpos : 0 < Nat.card (MulAut P ⧸ innerAut P) := Nat.card_pos
  change Nat.card (MulAut P ⧸ innerAut P) = 1 ∨ Nat.card (MulAut P ⧸ innerAut P) = 2
  omega

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
