module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen3
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem typeHyp3_suz_of_facts (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hSimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Suz).Group) :
    BMType.TypeHyp3 (S8.sporIs .Suz) 448345497600 where
  card T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    obtain rfl : i = .sporadic .Suz := hi
    rw [Nat.card_congr e.toEquiv]
    exact hOrd .Suz
  aut T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    obtain rfl : i = .sporadic .Suz := hi
    haveI : IsSimpleGroup T := (MulEquiv.isSimpleGroup_congr e).2 hSimple
    have hcard : Nat.card T = 448345497600 := (Nat.card_congr e.toEquiv).trans (hOrd .Suz)
    have hnab : ∃ a b : T, a * b ≠ b * a :=
      exists_noncomm_of_simple_card hcard (by norm_num)
    have hle : Nat.card (Outer T) ≤ 2 := hOut T inferInstance hnab .Suz ⟨e⟩
    haveI : Finite (MulAut T) :=
      Finite.of_injective (fun f : MulAut T => (f : T → T)) (fun f g h => DFunLike.coe_injective h)
    haveI : Finite (Outer T) := Finite.of_surjective _ QuotientGroup.mk_surjective
    have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
    obtain h1 | h2 : Nat.card (Outer T) = 1 ∨ Nat.card (Outer T) = 2 := by omega
    · rw [h1]
      norm_num
    · rw [h2]
      norm_num
  big := by norm_num
  nine := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
