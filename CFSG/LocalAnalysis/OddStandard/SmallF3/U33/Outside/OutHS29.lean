module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHVI218N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29Nonab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutSigma3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

theorem HS29 {T : Type} [Group T] [Finite T] (hcard : Nat.card T = 64)
    (hnab : ∃ a b : T, a * b ≠ b * a) {ρ x : MulAut T} (hs : Sigma3Rel ρ x)
    (hfpf : ∀ g : T, ρ g = g → g = 1) :
    Nonempty (T ≃* SylSL3_4) ∧
      (Nonempty (↥(fixSub x) ≃* DihedralGroup 4) ∨
        Nonempty (↥(fixSub x) ≃* QuaternionGroup 2)) := by
  have hS : FpfNonab T ρ := ⟨hcard, hnab, hs.cube, hfpf⟩
  have hspec : FpfSpecial T := hS.special
  have hfix8 : Nat.card ↥(fixSub x) = 8 :=
    card_fixSub hspec hs.cube hfpf hs.mul_self hs.conj
  have hfixnab : ∃ a b : ↥(fixSub x), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      fixSub_nonabelian hspec hs.cube hfpf hs.mul_self hs.conj
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hc => hab (congrArg Subtype.val hc)⟩
  refine ⟨?_, order8_nonabelian hfix8 hfixnab⟩
  rcases hS.classify with he | he
  · exact he
  · obtain ⟨e⟩ := he
    exact False.elim (no_sigma3_sylSU e hs)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
