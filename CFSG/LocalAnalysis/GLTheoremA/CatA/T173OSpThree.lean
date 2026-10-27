module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
  CFSG.LocalAnalysis.GLTheoremA.T173X CFSG.LocalAnalysis.GLTheoremA.T173O
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary
open Polynomial Module
open scoped commutatorElement

theorem modelFactSpThree : ∀ (F : Type) [Field F] [Finite F] (ℓ : ℕ), 3 ≤ ℓ → Nat.card F = 2 → ModelFactO 3 ↥(StatedSp ℓ F) := by
  intro F instField instFinite ℓ hℓ hF
  haveI : Finite ↥(StatedSp ℓ F) := Subtype.finite
  intro A d hA hd
  have hℓ1 : 1 ≤ ℓ := by omega
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hd1 : d ≠ 1 := hd.2.1
  rcases stdLayer_eq_or hF hℓ1 hd3 hd1 hd.2.2.2.1 with hK | hK
  · rcases stdOutcome_fixed hF hℓ hA hd hK with hv | he
    · exact Or.inl hv
    · have hQ : CFSG.Open.IsQuasisimple ↥⁅spSupported d ({X - 1} : Set F[X]),
          spSupported d ({X - 1} : Set F[X])⁆ := by
        have h : CFSG.Open.IsQuasisimple ↥(stdLayer d) := hd.2.2.2.1.2.2
        rwa [hK] at h
      obtain ⟨T, hT1, hT2, hTK⟩ := exists_two_subgroup_le_stdLayer_fixed hF hd3 hd1 hQ
      exact Or.inr (stdExtendsN_of_stdExtends he ⟨T, hT1, hT2, hK.symm ▸ hTK⟩)
  · exact stdOutcome_unitary hF hℓ hA hd hK

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
