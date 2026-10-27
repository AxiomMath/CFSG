module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

@[expose] def KD264Y1KerD4Model : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), StatedClassicalModel G .POmegaMinus 4 p f →
    ¬ p = 3 → ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 →
      CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E

@[expose] def KD264Y1TwistedD4Model : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), d.1 = .twistedD 4 q →
    StatedClassicalModel (CFSGIndex.lie d).Group .POmegaMinus 4 q.p q.exponent

theorem KD264Y1KerD4_of_model (hm : KD264Y1KerD4Model) (hi : KD264Y1TwistedD4Model) :
    KD264Y1KerD4 := by
  unfold KD264Y1KerD4 KD264Y1Kernel
  intro d hfin hns _hk2 _hk3 hP E hE hc
  obtain ⟨q, hq⟩ := hP
  have hp3 : q.p ≠ 3 := by
    intro h
    apply hns
    refine Or.inl ⟨CFSGIndex.lie d, ?_, ⟨MulEquiv.refl _⟩⟩
    show LieTypeIndex.characteristic d.1 = 3
    rw [hq, LieTypeIndex.characteristic_twistedD]
    exact h
  exact hm _ q.p q.exponent (hi d q hq) hp3 E hE hc

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
