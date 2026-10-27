module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Certificates.Kernel.TcRes.PlaneSound
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem kset_of_frob
    {w : WeylGroup Tag.E6} {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = ε • (w • γ)) {r : ℕ} {s : ZMod 3}
    (hs : (ε : ZMod 3) * s = r) (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3))
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = (r : ZMod 3) * v j) :
    ∀ v ∈ P, v ∈ KSet w s := by
  intro v hv j
  have h := hfrob v hv j
  have hb : IsRoot Tag.E6 (Pi.single j 1) := IsRoot.basis (τ := Tag.E6) j
  rw [hρ _ hb] at h
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_assoc, ← Finset.mul_sum] at h
  have hεε : (ε : ZMod 3) * ε = 1 := by
    rcases hε with rfl | rfl <;> decide
  change ∑ m : Fin Tag.E6.rank, (((w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) m : ℤ) : ZMod 3) *
    v m = s * v j
  generalize ∑ m : Fin Tag.E6.rank, (((w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) m : ℤ) :
    ZMod 3) * v m = X at h ⊢
  linear_combination (ε : ZMod 3) * h - (ε : ZMod 3) * v j * hs - (X - s * v j) * hεε

end CFSG.KC.TcRes

end
