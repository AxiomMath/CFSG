module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.LangFiniteSubfieldCongruence
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

@[expose, reducible] def Um (v : ℤ) : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, 1 - v], ![-1, -1, 1 - v, 1]]

@[expose, reducible] def Up (v : ℤ) : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, -v], ![-1, -1, -v, 1]]

@[expose, reducible] def Wm (w : ZMod 5) : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5 :=
  ![![-1, 0, 0, 1 - w], ![-1, -1, 1 - w, 1]]

@[expose, reducible] def Wp (w : ZMod 5) : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5 :=
  ![![-1, 0, 0, -w], ![-1, -1, -w, 1]]

@[expose] def uPZ (W : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5) (s : Fin 2)
    (α : Fin ReeTag.F4.tag.rank → ℤ) : ZMod 5 :=
  ∑ i, W s i * ((α i : ℤ) : ZMod 5)

@[expose] def kerZ (W : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5) (a b : ZMod 5) :
    Finset (Fin ReeTag.F4.tag.rank → ℤ) :=
  (rootFinset ReeTag.F4.tag).filter fun α => a * uPZ W 0 α + b * uPZ W 1 α = 0

@[expose] def KerOKZ (W : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5) : Prop :=
  ∀ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) →
    ((kerZ W a b).filter fun α => ReeTag.F4.quadForm α = 4).card = 4 ∧
    ((kerZ W a b).filter fun α => ReeTag.F4.quadForm α = 2).card = 4

@[expose] def CoverZ (W : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5) : Prop :=
  ∀ α ∈ rootFinset ReeTag.F4.tag, ∃ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) ∧ α ∈ kerZ W a b

instance (W : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5) : Decidable (KerOKZ W) := by
  unfold KerOKZ; infer_instance

instance (W : Fin 2 → Fin ReeTag.F4.tag.rank → ZMod 5) : Decidable (CoverZ W) := by
  unfold CoverZ; infer_instance

theorem kerOKZ_Wm : ∀ w : ZMod 5, 2 * w ^ 2 - 2 * w + 1 = 0 → KerOKZ (Wm w) := by
  decide +kernel

theorem kerOKZ_Wp : ∀ w : ZMod 5, 2 * w ^ 2 + 2 * w + 1 = 0 → KerOKZ (Wp w) := by
  decide +kernel

theorem coverZ_Wm : ∀ w : ZMod 5, 2 * w ^ 2 - 2 * w + 1 = 0 → CoverZ (Wm w) := by
  decide +kernel

theorem coverZ_Wp : ∀ w : ZMod 5, 2 * w ^ 2 + 2 * w + 1 = 0 → CoverZ (Wp w) := by
  decide +kernel

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux
