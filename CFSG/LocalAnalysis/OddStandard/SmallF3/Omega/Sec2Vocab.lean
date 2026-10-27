module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProjLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def SimInGStar (x : ProjSim Q) : Prop :=
  ∃ y : ProjOrth Q, projOrthToProjSim Q y = x

@[expose] def SimHasType (x : ProjSim Q) (r : ℕ) (α : ℤˣ) : Prop :=
  ∃ y : ProjOrth Q, projOrthToProjSim Q y = x ∧ HasType y r α

@[expose] def SimIsProjective (x : ProjSim Q) : Prop :=
  ∃ y : ProjOrth Q, projOrthToProjSim Q y = x ∧ IsProjective y

@[expose] def SimInOmegaStar (hQ : Q.Nondegenerate) (x : ProjSim Q) : Prop :=
  ∃ y ∈ omegaProj hQ, projOrthToProjSim Q y = x

theorem SimHasType.simInGStar {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (h : SimHasType x r α) :
    SimInGStar x :=
  let ⟨y, hy, _⟩ := h
  ⟨y, hy⟩

theorem SimInOmegaStar.simInGStar {hQ : Q.Nondegenerate} {x : ProjSim Q}
    (h : SimInOmegaStar hQ x) : SimInGStar x :=
  let ⟨y, _, hy⟩ := h
  ⟨y, hy⟩

theorem simHasType_projOrthToProjSim {y : ProjOrth Q} {r : ℕ} {α : ℤˣ} (h : HasType y r α) :
    SimHasType (projOrthToProjSim Q y) r α :=
  ⟨y, rfl, h⟩

variable {G : Type} [Group G]

@[expose] def InducesViaP (L : Subgroup G) (N : Subgroup ↥L) [N.Normal] (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ N ≃* omegaProj hQ) (s : G) (x : ProjSim Q) : Prop :=
  s ∈ Subgroup.normalizer (L : Set G) ∧
    ∀ l l' : ↥L, (l' : G) = s * l * s⁻¹ →
      ((e (QuotientGroup.mk l') : omegaProj hQ) : ProjOrth Q) =
        projSimAct Q x ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q)

@[expose] def InducesTypeSome (L : Subgroup G) (s : G) (n : ℕ) (ε : ℤˣ) (r : ℕ) (α : ℤˣ) :
    Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x : ProjSim Q),
    Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧
      InducesViaP L (Subgroup.center ↥L) hQ e s x ∧ SimHasType x r α

end CFSG.OddStandard.SmallF3.Omega
