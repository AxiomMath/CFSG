module

public import Mathlib

public noncomputable section

namespace CFSG.Blueprint.NativeSporadic

theorem unit_seed_closure_eq_ofUnits {M : Type*} [Monoid M] [Finite M] (a b : Mˣ) :
    Submonoid.closure ({(a : M), (b : M)} : Set M) =
      (Subgroup.closure ({a, b} : Set Mˣ)).ofUnits := by
  rw [Subgroup.ofUnits, Subgroup.closure_toSubmonoid_of_finite,
    MonoidHom.map_mclosure]
  simp

@[expose] def unitSeedEquiv {M : Type*} [Monoid M] [Finite M] (a b : Mˣ) :
    (Submonoid.closure ({(a : M), (b : M)} : Set M))ˣ ≃*
      Subgroup.closure ({a, b} : Set Mˣ) :=
  (Submonoid.unitsEquivUnitsType _).symm.trans
    (MulEquiv.subgroupCongr (by
      rw [unit_seed_closure_eq_ofUnits, Subgroup.units_ofUnits_eq]))

theorem unitSeedEquiv_val {M : Type*} [Monoid M] [Finite M] (a b : Mˣ)
    (u : (Submonoid.closure ({(a : M), (b : M)} : Set M))ˣ) :
    ((unitSeedEquiv a b u : Mˣ) : M) = u.val.val := rfl

@[expose] def matrixSeedEquiv (p d : ℕ) [Fact p.Prime] (_hd : 1 ≤ d)
    (A B : Matrix (Fin d) (Fin d) (ZMod p)) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (Submonoid.closure ({A, B} : Set (Matrix (Fin d) (Fin d) (ZMod p))))ˣ ≃*
      Subgroup.closure
        ({Matrix.GeneralLinearGroup.mkOfDetNeZero A hA,
          Matrix.GeneralLinearGroup.mkOfDetNeZero B hB} :
            Set (Matrix.GeneralLinearGroup (Fin d) (ZMod p))) :=
  unitSeedEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero A hA)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero B hB)

theorem matrixSeedEquiv_val (p d : ℕ) [Fact p.Prime] (hd : 1 ≤ d)
    (A B : Matrix (Fin d) (Fin d) (ZMod p)) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (u : (Submonoid.closure ({A, B} : Set (Matrix (Fin d) (Fin d) (ZMod p))))ˣ) :
    ((matrixSeedEquiv p d hd A B hA hB u :
      Matrix.GeneralLinearGroup (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) =
        u.val.val := rfl

end CFSG.Blueprint.NativeSporadic
