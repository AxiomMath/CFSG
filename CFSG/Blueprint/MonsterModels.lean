module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.Generated.Data
public import CFSG.Monster.Griess.AutFinite
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Blueprint.NativeSporadic

inductive MonsterModel where
  | gmat
  | griess
  | y443Derived
  | tauCeti
  deriving DecidableEq

@[expose] def MonsterModel.Carrier : MonsterModel → Type
  | .gmat => CFSG.Monster.Generated.Gmat
  | .griess => CFSG.Monster.Griess.AutO
  | .y443Derived => M
  | .tauCeti => TauCeti.SporadicName.M.Group

noncomputable instance MonsterModel.carrierGroup (m : MonsterModel) : Group m.Carrier := by
  cases m <;> dsimp [MonsterModel.Carrier] <;> infer_instance

@[expose] def selectCarrier (m : MonsterModel) : TauCeti.SporadicName → Type
  | .M => m.Carrier
  | s => Carrier s

noncomputable instance selectCarrierGroup (m : MonsterModel) (s : TauCeti.SporadicName) :
    Group (selectCarrier m s) := by
  cases s <;> dsimp [selectCarrier] <;> infer_instance

theorem selectCarrier_M (m : MonsterModel) : selectCarrier m .M = m.Carrier :=
  rfl

theorem selectCarrier_of_ne_M (m : MonsterModel) {s : TauCeti.SporadicName} (hs : s ≠ .M) :
    selectCarrier m s = Carrier s := by
  cases s <;> first | rfl | exact absurd rfl hs

theorem carrier_eq_selectCarrier : Carrier = selectCarrier .y443Derived := by
  funext s
  cases s <;> rfl

theorem carrier_M_eq_y443Derived : Carrier .M = MonsterModel.y443Derived.Carrier :=
  rfl

end CFSG.Blueprint.NativeSporadic
