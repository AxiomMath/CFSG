module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

@[expose] def AutL34NoQ16Q16 : Prop :=
  ∀ (F : Type) [Group F], LieModel F .PSL 3 2 2 → NoQ16Q16 (MulAut F)

@[expose] def AutM22NoQ16Q16 : Prop :=
  ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .M22 → NoQ16Q16 (MulAut F)

@[expose] def AutJ2NoQ16Q16 : Prop :=
  ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .J2 → NoQ16Q16 (MulAut F)

@[expose] def AutJ3NoQ16Q16 : Prop :=
  ∀ (F : Type) [Group F], NativeSporadic.IsSporadic F .J3 → NoQ16Q16 (MulAut F)

@[expose] def LocalL43 : Prop := LocalNoQ16Q16 fun F _ => LieModel F .PSL 4 3 1

@[expose] def LocalU43 : Prop := LocalNoQ16Q16 fun F _ => LieModel F .PSU 4 3 1

@[expose] def LocalL53 : Prop := LocalNoQ16Q16 fun F _ => LieModel F .PSL 5 3 1

theorem twinLeafR_or {r n : ℕ} {P Q : ∀ (F : Type) [Group F], Prop} (hP : TwinLeafR r n P)
    (hQ : TwinLeafR r n Q) : TwinLeafR r n fun F _ => P F ∨ Q F :=
  fun Y _ _ R S t hPH hsmall hF =>
    hF.elim (hP Y R S t hPH hsmall) (hQ Y R S t hPH hsmall)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
