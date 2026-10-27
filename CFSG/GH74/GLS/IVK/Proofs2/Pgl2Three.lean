module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import Mathlib.FieldTheory.Finite.GaloisField

public section

open CFSG CFSG.GorensteinWalter

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem exists_pgl2_equiv_perm {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) :
    Nonempty (PGL2 F ≃* Equiv.Perm (Fin 4)) := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
  exact ⟨(pgl2RingEquiv (FiniteField.ringEquivOfCardEq hc)).trans pgl2_three_equiv_perm⟩

end CFSG.GH74.GLS.IVK.Proofs2
