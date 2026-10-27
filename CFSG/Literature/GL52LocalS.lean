module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Literature.GL52Basic
public import CFSG.Sporadic.Schreier.Enumeration
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.Literature.GL52

open CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

theorem card_G_eq : Nat.card G = 9999360 := by rw [card_GL52]; norm_num

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

theorem orderOf_conj (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  MulEquiv.orderOf_eq (MulAut.conj g) x

end CFSG.Literature.GL52
