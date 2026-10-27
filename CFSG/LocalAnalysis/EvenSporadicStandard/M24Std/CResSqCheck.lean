module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6InvCheck

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def Sym6SqData : Prop :=
  ∀ p ∈ sym6T, p.2 * p.2 = 1 → ∀ k ∈ sxK0, k * p.1 * (k * p.1) ∈ m24E1l →
    k * p.1 ∉ m24E1l →
      (m24E1l.filter fun x => decide (k * p.1 * x * (k * p.1)⁻¹ = x)).length =
        if Equiv.Perm.sign p.2 = 1 then 16 else 8

instance : Decidable Sym6SqData := by
  unfold Sym6SqData
  infer_instance

end CFSG.EvenSporadicStandard.M24Std.Sym6
