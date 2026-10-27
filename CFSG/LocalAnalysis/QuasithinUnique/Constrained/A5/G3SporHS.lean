module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.Sporadic.HS
public import Certificates.Certificate3167
public import Certificates.Certificate4102
public import Certificates.Certificate4140

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem noDelta5In_hs
    {X : Type} [Group X] [Finite X] (h : IsSporadic .HS X) : NoDelta5In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
    CFSG.Sporadic.HS.isSimpleGroup_HS
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 9 * 86625 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS.trans (by norm_num)
  exact noDelta5In_of_rows hX (by norm_num) hcard HS.hsMems (by decide +kernel)
    (fun T Y hT hTY => HS.hs_overgroups ⟨e⟩ hT hTY)

end CFSG.QuasithinUnique.A5.G3
