module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Sporadic.Ru
public import Certificates.Certificate3172
public import Certificates.Certificate4034
public import Certificates.Certificate4080
public import Certificates.Certificate4143

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem noDelta5In_ru
    {X : Type} [Group X] [Finite X] (h : IsSporadic .Ru X) : NoDelta5In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 14 * 8906625 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru.trans (by norm_num)
  exact noDelta5In_of_rows hX (by norm_num) hcard Ru.ruMems (by decide +kernel)
    (fun T Y hT hTY => Ru.ru_overgroups ⟨e⟩ hT hTY)

end CFSG.QuasithinUnique.A5.G3
