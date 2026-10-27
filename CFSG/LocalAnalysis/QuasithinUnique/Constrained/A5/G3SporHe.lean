module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Sporadic.He.Simple
public import Certificates.Certificate3168
public import Certificates.Certificate4033
public import Certificates.Certificate4141

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem noDelta5In_he
    {X : Type} [Group X] [Finite X] (h : IsSporadic .He X) : NoDelta5In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He.trans (by norm_num)
  exact noDelta5In_of_rows hX (by norm_num) hcard He.heMems (by decide +kernel)
    (fun T Y hT hTY => He.he_overgroups ⟨e⟩ hT hTY)

end CFSG.QuasithinUnique.A5.G3
