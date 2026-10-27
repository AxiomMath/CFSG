module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate3017
public import Certificates.Certificate4068
public import Certificates.Certificate4075

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem noDelta5In_m24
    {X : Type} [Group X] [Finite X] (h : IsSporadic .M24 X) : NoDelta5In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 10 * 239085 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24.trans (by norm_num)
  exact noDelta5In_of_rows hX (by norm_num) hcard M24.m24Mems (by decide +kernel)
    (fun T Y hT hTY => M24.m24_overgroups ⟨e⟩ hT hTY)

end CFSG.QuasithinUnique.A5.G3
