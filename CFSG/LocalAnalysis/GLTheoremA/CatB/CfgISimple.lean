module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem sporadic_isSimple_of_ne_M
    (s : TauCeti.SporadicName) (hs : s ≠ .M) : IsSimpleGroup s.Group :=
  by
  obtain ⟨-, hsimp⟩ := CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M s hs
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact (MulEquiv.isSimpleGroup_congr e).1 hsimp

theorem lie_isSimple_of_index
    (i : TauCeti.ValidLieTypeIndex) : IsSimpleGroup i.Group :=
  (CFSG.Assembly.lie_finite_simple i).2

theorem onLie_isSimple
    (P : TauCeti.LieTypeIndex → Prop) (i : TauCeti.CFSGIndex) (h : onLie P i) :
    IsSimpleGroup i.Group :=
  by
  cases i with
  | cyclic p hp => exact False.elim h
  | alternating n hn => exact False.elim h
  | lie idx => exact lie_isSimple_of_index idx
  | sporadic s => exact False.elim h

theorem sporIs_isSimple
    (s : TauCeti.SporadicName) (hs : s ≠ .M) (i : TauCeti.CFSGIndex) (h : sporIs s i) :
    IsSimpleGroup i.Group :=
  by
  subst h
  exact sporadic_isSimple_of_ne_M s hs

theorem isU4of_isSimple
    {r : ℕ} {i : TauCeti.CFSGIndex} (h : isU4of r i) : IsSimpleGroup i.Group :=
  onLie_isSimple _ i h

theorem isD4of_isSimple
    {r : ℕ} {i : TauCeti.CFSGIndex} (h : isD4of r i) : IsSimpleGroup i.Group :=
  onLie_isSimple _ i h

theorem isG2of_isSimple
    {r : ℕ} {i : TauCeti.CFSGIndex} (h : isG2of r i) : IsSimpleGroup i.Group :=
  onLie_isSimple _ i h

theorem Iq_isSimple
    (row : S8.Row) (i : TauCeti.CFSGIndex) (h : row.Iq i) : IsSimpleGroup i.Group :=
  by
  cases row with
  | ly => exact sporIs_isSimple .McL (by decide) i h
  | co2 =>
    rcases h with h | h
    · exact isU4of_isSimple h
    · exact onLie_isSimple _ i h
  | co1 => exact sporIs_isSimple .Suz (by decide) i h
  | fi24 => exact isD4of_isSimple h
  | fi24h => exact isD4of_isSimple h
  | suz => exact isU4of_isSimple h
  | suzh => exact isU4of_isSimple h
  | th => exact isG2of_isSimple h
  | m3 => exact sporIs_isSimple .Fi24Prime (by decide) i h
  | m5 => exact sporIs_isSimple .HN (by decide) i h

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
