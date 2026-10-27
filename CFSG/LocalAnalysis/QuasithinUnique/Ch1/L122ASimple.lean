module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.Models

public section

namespace CFSG.QuasithinUnique.Vol2Native.L122A

open CFSG.Quasithin

theorem isSimpleGroup_of_a38Types
    {X : Type} [Group X] (hX : A38Types X) : IsSimpleGroup X := by
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hn⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n hn).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n hn).2
  · obtain ⟨e⟩ := hJ
    have := CFSG.Walter.J1Props.J1_simple
    exact (e.trans CFSG.Walter.walterJ1EquivNative.symm).isSimpleGroup
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 hn).2

end CFSG.QuasithinUnique.Vol2Native.L122A
