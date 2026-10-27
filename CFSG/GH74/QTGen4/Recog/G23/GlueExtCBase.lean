
module

public import Certificates.Data.G23RecogGlueInputs
public import CFSG.GH74.QTGen4.Recog.G23.GlueExtB
public meta import CFSG.Certificates.CosetTablePresented
public meta import CFSG.GH74.QTGen4.Recog.G23.Words
public meta import CFSG.GH74.QTGen4.Recog.G23.GlueExtB
public import CFSG.GH74.QTGen4.Recog.G23.Words

@[expose] public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

theorem f5_rel : ∀ r ∈ {r : FreeGroup (Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) |
    r ∈ g23H5.map FreeGroup.mk}, FreeGroup.lift f5 r = 1 := by
  rintro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [FreeGroup.lift_mk]
  exact g23H5_rel w hw

def φ5 : PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5 →* Equiv.Perm (Fin 32) :=
  PresentedGroup.toGroup f5_rel

theorem φ5_of (i : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) :
    φ5 (PresentedGroup.of i) = f5 i :=
  PresentedGroup.toGroup.of f5_rel

theorem range_φ5 : φ5.range = Hc := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) | r ∈ g23H5.map FreeGroup.mk},
    MonoidHom.map_closure]
  unfold Hc
  congr 1
  have himg : φ5 '' Set.range PresentedGroup.of = Set.range f5 := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, φ5_of i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨PresentedGroup.of i, ⟨i, rfl⟩, φ5_of i⟩
  rw [himg, range_f5]

end CFSG.GH74.QTGen4.Recog.G23
