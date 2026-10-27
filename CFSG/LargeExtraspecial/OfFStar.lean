module

public import CFSG.LargeExtraspecial.Setting
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Adapters.GeneralizedFitting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open

theorem timmesfeldFStar_normal (H : Type*) [Group H] : (timmesfeldFStar H).Normal := by
  have h1 : (timmesfeldFitting H).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  have h2 : (timmesfeldLayer H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hle : (timmesfeldLayer H).map (MulAut.conj g).toMonoidHom ≤ timmesfeldLayer H := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun L hL => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup
        ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL)
    exact hle ⟨x, hx, rfl⟩
  exact Subgroup.sup_normal _ _

theorem isExtraspecialPGroup_of_timmesfeld {P : Type*} [Group P]
    (h : timmesfeldIsExtraspecial P) : IsExtraspecialPGroup 2 P :=
  ⟨h.1, h.2.1.trans h.2.2.1, h.2.2.1, h.2.2.2⟩

@[expose] noncomputable def Setting.ofFStar {G : Type} [Group G] [Finite G] (z : G)
    (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({z} : Set G)))) :
    Setting G where
  z := z
  orderOf_z := hz
  Q := timmesfeldFStar (centralizer ({z} : Set G))
  normal := timmesfeldFStar_normal _
  extraspecial := isExtraspecialPGroup_of_timmesfeld hext
  centralizer_le := CFSG.Adapters.generalized_fitting_self_centralizing _
  le_of_normal := fun P hP h2 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact le_sup_of_le_left (le_sSup ⟨hP, h2.isNilpotent⟩)

@[simp] theorem Setting.ofFStar_z {G : Type} [Group G] [Finite G] (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({z} : Set G)))) :
    (Setting.ofFStar z hz hext).z = z := rfl

@[simp] theorem Setting.ofFStar_Q {G : Type} [Group G] [Finite G] (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({z} : Set G)))) :
    (Setting.ofFStar z hz hext).Q = timmesfeldFStar (centralizer ({z} : Set G)) := rfl

end CFSG.LargeExtraspecial
