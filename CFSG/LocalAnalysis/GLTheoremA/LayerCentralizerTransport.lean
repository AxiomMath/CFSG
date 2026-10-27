module

public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem glaPLayer_centralizer_ne_bot_iff_of_mulEquiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {p : ℕ} (hp : p.Prime) (e : A ≃* B) (a : A) :
    GLAPLayer p (Subgroup.centralizer ({e a} : Set B)) ≠ ⊥ ↔
      GLAPLayer p (Subgroup.centralizer ({a} : Set A)) ≠ ⊥ := by
  have h := glaPLayer_map_eq_of_injective hp e.toMonoidHom e.injective
    (Subgroup.centralizer ({a} : Set A))
  rw [CFSG.Walter.map_centralizer_singleton_mulEquiv e a] at h
  constructor
  · intro hB hA
    exact hB (by rw [← h, hA, Subgroup.map_bot])
  · intro hA hB
    exact hA ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 (by rw [h, hB]))

theorem glaPLayer_centralizer_subtype_ne_bot_iff {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H : Subgroup G} (y : H) :
    GLAPLayer p (Subgroup.centralizer ({y} : Set H)) ≠ ⊥ ↔
      GLAPLayer p (H ⊓ Subgroup.centralizer ({(y : G)} : Set G)) ≠ ⊥ := by
  have h := glaPLayer_map_eq_of_injective hp H.subtype H.subtype_injective
    (Subgroup.centralizer ({y} : Set H))
  rw [CFSG.LocalAnalysis.GLTheoremA.H81.map_subtype_centralizer (G := G) (L := H) y] at h
  constructor
  · intro hH hinf
    exact hH ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 (by rw [h, hinf]))
  · intro hinf hH
    exact hinf (by rw [← h, hH, Subgroup.map_bot])

end CFSG.LocalAnalysis.GLTheoremA

end
