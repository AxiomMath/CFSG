module

public import CFSG.Assembly.Reduction

public section

namespace CFSG.Assembly

@[expose] def CatalogImp (C D : GroupProp) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) → C X → D X

@[expose] def CatalogAgreeOn (C D : GroupProp) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    (C X ↔ D X)

variable {C D : GroupProp}

namespace CatalogAgreeOn

theorem imp (h : CatalogAgreeOn C D) : CatalogImp C D :=
  fun X _ _ _ hn => (h X hn).1

theorem symm (h : CatalogAgreeOn C D) : CatalogAgreeOn D C :=
  fun X _ _ _ hn => (h X hn).symm

theorem rev (h : CatalogAgreeOn C D) : CatalogImp D C :=
  h.symm.imp

end CatalogAgreeOn

theorem KProper.of_catalogImp (h : CatalogImp C D) {G : Type} [Group G] [Finite G]
    (hK : KProper C G) : KProper D G :=
  KCore.KProperNonab.mono_of_finite h hK

theorem KProper.of_catalogAgree (h : CatalogAgreeOn C D) {G : Type} [Group G] [Finite G]
    (hK : KProper C G) : KProper D G :=
  hK.of_catalogImp h.imp

theorem kProper_iff_of_catalogAgree (h : CatalogAgreeOn C D) {G : Type} [Group G] [Finite G] :
    KProper C G ↔ KProper D G :=
  ⟨KProper.of_catalogAgree h, KProper.of_catalogAgree h.symm⟩

theorem kGroupAllSimple_of_kGroupNonab_of_catalogImp (h : CatalogImp C D)
    (hD : KCore.IsoInvariant D) (hab : KCore.ContainsAbelianSimple D) {X : Type} [Group X]
    [Finite X] (hX : KCore.KGroupNonab C X) : KCore.KGroupAllSimple D X :=
  KCore.KGroupNonab.kGroupAllSimple hD hab (KCore.KGroupNonab.mono_of_finite h hX)

theorem kProper_of_kGroupAllSimple_of_catalogImp (h : CatalogImp C D) {X : Type} [Group X]
    [Finite X] (hX : KCore.KGroupAllSimple C X) : KProper D X :=
  KProper.of_catalogImp h (KCore.KGroupNonab.kProperNonab (KCore.KGroupAllSimple.kGroupNonab hX))

end CFSG.Assembly
