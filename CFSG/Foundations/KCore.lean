module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

public section

universe u v

namespace CFSG.KCore

abbrev Catalogue : Type (u + 1) := ∀ (G : Type u) [Group G], Prop

variable (C : Catalogue.{u})

abbrev IsoInvariant : Prop := ∀ {X Y : Type u} [Group X] [Group Y], X ≃* Y → C Y → C X

abbrev ContainsAbelianSimple : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], (∀ a b : S, a * b = b * a) → C S

abbrev IsoTransfer (D : Catalogue.{v}) : Prop :=
  ∀ {X : Type u} {Y : Type v} [Group X] [Group Y], X ≃* Y → C X → D Y

abbrev KGroupAllSimple (X : Type u) [Group X] : Prop :=
  ∀ (H : Subgroup X) (N : Subgroup H) [N.Normal], IsSimpleGroup (H ⧸ N) → C (H ⧸ N)

abbrev KGroupNonab (X : Type u) [Group X] : Prop :=
  ∀ (K L : Subgroup X), L ≤ K → ∀ [(L.subgroupOf K).Normal],
    IsSimpleGroup (K ⧸ L.subgroupOf K) → (∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) →
    C (K ⧸ L.subgroupOf K)

abbrev KProperAllSimple (G : Type u) [Group G] : Prop :=
  ∀ H : Subgroup G, H ≠ ⊤ → KGroupAllSimple C H

abbrev KProperNonab (G : Type u) [Group G] : Prop :=
  ∀ (K L : Subgroup G), K ≠ ⊤ → L ≤ K → ∀ [(L.subgroupOf K).Normal],
    IsSimpleGroup (K ⧸ L.subgroupOf K) → (∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) →
    C (K ⧸ L.subgroupOf K)

abbrev SQTKOver (SQT : Catalogue.{u}) (X : Type u) [Group X] : Prop :=
  SQT X ∧ KGroupAllSimple C X

variable {C}

theorem nonabelian_of_mulEquiv {A S : Type*} [Group A] [Group S] (e : A ≃* S)
    (h : ∃ a b : S, a * b ≠ b * a) : ∃ a b : A, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hc

theorem map_subtype_ne_top {G : Type*} [Group G] {H : Subgroup G} (hH : H ≠ ⊤)
    (K : Subgroup H) : K.map H.subtype ≠ ⊤ := fun htop =>
  hH (top_unique (htop ▸ Subgroup.map_subtype_le K))

theorem map_ne_top_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {K : Subgroup G} (hK : K ≠ ⊤) : K.map f ≠ ⊤ := fun htop => hK <| by
  rw [← Subgroup.comap_map_eq_self_of_injective hf K, htop, Subgroup.comap_top]

theorem comap_ne_top_of_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) {K : Subgroup H} (hK : K ≠ ⊤) : K.comap f ≠ ⊤ := fun htop =>
  hK <| by rw [← Subgroup.map_comap_eq_self_of_surjective hf K, htop,
    Subgroup.map_top_of_surjective f hf]

theorem IsoInvariant.isoTransfer (hC : IsoInvariant C) : IsoTransfer C C := fun e h => hC e.symm h

section AllSimple

variable {X Y : Type u} [Group X] [Group Y]

theorem KGroupAllSimple.catalogue_of_surjective_transfer {D : Catalogue.{v}}
    (hT : IsoTransfer C D) (hX : KGroupAllSimple C X) (K : Subgroup X) {S : Type v} [Group S]
    [IsSimpleGroup S] (φ : K →* S) (hφ : Function.Surjective φ) : D S := by
  let e : (K ⧸ φ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (K ⧸ φ.ker) := e.isSimpleGroup
  exact hT e (hX K φ.ker this)

theorem KGroupAllSimple.catalogue_of_surjective (hC : IsoInvariant C) (hX : KGroupAllSimple C X)
    (K : Subgroup X) {S : Type u} [Group S] [IsSimpleGroup S] (φ : K →* S)
    (hφ : Function.Surjective φ) : C S :=
  hX.catalogue_of_surjective_transfer hC.isoTransfer K φ hφ

theorem KGroupAllSimple.of_injective (hC : IsoInvariant C) (hY : KGroupAllSimple C Y)
    (f : X →* Y) (hf : Function.Injective f) : KGroupAllSimple C X := by
  intro K N _ _
  let e : K ≃* K.map f := K.equivMapOfInjective f hf
  exact hY.catalogue_of_surjective hC (K.map f) ((QuotientGroup.mk' N).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective N).comp e.symm.surjective)

theorem KGroupAllSimple.subgroup (hC : IsoInvariant C) (hX : KGroupAllSimple C X)
    (H : Subgroup X) : KGroupAllSimple C H :=
  hX.of_injective hC H.subtype H.subtype_injective

theorem KGroupAllSimple.of_mulEquiv (hC : IsoInvariant C) (hY : KGroupAllSimple C Y)
    (e : X ≃* Y) : KGroupAllSimple C X :=
  hY.of_injective hC e.toMonoidHom e.injective

theorem kGroupAllSimple_congr (hC : IsoInvariant C) (e : X ≃* Y) :
    KGroupAllSimple C X ↔ KGroupAllSimple C Y :=
  ⟨fun h => h.of_mulEquiv hC e.symm, fun h => h.of_mulEquiv hC e⟩

theorem KGroupAllSimple.of_surjective (hC : IsoInvariant C) (hX : KGroupAllSimple C X)
    (f : X →* Y) (hf : Function.Surjective f) : KGroupAllSimple C Y := by
  intro K N _ _
  exact hX.catalogue_of_surjective hC (K.comap f) ((QuotientGroup.mk' N).comp (f.subgroupComap K))
    ((QuotientGroup.mk'_surjective N).comp (f.subgroupComap_surjective K hf))

theorem KGroupAllSimple.quotient (hC : IsoInvariant C) (hX : KGroupAllSimple C X)
    (M : Subgroup X) [M.Normal] : KGroupAllSimple C (X ⧸ M) :=
  hX.of_surjective hC (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)

theorem KGroupAllSimple.section (hC : IsoInvariant C) (hX : KGroupAllSimple C X)
    (H : Subgroup X) (N : Subgroup H) [N.Normal] : KGroupAllSimple C (H ⧸ N) :=
  (hX.subgroup hC H).quotient hC N

theorem KGroupAllSimple.catalogue_self (hC : IsoInvariant C) (hX : KGroupAllSimple C X)
    [IsSimpleGroup X] : C X :=
  hX.catalogue_of_surjective hC ⊤ (Subgroup.topEquiv (G := X)).toMonoidHom
    (Subgroup.topEquiv (G := X)).surjective

theorem KGroupAllSimple.kProperAllSimple (hC : IsoInvariant C) (hX : KGroupAllSimple C X) :
    KProperAllSimple C X :=
  fun H _ => hX.subgroup hC H

theorem KProperAllSimple.catalogue_of_surjective (hC : IsoInvariant C)
    (hX : KProperAllSimple C X) (K : Subgroup X) (hK : K ≠ ⊤) {S : Type u} [Group S]
    [IsSimpleGroup S] (φ : K →* S) (hφ : Function.Surjective φ) : C S :=
  (hX K hK).catalogue_of_surjective hC ⊤ (φ.comp (Subgroup.topEquiv (G := K)).toMonoidHom)
    (hφ.comp (Subgroup.topEquiv (G := K)).surjective)

theorem KProperAllSimple.of_injective (hC : IsoInvariant C) (hY : KProperAllSimple C Y)
    (f : X →* Y) (hf : Function.Injective f) : KProperAllSimple C X := fun H hH =>
  (hY _ (map_ne_top_of_injective hf hH)).of_mulEquiv hC (H.equivMapOfInjective f hf)

theorem KProperAllSimple.of_surjective (hC : IsoInvariant C) (hX : KProperAllSimple C X)
    (f : X →* Y) (hf : Function.Surjective f) : KProperAllSimple C Y := fun H hH =>
  (hX _ (comap_ne_top_of_surjective hf hH)).of_surjective hC (f.subgroupComap H)
    (f.subgroupComap_surjective H hf)

theorem KProperAllSimple.of_mulEquiv (hC : IsoInvariant C) (hY : KProperAllSimple C Y)
    (e : X ≃* Y) : KProperAllSimple C X :=
  hY.of_injective hC e.toMonoidHom e.injective

theorem kProperAllSimple_congr (hC : IsoInvariant C) (e : X ≃* Y) :
    KProperAllSimple C X ↔ KProperAllSimple C Y :=
  ⟨fun h => h.of_mulEquiv hC e.symm, fun h => h.of_mulEquiv hC e⟩

end AllSimple

section Nonab

variable {X Y : Type u} [Group X] [Group Y]

theorem KGroupNonab.catalogue_of_surjective_transfer {D : Catalogue.{v}} (hT : IsoTransfer C D)
    (hX : KGroupNonab C X) (K : Subgroup X) {S : Type v} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S) (hφ : Function.Surjective φ) : D S := by
  let L : Subgroup X := φ.ker.map K.subtype
  have hL : L.subgroupOf K = φ.ker := by
    ext k
    exact Subgroup.mem_map_iff_mem K.subtype_injective
  have : (L.subgroupOf K).Normal := by rw [hL]; infer_instance
  let e : (K ⧸ L.subgroupOf K) ≃* S := QuotientGroup.liftEquiv (L.subgroupOf K) hφ hL
  have : IsSimpleGroup (K ⧸ L.subgroupOf K) := e.isSimpleGroup
  exact hT e (hX K L (Subgroup.map_subtype_le _) this (nonabelian_of_mulEquiv e hnonab))

theorem KGroupNonab.catalogue_of_surjective (hC : IsoInvariant C) (hX : KGroupNonab C X)
    (K : Subgroup X) {S : Type u} [Group S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (φ : K →* S) (hφ : Function.Surjective φ) : C S :=
  hX.catalogue_of_surjective_transfer hC.isoTransfer K hnonab φ hφ

theorem KProperNonab.catalogue_of_surjective_transfer {D : Catalogue.{v}} (hT : IsoTransfer C D)
    (hX : KProperNonab C X) (K : Subgroup X) (hK : K ≠ ⊤) {S : Type v} [Group S]
    [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : D S := by
  let L : Subgroup X := φ.ker.map K.subtype
  have hL : L.subgroupOf K = φ.ker := by
    ext k
    exact Subgroup.mem_map_iff_mem K.subtype_injective
  have : (L.subgroupOf K).Normal := by rw [hL]; infer_instance
  let e : (K ⧸ L.subgroupOf K) ≃* S := QuotientGroup.liftEquiv (L.subgroupOf K) hφ hL
  have : IsSimpleGroup (K ⧸ L.subgroupOf K) := e.isSimpleGroup
  exact hT e (hX K L hK (Subgroup.map_subtype_le _) this (nonabelian_of_mulEquiv e hnonab))

theorem KProperNonab.catalogue_of_surjective (hC : IsoInvariant C) (hX : KProperNonab C X)
    (K : Subgroup X) (hK : K ≠ ⊤) {S : Type u} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S) (hφ : Function.Surjective φ) : C S :=
  hX.catalogue_of_surjective_transfer hC.isoTransfer K hK hnonab φ hφ

theorem KGroupNonab.catalogue_self (hC : IsoInvariant C) (hX : KGroupNonab C X)
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) : C X :=
  hX.catalogue_of_surjective hC ⊤ hnonab (Subgroup.topEquiv (G := X)).toMonoidHom
    (Subgroup.topEquiv (G := X)).surjective

theorem KGroupNonab.kProperNonab (hX : KGroupNonab C X) : KProperNonab C X := by
  intro K L _ hLK _ hs hn
  exact hX K L hLK hs hn

theorem KGroupNonab.of_injective (hC : IsoInvariant C) (hY : KGroupNonab C Y) (f : X →* Y)
    (hf : Function.Injective f) : KGroupNonab C X := by
  intro K L _ _ _ hn
  let e : K ≃* K.map f := K.equivMapOfInjective f hf
  exact hY.catalogue_of_surjective hC (K.map f) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)

theorem KGroupNonab.subgroup (hC : IsoInvariant C) (hX : KGroupNonab C X) (H : Subgroup X) :
    KGroupNonab C H :=
  hX.of_injective hC H.subtype H.subtype_injective

theorem KGroupNonab.of_mulEquiv (hC : IsoInvariant C) (hY : KGroupNonab C Y) (e : X ≃* Y) :
    KGroupNonab C X :=
  hY.of_injective hC e.toMonoidHom e.injective

theorem KGroupNonab.of_surjective_transfer {D : Catalogue.{v}} (hT : IsoTransfer C D)
    (hX : KGroupNonab C X) {Z : Type v} [Group Z] (f : X →* Z) (hf : Function.Surjective f) :
    KGroupNonab D Z := by
  intro K L _ _ _ hn
  exact hX.catalogue_of_surjective_transfer hT (K.comap f) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp (f.subgroupComap K))
    ((QuotientGroup.mk'_surjective _).comp (f.subgroupComap_surjective K hf))

theorem KGroupNonab.of_surjective (hC : IsoInvariant C) (hX : KGroupNonab C X) (f : X →* Y)
    (hf : Function.Surjective f) : KGroupNonab C Y :=
  hX.of_surjective_transfer hC.isoTransfer f hf

theorem KGroupNonab.quotient (hC : IsoInvariant C) (hX : KGroupNonab C X) (M : Subgroup X)
    [M.Normal] : KGroupNonab C (X ⧸ M) :=
  hX.of_surjective hC (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)

theorem KProperNonab.kGroupNonab (hC : IsoInvariant C) (hX : KProperNonab C X) (H : Subgroup X)
    (hH : H ≠ ⊤) : KGroupNonab C H := by
  intro K L _ _ _ hn
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  exact hX.catalogue_of_surjective hC (K.map H.subtype) (map_subtype_ne_top hH K) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)

theorem KProperNonab.of_injective (hC : IsoInvariant C) (hY : KProperNonab C Y) (f : X →* Y)
    (hf : Function.Injective f) : KProperNonab C X := by
  intro K L hK _ _ _ hn
  let e : K ≃* K.map f := K.equivMapOfInjective f hf
  exact hY.catalogue_of_surjective hC (K.map f) (map_ne_top_of_injective hf hK) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)

theorem KProperNonab.of_surjective (hC : IsoInvariant C) (hX : KProperNonab C X) (f : X →* Y)
    (hf : Function.Surjective f) : KProperNonab C Y := by
  intro K L hK _ _ _ hn
  exact hX.catalogue_of_surjective hC (K.comap f) (comap_ne_top_of_surjective hf hK) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp (f.subgroupComap K))
    ((QuotientGroup.mk'_surjective _).comp (f.subgroupComap_surjective K hf))

theorem KProperNonab.subgroup (hC : IsoInvariant C) (hX : KProperNonab C X) (H : Subgroup X) :
    KProperNonab C H :=
  hX.of_injective hC H.subtype H.subtype_injective

theorem KProperNonab.quotient (hC : IsoInvariant C) (hX : KProperNonab C X) (N : Subgroup X)
    [N.Normal] : KProperNonab C (X ⧸ N) :=
  hX.of_surjective hC (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem KProperNonab.section (hC : IsoInvariant C) (hX : KProperNonab C X) (H : Subgroup X)
    (N : Subgroup H) [N.Normal] : KProperNonab C (H ⧸ N) :=
  (hX.subgroup hC H).quotient hC N

theorem KProperNonab.of_mulEquiv (hC : IsoInvariant C) (hY : KProperNonab C Y) (e : X ≃* Y) :
    KProperNonab C X :=
  hY.of_injective hC e.toMonoidHom e.injective

theorem kProperNonab_congr (hC : IsoInvariant C) (e : X ≃* Y) :
    KProperNonab C X ↔ KProperNonab C Y :=
  ⟨fun h => h.of_mulEquiv hC e.symm, fun h => h.of_mulEquiv hC e⟩

end Nonab

section Compare

variable {X : Type u} [Group X]

theorem KGroupAllSimple.kGroupNonab (hX : KGroupAllSimple C X) : KGroupNonab C X := by
  intro K L _ _ hs _
  exact hX K (L.subgroupOf K) hs

theorem KGroupNonab.kGroupAllSimple [Finite X] (hC : IsoInvariant C)
    (hab : ContainsAbelianSimple C) (hX : KGroupNonab C X) : KGroupAllSimple C X := by
  intro H N _ _
  by_cases hcomm : ∀ a b : H ⧸ N, a * b = b * a
  · have : Finite (H ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
    exact hab _ hcomm
  · push Not at hcomm
    exact hX.catalogue_of_surjective hC H hcomm (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)

theorem kGroupNonab_iff_kGroupAllSimple [Finite X] (hC : IsoInvariant C)
    (hab : ContainsAbelianSimple C) : KGroupNonab C X ↔ KGroupAllSimple C X :=
  ⟨fun h => h.kGroupAllSimple hC hab, fun h => h.kGroupNonab⟩

theorem KProperAllSimple.kProperNonab (hC : IsoInvariant C) (hX : KProperAllSimple C X) :
    KProperNonab C X := by
  intro K L hK _ _ _ _
  exact hX.catalogue_of_surjective hC K hK (QuotientGroup.mk' (L.subgroupOf K))
    (QuotientGroup.mk'_surjective _)

theorem KProperNonab.kGroupAllSimple [Finite X] (hC : IsoInvariant C)
    (hab : ContainsAbelianSimple C) (hX : KProperNonab C X) (H : Subgroup X) (hH : H ≠ ⊤) :
    KGroupAllSimple C H :=
  (hX.kGroupNonab hC H hH).kGroupAllSimple hC hab

theorem KProperNonab.kProperAllSimple [Finite X] (hC : IsoInvariant C)
    (hab : ContainsAbelianSimple C) (hX : KProperNonab C X) : KProperAllSimple C X :=
  hX.kGroupAllSimple hC hab

theorem kProperNonab_iff_kProperAllSimple [Finite X] (hC : IsoInvariant C)
    (hab : ContainsAbelianSimple C) : KProperNonab C X ↔ KProperAllSimple C X :=
  ⟨fun h => h.kProperAllSimple hC hab, fun h => h.kProperNonab hC⟩

end Compare

section Transport

variable {D : Catalogue.{u}} {X : Type u} [Group X]

theorem KGroupAllSimple.mono (h : ∀ (S : Type u) [Group S] [IsSimpleGroup S], C S → D S)
    (hX : KGroupAllSimple C X) : KGroupAllSimple D X := by
  intro H N _ _
  exact h _ (hX H N inferInstance)

theorem KGroupAllSimple.mono_of_finite [Finite X]
    (h : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], C S → D S)
    (hX : KGroupAllSimple C X) : KGroupAllSimple D X := by
  intro H N _ _
  have : Finite (H ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
  exact h _ (hX H N inferInstance)

theorem KGroupAllSimple.mono_of_nonab [Finite X] (hab : ContainsAbelianSimple D)
    (h : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      C S → D S)
    (hX : KGroupAllSimple C X) : KGroupAllSimple D X := by
  intro H N _ _
  have : Finite (H ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
  by_cases hcomm : ∀ a b : H ⧸ N, a * b = b * a
  · exact hab _ hcomm
  · push Not at hcomm
    exact h _ hcomm (hX H N inferInstance)

theorem KProperAllSimple.mono_of_finite [Finite X]
    (h : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], C S → D S)
    (hX : KProperAllSimple C X) : KProperAllSimple D X :=
  fun H hH => (hX H hH).mono_of_finite h

theorem KGroupNonab.mono_of_finite [Finite X]
    (h : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      C S → D S)
    (hX : KGroupNonab C X) : KGroupNonab D X := by
  intro K L hLK _ hs hn
  have : Finite (K ⧸ L.subgroupOf K) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact h _ hn (hX K L hLK hs hn)

theorem KProperNonab.mono_of_finite [Finite X]
    (h : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      C S → D S)
    (hX : KProperNonab C X) : KProperNonab D X := by
  intro K L hK hLK _ hs hn
  have : Finite (K ⧸ L.subgroupOf K) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact h _ hn (hX K L hK hLK hs hn)

end Transport

section SQTK

variable {SQT : Catalogue.{u}} {X Y : Type u} [Group X] [Group Y]

theorem SQTKOver.of_mulEquiv (hC : IsoInvariant C) (hSQT : IsoInvariant SQT)
    (hY : SQTKOver C SQT Y) (e : X ≃* Y) : SQTKOver C SQT X :=
  ⟨hSQT e hY.1, hY.2.of_mulEquiv hC e⟩

theorem SQTKOver.subgroup (hC : IsoInvariant C)
    (hSQT : ∀ (H : Subgroup X), SQT X → SQT H) (hX : SQTKOver C SQT X) (H : Subgroup X) :
    SQTKOver C SQT H :=
  ⟨hSQT H hX.1, hX.2.subgroup hC H⟩

end SQTK

end CFSG.KCore
