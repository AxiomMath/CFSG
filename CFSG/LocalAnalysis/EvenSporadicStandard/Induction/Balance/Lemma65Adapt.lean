module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Basic
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.RankThree.PerfectCover

@[expose] def M23Facts : Prop :=
  IsSimpleGroup (Carrier .M23) ∧ Nat.card (Carrier .M23) = 10200960

@[expose] def M24Recognition : Prop :=
  ∀ {G : Type} [Group G], CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ {K L : Subgroup G}, K ≠ ⊤ → L ≤ K → ∀ [(L.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L.subgroupOf K) → Nat.card (K ⧸ L.subgroupOf K) = 244823040 →
        IsSporadic (K ⧸ L.subgroupOf K) .M24

@[expose] def M24Multiplier : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* Carrier .M24) → Nat.card (hopfMultiplier X) = 1

theorem nonempty_subgroupQuotEquiv {G : Type} [Group G] {H E H₁ : Subgroup G} (hH₁ : H₁ ≤ H)
    (hEN : (E.subgroupOf H).Normal) (hN : (E.subgroupOf H₁).Normal) :
    Nonempty (↥(H₁.subgroupOf H) ⧸ (E.subgroupOf H).subgroupOf (H₁.subgroupOf H) ≃*
      ↥H₁ ⧸ E.subgroupOf H₁) :=
  ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hH₁) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨⟨y, hH₁ y.2⟩, y.2⟩, hy, rfl⟩)⟩

theorem setting65_of_subgroup {G : Type} [Group G] {H E H₁ : Subgroup G} {e : G}
    (hEH : E ≤ H) (hH₁ : H₁ ≤ H) (hEN : (E.subgroupOf H).Normal)
    (hN : (E.subgroupOf H₁).Normal) (hab : IsElemAbelian 2 E) (hcard : Nat.card E = 2 ^ 12)
    (hcent : centralizer (E : Set G) ⊓ H = E) (he : e ∈ E) (hord : orderOf e = 2)
    (horb : Set.ncard {x : G | ∃ h ∈ H, x = h * e * h⁻¹} = 24)
    (hC : centralizer ({e} : Set G) ⊓ H = H₁ ⊔ zpowers e) (hdisj : Disjoint H₁ (zpowers e))
    (hsimple : IsSimpleGroup (H₁ ⧸ E.subgroupOf H₁))
    (hcard₁ : Nat.card (H₁ ⧸ E.subgroupOf H₁) = 10200960) :
    Setting65 ↥H (E.subgroupOf H) (H₁.subgroupOf H) ⟨e, hEH he⟩ := by
  have heH : e ∈ H := hEH he
  obtain ⟨φ⟩ := nonempty_subgroupQuotEquiv hH₁ hEN hN
  have hcommE : ∀ x y : G, x ∈ E → y ∈ E → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcentE : centralizer (((E.subgroupOf H : Subgroup ↥H)) : Set ↥H) =
      (centralizer (E : Set G)).subgroupOf H := by
    ext γ
    rw [mem_centralizer_iff, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro h x hx
      exact congrArg Subtype.val (h ⟨x, hEH hx⟩ hx)
    · intro h x hx
      exact Subtype.ext (h x hx)
  have hcentel : centralizer ({(⟨e, heH⟩ : ↥H)} : Set ↥H) =
      (centralizer ({e} : Set G)).subgroupOf H := by
    ext γ
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hzp : (zpowers e).subgroupOf H = zpowers (⟨e, heH⟩ : ↥H) := by
    ext x
    rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [Subgroup.coe_zpow]⟩
  refine
    { normal := hEN
      elemAb := ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcommE (a : ↥H) (b : ↥H) a.2 b.2))⟩⟩,
        fun x hx => Subtype.ext (by simpa using hab.2 (x : G) hx)⟩
      card := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv).trans hcard
      cent := ?_
      mem := he
      order := by rw [Subgroup.orderOf_mk, hord]
      orbit := ?_
      centralizer_e := ?_
      disjoint := ?_
      normal₁ := inferInstance
      simple := φ.isSimpleGroup
      card₁ := (Nat.card_congr φ.toEquiv).trans hcard₁ }
  · rw [hcentE, ← Subgroup.inf_subgroupOf_right (centralizer (E : Set G)) H, hcent]
  · have himg : Subtype.val '' {x : ↥H | ∃ h : ↥H, x = h * (⟨e, heH⟩ : ↥H) * h⁻¹} =
        {x : G | ∃ h ∈ H, x = h * e * h⁻¹} := by
      ext y
      constructor
      · rintro ⟨x, ⟨h, rfl⟩, rfl⟩
        exact ⟨h, h.2, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(⟨h, hh⟩ : ↥H) * (⟨e, heH⟩ : ↥H) * (⟨h, hh⟩ : ↥H)⁻¹, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
    exact horb
  · rw [hcentel, ← Subgroup.inf_subgroupOf_right (centralizer ({e} : Set G)) H, hC,
      Subgroup.subgroupOf_sup hH₁ (zpowers_le.2 heH), hzp]
  · rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    have hx2' : (x : G) ∈ zpowers e := by
      rw [← hzp] at hx2
      exact hx2
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj hx1 hx2')

end CFSG.EvenSporadicStandard.Induction.Balance
