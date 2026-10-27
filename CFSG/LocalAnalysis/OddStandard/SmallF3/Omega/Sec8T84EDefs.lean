module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8T84XCore (G : Type) [Group G] [Finite G] (t : G) (E Y1 Y2 : Subgroup G) :
    Prop where
  o_le1 : oddCoreIn (normalizer (E : Set G)) ≤ Y1
  o_le2 : oddCoreIn (normalizer (E : Set G)) ≤ Y2
  le1 : Y1 ≤ normalizer (E : Set G)
  le2 : Y2 ≤ normalizer (E : Set G)
  comm : ∀ a ∈ Y1, ∀ b ∈ Y2, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G))
  inf : Y1 ⊓ Y2 ≤ oddCoreIn (normalizer (E : Set G))
  sup : Y1 ⊔ Y2 ⊔ zpowers t = normalizer (E : Set G)
  t_not : t ∉ Y1 ⊔ Y2
  swap1 : ∀ a ∈ Y1, t * a * t⁻¹ ∈ Y2
  swap2 : ∀ a ∈ Y2, t * a * t⁻¹ ∈ Y1
  E_sup : E = (E ⊓ Y1) ⊔ (E ⊓ Y2)
  e16_1 : IsElemAb2 (E ⊓ Y1) 4
  e16_2 : IsElemAb2 (E ⊓ Y2) 4
  quot1 : QuotEquivTo Y1 ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) (alternatingGroup (Fin 6))
  quot2 : QuotEquivTo Y2 ((E ⊓ Y2) ⊔ oddCoreIn (normalizer (E : Set G))) (alternatingGroup (Fin 6))
  cent1 : Y1 ⊓ centralizer ((E ⊓ Y1 : Subgroup G) : Set G) ≤
    (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))
  cent2 : Y2 ⊓ centralizer ((E ⊓ Y2 : Subgroup G) : Set G) ≤
    (E ⊓ Y2) ⊔ oddCoreIn (normalizer (E : Set G))
  trans1 : ∀ v ∈ E ⊓ Y1, v ≠ 1 → ∀ w ∈ E ⊓ Y1, w ≠ 1 → ∃ y ∈ Y1, y * v * y⁻¹ = w
  trans2 : ∀ v ∈ E ⊓ Y2, v ≠ 1 → ∀ w ∈ E ⊓ Y2, w ≠ 1 → ∃ y ∈ Y2, y * v * y⁻¹ = w

@[expose] def Sec8T84SplitFor (G : Type) [Group G] [Finite G] (E Y : Subgroup G) : Prop :=
  ∃ H : Subgroup G, H ≤ Y ∧ H ⊓ ((E ⊓ Y) ⊔ oddCoreIn (normalizer (E : Set G))) ≤
    oddCoreIn (normalizer (E : Set G)) ∧
      H ⊔ ((E ⊓ Y) ⊔ oddCoreIn (normalizer (E : Set G))) = Y

theorem Sec8XO.core {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 : Subgroup G}
    (h : Sec8XO G t E Y1 Y2) : Sec8T84XCore G t E Y1 Y2 :=
  ⟨h.o_le1, h.o_le2, h.le1, h.le2, h.comm, h.inf, h.sup, h.t_not, h.swap1, h.swap2, h.E_sup,
    h.e16_1, h.e16_2, h.quot1, h.quot2, h.cent1, h.cent2, h.trans1, h.trans2⟩

theorem Sec8XO.of_core_split {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 : Subgroup G}
    (h : Sec8T84XCore G t E Y1 Y2) (s1 : Sec8T84SplitFor G E Y1)
    (s2 : Sec8T84SplitFor G E Y2) : Sec8XO G t E Y1 Y2 :=
  ⟨h.o_le1, h.o_le2, h.le1, h.le2, h.comm, h.inf, h.sup, h.t_not, h.swap1, h.swap2, h.E_sup,
    h.e16_1, h.e16_2, h.quot1, h.quot2, h.cent1, h.cent2, h.trans1, h.trans2, s1, s2⟩

@[expose] def Asc82Lemma811KCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
      Sec8E G t L S z g B E → ∃ Y1 Y2 : Subgroup G, Sec8T84XCore G t E Y1 Y2

@[expose] def Sec8T84SplitK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
      Sec8E G t L S z g B E → ∀ Y1 Y2 : Subgroup G, Sec8T84XCore G t E Y1 Y2 →
        Sec8T84SplitFor G E Y1 ∧ Sec8T84SplitFor G E Y2

theorem asc82Lemma811K_of_core_split (hc : Asc82Lemma811KCore) (hs : Sec8T84SplitK) :
    Asc82Lemma811K := by
  intro G _ _ hK t L S z g B E hE
  obtain ⟨Y1, Y2, h⟩ := hc G hK t L S z g B E hE
  obtain ⟨s1, s2⟩ := hs G hK t L S z g B E hE Y1 Y2 h
  exact ⟨Y1, Y2, Sec8XO.of_core_split h s1 s2⟩

end CFSG.OddStandard.SmallF3.Omega
