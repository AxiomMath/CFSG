module

public import CFSG.GH74.E2.CaseIIStruct
public import CFSG.GH74.E2.OddRankG

public section

namespace CFSG.GH74.E2

open Subgroup

@[expose] def NoCaseIIAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K → (ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) → B ≤ K →
    (∀ b ∈ B, ∀ q ∈ Qt t, b * q = q * b) → (∀ k ∈ K, t' * k = k * t') → False

@[expose] def NoCaseIIBeta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B K : Subgroup G),
    CaseII t t' a A B → IsCompCen t K →
    (ShapeA5 ↥K ∨ ShapeL27 ↥K ∨ ShapeA6 ↥K ∨ ShapeL217 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) →
    Nonempty (↥(Qt t) ≃* QuaternionGroup 2) →
    Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 → False

theorem card_inf_centralizer_transport {G : Type*} [Group G] {H B : Subgroup G} (hBH : B ≤ H)
    (Q' : Subgroup H) :
    Nat.card ↥(B.subgroupOf H ⊓ centralizer (Q' : Set H)) =
      Nat.card ↥(B ⊓ centralizer ((Q'.map H.subtype : Subgroup G) : Set G)) := by
  have hmap : (B.subgroupOf H ⊓ centralizer (Q' : Set H)).map H.subtype =
      B ⊓ centralizer ((Q'.map H.subtype : Subgroup G) : Set G) := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxB, hxC⟩, rfl⟩
      refine ⟨hxB, ?_⟩
      refine mem_centralizer_iff.2 ?_
      rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hxC q hq)
    · rintro ⟨hgB, hgC⟩
      refine ⟨⟨g, hBH hgB⟩, ⟨hgB, ?_⟩, rfl⟩
      refine mem_centralizer_iff.2 ?_
      intro q hq
      apply Subtype.ext
      exact mem_centralizer_iff.1 hgC (q : G) ⟨q, hq, rfl⟩
  rw [← hmap]
  exact (Subgroup.card_map_of_injective H.subtype_injective).symm

theorem noCaseIIComp_of (hComp : ComponentList) (hD : K0Data) (hD3 : K0Data3) (hQ8 : Q8Lemma)
    (hα : NoCaseIIAlpha) (hβ : NoCaseIIBeta) : NoCaseIIComp := by
  intro G _ _ hH t t' a A B hc hl
  have ht := hc.order_t
  have hgenC : Gen4 ↥(Cen t) := Gen4.subgroup (Cen t) hH.gen4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := exists_isCompCen_of_layer_ne_bot hl
  obtain ⟨hshape, huniq⟩ := hComp G hH t ht K hK
  have hL := localK_of_component hH ht
    (fun K₁ K₂ h₁ h₂ => (huniq K₁ h₁).trans (huniq K₂ h₂).symm) hK
  have hKle : K ≤ Cen t := hK.1
  have hshape' : K0Shape ↥(K.subgroupOf (Cen t)) :=
    K0Shape.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle).symm hshape
  have hBC : B ≤ Cen t := fun b hb => mem_Cen'.2 (hc.centralizes_t b hb)
  have hBab : ElemAb 3 B :=
    ⟨fun a ha b hb => hc.elemAb.1 a (hc.B_le ha) b (hc.B_le hb),
      fun a ha => hc.elemAb.2 a (hc.B_le ha)⟩
  have hB'ab : ElemAb 3 (B.subgroupOf (Cen t)) :=
    ⟨fun a ha b hb => Subtype.ext (hBab.1 a ha b hb), fun a ha => Subtype.ext (hBab.2 a ha)⟩
  have hB'card : Nat.card (B.subgroupOf (Cen t)) = 9 := by
    rw [← hc.card_B]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  have htC : t ∈ Cen t := mem_Cen.2 rfl
  have ht'C : t' ∈ Cen t := mem_Cen.2 hc.comm
  have htQ : (⟨t, htC⟩ : Cen t) ∈ CFSG.pCore 2 ↥(Cen t) := (mem_Qt.1 (t_mem_Qt ht)).2
  have ht1 : (⟨t, htC⟩ : Cen t) ≠ 1 := by
    intro h1
    have : t = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at ht
    omega
  have ht2 : (⟨t, htC⟩ : Cen t) ^ 2 = 1 := Subtype.ext (sq_eq_one_of_orderOf ht)
  have ht'1 : (⟨t', ht'C⟩ : Cen t) ≠ 1 := by
    intro h1
    have h2 : t' = 1 := congrArg Subtype.val h1
    have := hc.order_t'
    rw [h2, orderOf_one] at this
    omega
  have htt' : (⟨t', ht'C⟩ : Cen t) ≠ ⟨t, htC⟩ := fun h1 => hc.ne (congrArg Subtype.val h1).symm
  have ht'2 : (⟨t', ht'C⟩ : Cen t) ^ 2 = 1 := Subtype.ext (sq_eq_one_of_orderOf hc.order_t')
  have hcomm : (⟨t, htC⟩ : Cen t) * ⟨t', ht'C⟩ = ⟨t', ht'C⟩ * ⟨t, htC⟩ := Subtype.ext hc.comm
  have hBt : ∀ b ∈ B.subgroupOf (Cen t), b * (⟨t, htC⟩ : Cen t) = ⟨t, htC⟩ * b := fun b hb =>
    Subtype.ext (hc.centralizes_t b hb)
  have hBt' : ∀ b ∈ B.subgroupOf (Cen t), b * (⟨t', ht'C⟩ : Cen t) = ⟨t', ht'C⟩ * b := fun b hb =>
    Subtype.ext (hc.centralizes_t' b hb)
  rcases caseII_structure hgenC hL hshape' hD hD3 hB'ab hB'card htQ ht1 ht2 ht'1 htt' ht'2 hcomm
      hBt hBt' with ⟨hBQ, hsh, hBK, ht'K⟩ | ⟨hcard3, hr2, hP2, hsh, c, hcK, hcord, φ, hφ, hφord,
      hφirr, hfix⟩
  · refine hα G hH t t' a A B K hc hK ?_ ?_ ?_ ?_
    · have e := Subgroup.subgroupOfEquivOfLe hKle
      rcases hsh with h1 | h1 | h1
      · exact Or.inl (ShapeA6.of_mulEquiv e h1)
      · exact Or.inr (Or.inl (lieModel_of_mulEquiv e h1))
      · exact Or.inr (Or.inr (isSporadic_of_mulEquiv e h1))
    · intro b hb
      have : (⟨b, hBC hb⟩ : Cen t) ∈ K.subgroupOf (Cen t) := hBK hb
      exact this
    · intro b hb q hq
      obtain ⟨hqC, hq'⟩ := mem_Qt.1 hq
      have hb' : (⟨b, hBC hb⟩ : Cen t) ∈ B.subgroupOf (Cen t) := hb
      have := mem_centralizer_iff.1 (hBQ hb') ⟨q, hqC⟩ hq'
      exact (congrArg Subtype.val this).symm
    · intro k hk
      have := ht'K ⟨k, hKle hk⟩ hk
      exact congrArg Subtype.val this
  · have hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥(Cen t)) := CFSG.pCore_isPGroup
    have hP2' : ∀ P : Subgroup ↥(CFSG.pCore 2 ↥(Cen t)), Group.rank ↥P ≤ 2 := by
      intro P
      have h1 := hP2 (P.map (CFSG.pCore 2 ↥(Cen t)).subtype) (by
        rintro _ ⟨x, -, rfl⟩
        exact x.2)
      rwa [← Group.rank_congr (P.equivMapOfInjective _ (Subgroup.subtype_injective _))] at h1
    obtain ⟨hQ8iso⟩ := hQ8 ↥(CFSG.pCore 2 ↥(Cen t)) φ hQ2 hr2 hP2' hφord hφirr hfix
    have hQ8G : Nonempty (↥(Qt t) ≃* QuaternionGroup 2) :=
      ⟨((CFSG.pCore 2 ↥(Cen t)).equivMapOfInjective (Cen t).subtype
        (Cen t).subtype_injective).symm.trans hQ8iso⟩
    have hshapeK : ShapeA5 ↥K ∨ ShapeL27 ↥K ∨ ShapeA6 ↥K ∨ ShapeL217 ↥K ∨ ShapeL33 ↥K ∨
        ShapeM11 ↥K := by
      have e := Subgroup.subgroupOfEquivOfLe hKle
      rcases hsh with h1 | h1 | h1 | h1 | h1 | h1
      · exact Or.inl (ShapeA5.of_mulEquiv e h1)
      · exact Or.inr (Or.inl (ShapeL27.of_mulEquiv e h1))
      · exact Or.inr (Or.inr (Or.inl (ShapeA6.of_mulEquiv e h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv e h1)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isSporadic_of_mulEquiv e h1)))))
    have hcardG : Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3 := by
      have h := card_inf_centralizer_transport hBC (CFSG.pCore 2 ↥(Cen t))
      exact h.symm.trans hcard3
    exact hβ G hH t t' a A B K hc hK hshapeK hQ8G hcardG

end CFSG.GH74.E2
