module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ClassCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsModel

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

section Abstract

variable {G : Type*} [Group G]

theorem card_centralizer_eq_of_isConj [Finite G] {a y : G} (h : IsConj a y) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  have hset : {x : G | IsConj a x} = {x : G | IsConj y x} := by
    ext x
    exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩
  have ha := ncard_isConj_mul_card_centralizer a
  have hy := ncard_isConj_mul_card_centralizer y
  rw [← hset] at hy
  have hG : 0 < Nat.card G := Nat.card_pos
  have hN : 0 < {x : G | IsConj a x}.ncard := by
    rcases Nat.eq_zero_or_pos {x : G | IsConj a x}.ncard with h0 | h0
    · rw [h0, zero_mul] at ha
      omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_left hN (ha.trans hy.symm)

theorem orderOf_eq_of_isConj' {a y : G} (h : IsConj a y) : orderOf a = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact ((MulAut.conj c).orderOf_eq a).symm

structure HSInvolutionData (G : Type*) [Group G] : Prop where
  card_eq : Nat.card G = 44352000
  exists_reps : ∃ a b : G, orderOf a = 2 ∧ orderOf b = 2 ∧
    Nat.card (centralizer ({a} : Set G)) = 7680 ∧ Nat.card (centralizer ({b} : Set G)) = 2880 ∧
    ∀ y : G, orderOf y = 2 → IsConj a y ∨ IsConj b y

variable [Finite G]

theorem HSInvolutionData.card_centralizer (D : HSInvolutionData G) {y : G} (hy : orderOf y = 2) :
    Nat.card (centralizer ({y} : Set G)) = 7680 ∨ Nat.card (centralizer ({y} : Set G)) = 2880 := by
  obtain ⟨a, b, -, -, ha, hb, hcov⟩ := D.exists_reps
  rcases hcov y hy with h | h
  · exact Or.inl ((card_centralizer_eq_of_isConj h).symm.trans ha)
  · exact Or.inr ((card_centralizer_eq_of_isConj h).symm.trans hb)

theorem HSInvolutionData.isConj_of_card_eq (D : HSInvolutionData G) {y y' : G}
    (hy : orderOf y = 2) (hy' : orderOf y' = 2)
    (h : Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({y'} : Set G))) :
    IsConj y y' := by
  obtain ⟨a, b, -, -, ha, hb, hcov⟩ := D.exists_reps
  have key : ∀ x, IsConj a x → Nat.card (centralizer ({x} : Set G)) = 7680 := fun x hx =>
    (card_centralizer_eq_of_isConj hx).symm.trans ha
  have key' : ∀ x, IsConj b x → Nat.card (centralizer ({x} : Set G)) = 2880 := fun x hx =>
    (card_centralizer_eq_of_isConj hx).symm.trans hb
  rcases hcov y hy with h1 | h1 <;> rcases hcov y' hy' with h2 | h2
  · exact h1.symm.trans h2
  · have := key y h1
    have := key' y' h2
    omega
  · have := key' y h1
    have := key y' h2
    omega
  · exact h1.symm.trans h2

theorem HSInvolutionData.ncard_involutions (D : HSInvolutionData G) :
    {y : G | orderOf y = 2}.ncard = 21175 := by
  obtain ⟨a, b, ha2, hb2, ha, hb, hcov⟩ := D.exists_reps
  have hG := D.card_eq
  have hA := ncard_isConj_mul_card_centralizer a
  have hB := ncard_isConj_mul_card_centralizer b
  rw [ha, hG] at hA
  rw [hb, hG] at hB
  have hA' : {x : G | IsConj a x}.ncard = 5775 := by omega
  have hB' : {x : G | IsConj b x}.ncard = 15400 := by omega
  have hU : {y : G | orderOf y = 2} = {x : G | IsConj a x} ∪ {x : G | IsConj b x} := by
    ext y
    constructor
    · intro hy
      exact hcov y hy
    · rintro (hy | hy)
      · exact (orderOf_eq_of_isConj' hy).symm.trans ha2
      · exact (orderOf_eq_of_isConj' hy).symm.trans hb2
  have hD : Disjoint {x : G | IsConj a x} {x : G | IsConj b x} := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    have h1 := (card_centralizer_eq_of_isConj hxa).symm.trans ha
    have h2 := (card_centralizer_eq_of_isConj hxb).symm.trans hb
    omega
  rw [hU, Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _), hA', hB']

end Abstract

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem card_centralizer_equiv (e : G ≃* H) (y : G) :
    Nat.card (centralizer ({e y} : Set H)) = Nat.card (centralizer ({y} : Set G)) :=
  (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => by
    simp only [mem_centralizer_singleton_iff]
    show x * y = y * x ↔ e x * e y = e y * e x
    rw [← map_mul, ← map_mul, e.injective.eq_iff])).symm

theorem HSInvolutionData.of_equiv (e : G ≃* H) (D : HSInvolutionData G) : HSInvolutionData H := by
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans D.card_eq, ?_⟩
  obtain ⟨a, b, ha2, hb2, ha, hb, hcov⟩ := D.exists_reps
  refine ⟨e a, e b, (e.orderOf_eq a).trans ha2, (e.orderOf_eq b).trans hb2,
    (card_centralizer_equiv e a).trans ha, (card_centralizer_equiv e b).trans hb, fun y hy => ?_⟩
  have hy' : orderOf (e.symm y) = 2 := (e.symm.orderOf_eq y).trans hy
  have map_conj : ∀ x x' : G, IsConj x x' → IsConj (e x) (e x') := fun x x' hx => by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    exact isConj_iff.2 ⟨e c, by simp⟩
  rcases hcov _ hy' with h | h
  · exact Or.inl (by simpa using map_conj _ _ h)
  · exact Or.inr (by simpa using map_conj _ _ h)

end Transport

section Model

set_option linter.unusedSectionVars false


theorem card_centralizer_hsP (t : Equiv.Perm (Fin 3850)) (ht : t ∈ hsP) :
    Nat.card (centralizer ({(⟨t, ht⟩ : ↥hsP)} : Set ↥hsP)) =
      Nat.card (hsP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 3850))) : Subgroup _) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, mem_centralizer_singleton_iff.2 (by
        have := mem_centralizer_singleton_iff.1 x.2
        exact congrArg Subtype.val this)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext (by
        exact mem_centralizer_singleton_iff.1 x.2.2))⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem hsInvolutionData_hsP : HSInvolutionData ↥hsP := by
  obtain ⟨-, -, h1, h2, hcov⟩ := hs_reps
  obtain ⟨hm1, ho1⟩ := hsT1_mem_ord
  obtain ⟨hm2, ho2⟩ := hsT2_mem_ord
  refine ⟨card_hsP, ⟨⟨hsT1, hm1⟩, ⟨hsT2, hm2⟩, ?_, ?_, ?_, ?_, fun y hy => ?_⟩⟩
  · rw [← Subgroup.orderOf_coe]
    exact ho1
  · rw [← Subgroup.orderOf_coe]
    exact ho2
  · rw [card_centralizer_hsP]
    exact h1
  · rw [card_centralizer_hsP]
    exact h2
  · have hy' : orderOf (y : Equiv.Perm (Fin 3850)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hy
    obtain ⟨r, hr, g, hg, hgr⟩ := hcov y y.2 hy'
    rcases hr with rfl | rfl
    · exact Or.inl (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgr.symm⟩)
    · exact Or.inr (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgr.symm⟩)

end Model

section Main

set_option linter.unusedSectionVars false


theorem hsInvolutionData_of_isSporadic {Y : Type} [Group Y] (hY : IsSporadic Y .HS) :
    HSInvolutionData Y := by
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.HS := e₀
  exact hsInvolutionData_hsP.of_equiv (e.trans hsPermEquiv).symm

theorem card_eq_of_isSporadic_hs {Y : Type} [Group Y] (hY : IsSporadic Y .HS) :
    Nat.card Y = 44352000 :=
  (hsInvolutionData_of_isSporadic hY).card_eq

theorem card_centralizer_of_involution_hs {Y : Type} [Group Y] (hY : IsSporadic Y .HS) (y : Y)
    (hy : orderOf y = 2) :
    Nat.card (centralizer ({y} : Set Y)) = 7680 ∨ Nat.card (centralizer ({y} : Set Y)) = 2880 := by
  have := (hsInvolutionData_of_isSporadic hY).card_eq
  have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  exact (hsInvolutionData_of_isSporadic hY).card_centralizer hy

theorem isConj_of_card_centralizer_eq_hs {Y : Type} [Group Y] (hY : IsSporadic Y .HS) (y y' : Y)
    (hy : orderOf y = 2) (hy' : orderOf y' = 2)
    (h : Nat.card (centralizer ({y} : Set Y)) = Nat.card (centralizer ({y'} : Set Y))) :
    IsConj y y' := by
  have := (hsInvolutionData_of_isSporadic hY).card_eq
  have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  exact (hsInvolutionData_of_isSporadic hY).isConj_of_card_eq hy hy' h

theorem ncard_involutions_hs {Y : Type} [Group Y] (hY : IsSporadic Y .HS) :
    {y : Y | orderOf y = 2}.ncard = 21175 := by
  have := (hsInvolutionData_of_isSporadic hY).card_eq
  have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  exact (hsInvolutionData_of_isSporadic hY).ncard_involutions

theorem ncard_involutions_hs_le_of_le {G : Type} [Group G] (L : Subgroup G)
    (hL : IsSporadic ↥L .HS) :
    {g : G | g ∈ L ∧ orderOf g = 2}.ncard = 21175 := by
  have h := ncard_involutions_hs hL
  rw [← h]
  have himg : {g : G | g ∈ L ∧ orderOf g = 2} = L.subtype '' {y : ↥L | orderOf y = 2} := by
    ext g
    constructor
    · rintro ⟨hg, hg2⟩
      exact ⟨⟨g, hg⟩, by show orderOf (⟨g, hg⟩ : ↥L) = 2; rw [← Subgroup.orderOf_coe]; exact hg2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [← Subgroup.orderOf_coe] using hy⟩
  rw [himg, Set.ncard_image_of_injective _ L.subtype_injective]

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
