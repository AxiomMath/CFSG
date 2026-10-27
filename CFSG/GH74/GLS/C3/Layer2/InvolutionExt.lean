module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.C3.Layer2

open Subgroup

theorem mem_sup_zpowers_iff {G : Type*} [Group G] {T : Subgroup G} {a : G}
    (haN : ∀ t ∈ T, a * t * a⁻¹ ∈ T) (ha2 : a ^ 2 = 1) {g : G} :
    g ∈ T ⊔ zpowers a ↔ g ∈ T ∨ g * a⁻¹ ∈ T := by
  have haa : a * a = 1 := by rwa [← sq]
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haN' : ∀ t ∈ T, a * t * a ∈ T := fun t ht => by
    have := haN t ht
    rwa [ha] at this
  let N : Subgroup G :=
    { carrier := {g | g ∈ T ∨ g * a⁻¹ ∈ T}
      one_mem' := Or.inl T.one_mem
      mul_mem' := by
        rintro g h (hg | hg) (hh | hh)
        · exact Or.inl (T.mul_mem hg hh)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact T.mul_mem hg hh
        · refine Or.inr ?_
          have : g * h * a⁻¹ = (g * a⁻¹) * (a * h * a⁻¹) := by group
          rw [this]
          exact T.mul_mem hg (haN h hh)
        · refine Or.inl ?_
          have : g * h = (g * a⁻¹) * (a * (h * a⁻¹) * a) := by group
          rw [this]
          exact T.mul_mem hg (haN' _ hh)
      inv_mem' := by
        rintro g (hg | hg)
        · exact Or.inl (T.inv_mem hg)
        · refine Or.inr ?_
          have : g⁻¹ * a⁻¹ = a * (g * a⁻¹)⁻¹ * a := by rw [ha]; group
          rw [this]
          exact haN' _ (T.inv_mem hg) }
  constructor
  · intro hg
    have hle : T ⊔ zpowers a ≤ N := by
      refine sup_le (fun t ht => Or.inl ht) (zpowers_le.mpr (Or.inr ?_))
      rw [mul_inv_cancel]
      exact T.one_mem
    exact hle hg
  · rintro (hg | hg)
    · exact mem_sup_left hg
    · have := mul_mem_sup hg (mem_zpowers a)
      rwa [inv_mul_cancel_right] at this

theorem card_sup_zpowers {G : Type*} [Group G] [Finite G] {T : Subgroup G} {a : G}
    (haN : ∀ t ∈ T, a * t * a⁻¹ ∈ T) (ha2 : a ^ 2 = 1) (haT : a ∉ T) :
    Nat.card ↥(T ⊔ zpowers a) = 2 * Nat.card T := by
  have haa : a * a = 1 := by rwa [← sq]
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hidx : T.relIndex (T ⊔ zpowers a) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨a, mem_sup_right (mem_zpowers a), fun x hx => ?_⟩
    rcases (mem_sup_zpowers_iff haN ha2).mp hx with hxT | hxT
    · refine Or.inr ⟨hxT, fun h => haT ?_⟩
      have := T.mul_mem (T.inv_mem hxT) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, fun h => haT ?_⟩
      · rw [← ha]
        exact hxT
      · rw [ha] at hxT
        have := T.mul_mem (T.inv_mem hxT) h
        simpa using this
  have h := relIndex_mul_card T (T ⊔ zpowers a)
  rw [inf_eq_left.mpr le_sup_left, hidx] at h
  rw [← h, mul_comm]

section Extension

variable {G G' : Type*} [Group G] [Group G'] {T : Subgroup G} {T' : Subgroup G'}

open Classical in
private noncomputable def extTotal (e : ↥T ≃* ↥T') (g : G) : G' :=
  if h : g ∈ T then (e ⟨g, h⟩ : G') else 1

private theorem extTotal_of_mem (e : ↥T ≃* ↥T') {t : G} (ht : t ∈ T) :
    extTotal e t = ((e ⟨t, ht⟩ : ↥T') : G') := by
  rw [extTotal, dite_eq_left ht]

private theorem extTotal_mem (e : ↥T ≃* ↥T') (g : G) : extTotal e g ∈ T' := by
  unfold extTotal
  split_ifs
  · exact SetLike.coe_mem _
  · exact T'.one_mem

private theorem extTotal_mul (e : ↥T ≃* ↥T') {s t : G} (hs : s ∈ T) (ht : t ∈ T) :
    extTotal e (s * t) = extTotal e s * extTotal e t := by
  rw [extTotal_of_mem e (T.mul_mem hs ht), extTotal_of_mem e hs, extTotal_of_mem e ht]
  exact congrArg Subtype.val (map_mul e ⟨s, hs⟩ ⟨t, ht⟩)

private theorem extTotal_symm_extTotal (e : ↥T ≃* ↥T') {t : G} (ht : t ∈ T) :
    extTotal e.symm (extTotal e t) = t := by
  rw [extTotal_of_mem e ht, extTotal_of_mem e.symm (SetLike.coe_mem _)]
  simp

private theorem extTotal_conj (e : ↥T ≃* ↥T') {a : G} {a' : G'} (haN : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (hconj : ∀ (t : G) (ht : t ∈ T), ((e ⟨a * t * a⁻¹, haN t ht⟩ : ↥T') : G') =
      a' * ((e ⟨t, ht⟩ : ↥T') : G') * a'⁻¹)
    {t : G} (ht : t ∈ T) : extTotal e (a * t * a⁻¹) = a' * extTotal e t * a'⁻¹ := by
  rw [extTotal_of_mem e (haN t ht), extTotal_of_mem e ht]
  exact hconj t ht

open Classical in
private noncomputable def extFun (e : ↥T ≃* ↥T') (a : G) (a' : G') (g : G) : G' :=
  if g ∈ T then extTotal e g else extTotal e (g * a⁻¹) * a'

private theorem extFun_of_mem (e : ↥T ≃* ↥T') (a : G) (a' : G') {t : G} (ht : t ∈ T) :
    extFun e a a' t = extTotal e t := by
  rw [extFun, ite_eq_left ht]

private theorem extFun_of_not_mem (e : ↥T ≃* ↥T') (a : G) (a' : G') {g : G} (hg : g ∉ T) :
    extFun e a a' g = extTotal e (g * a⁻¹) * a' := by
  rw [extFun, ite_eq_right hg]

private theorem extFun_self (e : ↥T ≃* ↥T') {a : G} (a' : G') (haT : a ∉ T) :
    extFun e a a' a = a' := by
  rw [extFun_of_not_mem e a a' haT, mul_inv_cancel, extTotal_of_mem e T.one_mem]
  simp

private theorem extFun_mem (e : ↥T ≃* ↥T') (a : G) (a' : G') (g : G) :
    extFun e a a' g ∈ T' ⊔ zpowers a' := by
  by_cases hg : g ∈ T
  · rw [extFun_of_mem e a a' hg]
    exact mem_sup_left (extTotal_mem e g)
  · rw [extFun_of_not_mem e a a' hg]
    exact mul_mem (mem_sup_left (extTotal_mem e _)) (mem_sup_right (mem_zpowers a'))

private theorem extFun_symm_extFun (e : ↥T ≃* ↥T') {a : G} {a' : G'} (ha'T : a' ∉ T') {g : G}
    (hg : g ∈ T ∨ g * a⁻¹ ∈ T) : extFun e.symm a' a (extFun e a a' g) = g := by
  by_cases hgT : g ∈ T
  · rw [extFun_of_mem e a a' hgT, extFun_of_mem e.symm a' a (extTotal_mem e g)]
    exact extTotal_symm_extTotal e hgT
  · have hg' : g * a⁻¹ ∈ T := hg.resolve_left hgT
    have hs : extTotal e (g * a⁻¹) * a' ∉ T' := fun H => ha'T (by
      simpa using T'.mul_mem (T'.inv_mem (extTotal_mem e (g * a⁻¹))) H)
    rw [extFun_of_not_mem e a a' hgT, extFun_of_not_mem e.symm a' a hs, mul_inv_cancel_right,
      extTotal_symm_extTotal e hg', inv_mul_cancel_right]

private theorem extFun_mul (e : ↥T ≃* ↥T') {a : G} {a' : G'} (ha2 : a ^ 2 = 1)
    (ha'2 : a' ^ 2 = 1) (haN : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (hconj : ∀ (t : G) (ht : t ∈ T), ((e ⟨a * t * a⁻¹, haN t ht⟩ : ↥T') : G') =
      a' * ((e ⟨t, ht⟩ : ↥T') : G') * a'⁻¹)
    {g h : G} (hg : g ∈ T ∨ g * a⁻¹ ∈ T) (hh : h ∈ T ∨ h * a⁻¹ ∈ T) :
    extFun e a a' (g * h) = extFun e a a' g * extFun e a a' h := by
  have haa : a * a = 1 := by rwa [← sq]
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have ha'a' : a' * a' = 1 := by rwa [← sq]
  have ha' : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'a'
  by_cases hgT : g ∈ T <;> by_cases hhT : h ∈ T
  · rw [extFun_of_mem e a a' (T.mul_mem hgT hhT), extFun_of_mem e a a' hgT,
      extFun_of_mem e a a' hhT, extTotal_mul e hgT hhT]
  · have hh' : h * a⁻¹ ∈ T := hh.resolve_left hhT
    have hgh : g * h ∉ T := fun H => hhT (by simpa using T.mul_mem (T.inv_mem hgT) H)
    rw [extFun_of_not_mem e a a' hgh, extFun_of_mem e a a' hgT, extFun_of_not_mem e a a' hhT,
      mul_assoc g h, extTotal_mul e hgT hh', mul_assoc]
  · have hg' : g * a⁻¹ ∈ T := hg.resolve_left hgT
    have hgh : g * h ∉ T := fun H => hgT (by simpa using T.mul_mem H (T.inv_mem hhT))
    have key : g * h * a⁻¹ = (g * a⁻¹) * (a * h * a⁻¹) := by group
    rw [extFun_of_not_mem e a a' hgh, extFun_of_not_mem e a a' hgT, extFun_of_mem e a a' hhT,
      key, extTotal_mul e hg' (haN h hhT), extTotal_conj e haN hconj hhT]
    group
  · have hg' : g * a⁻¹ ∈ T := hg.resolve_left hgT
    have hh' : h * a⁻¹ ∈ T := hh.resolve_left hhT
    have key : g * h = (g * a⁻¹) * (a * (h * a⁻¹) * a⁻¹) := by
      calc g * h = (g * a⁻¹) * (a * (h * a⁻¹) * a) := by group
        _ = (g * a⁻¹) * (a * (h * a⁻¹) * a⁻¹) := by rw [ha]
    have hgh : g * h ∈ T := by
      rw [key]
      exact T.mul_mem hg' (haN _ hh')
    rw [extFun_of_mem e a a' hgh, extFun_of_not_mem e a a' hgT, extFun_of_not_mem e a a' hhT,
      key, extTotal_mul e hg' (haN _ hh'), extTotal_conj e haN hconj hh', ha']
    group

end Extension

theorem exists_mulEquiv_sup_zpowers {G G' : Type*} [Group G] [Group G'] {T : Subgroup G}
    {T' : Subgroup G'} (e : ↥T ≃* ↥T') {a : G} {a' : G'} (ha2 : a ^ 2 = 1) (ha'2 : a' ^ 2 = 1)
    (haT : a ∉ T) (ha'T : a' ∉ T') (haN : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (ha'N : ∀ t ∈ T', a' * t * a'⁻¹ ∈ T')
    (hconj : ∀ (t : G) (ht : t ∈ T), ((e ⟨a * t * a⁻¹, haN t ht⟩ : ↥T') : G') =
      a' * ((e ⟨t, ht⟩ : ↥T') : G') * a'⁻¹) :
    ∃ Φ : ↥(T ⊔ zpowers a) ≃* ↥(T' ⊔ zpowers a'),
      (∀ (t : G) (ht : t ∈ T),
        ((Φ ⟨t, (le_sup_left : T ≤ T ⊔ zpowers a) ht⟩ : ↥(T' ⊔ zpowers a')) : G') =
          ((e ⟨t, ht⟩ : ↥T') : G')) ∧
      ((Φ ⟨a, (le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a)⟩ :
        ↥(T' ⊔ zpowers a')) : G') = a' := by
  refine ⟨{ toFun := fun g => ⟨extFun e a a' g, extFun_mem e a a' g⟩
            invFun := fun g => ⟨extFun e.symm a' a g, extFun_mem e.symm a' a g⟩
            left_inv := fun g => Subtype.ext ?_
            right_inv := fun g => Subtype.ext ?_
            map_mul' := fun g h => Subtype.ext ?_ }, ?_, ?_⟩
  · exact extFun_symm_extFun e ha'T ((mem_sup_zpowers_iff haN ha2).mp g.2)
  · exact extFun_symm_extFun e.symm haT ((mem_sup_zpowers_iff ha'N ha'2).mp g.2)
  · exact extFun_mul e ha2 ha'2 haN hconj ((mem_sup_zpowers_iff haN ha2).mp g.2)
      ((mem_sup_zpowers_iff haN ha2).mp h.2)
  · intro t ht
    exact (extFun_of_mem e a a' ht).trans (extTotal_of_mem e ht)
  · exact extFun_self e a' haT

end CFSG.GH74.GLS.C3.Layer2
