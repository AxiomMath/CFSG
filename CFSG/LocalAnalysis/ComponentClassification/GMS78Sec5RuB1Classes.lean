module

public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuOddCoreBase

public section

namespace CFSG.ComponentClassification.GMS78.RuB1

open Subgroup CFSG.Sporadic.RuSchreier CFSG.Blueprint


theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card (centralizer ({a} : Set A)) = Nat.card (centralizer ({e a} : Set B)) := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun c => ?_)
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem card_centralizer_subtype {Ω : Type*} [Group Ω] (P : Subgroup Ω) (y : P) :
    Nat.card (centralizer ({y} : Set P)) = Nat.card ↥(P ⊓ centralizer ({(y : Ω)} : Set Ω)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1, mem_inf.2 ⟨c.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2))⟩⟩
      invFun := fun c => ⟨⟨c.1, (mem_inf.1 c.2).1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2))⟩
      left_inv := fun c => rfl
      right_inv := fun c => rfl }

theorem ruP_involution_cases {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    (t ∈ ruZP ∧ Nat.card ↥(ruP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) = 245760) ∨
      (t ∈ ruAP ∧ Nat.card ↥(ruP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) = 116480) := by
  have hinv : t ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨ht, h2⟩
  rw [ruInvolutions_eq] at hinv
  rcases hinv with hZ | hA
  · refine Or.inl ⟨hZ, ?_⟩
    obtain ⟨g, hg, rfl⟩ := hZ
    rw [← Nat.card_congr (conjCentralizerEquiv hg ruZ).toEquiv, ← ruC_eq_centralizer, card_ruC]
  · refine Or.inr ⟨hA, ?_⟩
    obtain ⟨g, hg, rfl⟩ := hA
    rw [← Nat.card_congr (conjCentralizerEquiv hg ruA0).toEquiv, ruCentralizer_a, card_ruL]

theorem exists_conj_of_mem_conjSet {x t t' : Equiv.Perm (Fin 4060)} (ht : t ∈ conjSet ruP x)
    (ht' : t' ∈ conjSet ruP x) : ∃ g ∈ ruP, g * t * g⁻¹ = t' := by
  obtain ⟨g, hg, rfl⟩ := ht
  obtain ⟨h, hh, rfl⟩ := ht'
  exact ⟨h * g⁻¹, ruP.mul_mem hh (ruP.inv_mem hg), by group⟩

theorem ruP_involution_classes {t t' : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (ht' : t' ∈ ruP)
    (h2 : orderOf t = 2) (h2' : orderOf t' = 2) :
    (Nat.card ↥(ruP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) = 245760 ∨
      Nat.card ↥(ruP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) = 116480) ∧
    ((∃ g ∈ ruP, g * t * g⁻¹ = t') ↔
      Nat.card ↥(ruP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) =
        Nat.card ↥(ruP ⊓ centralizer ({t'} : Set (Equiv.Perm (Fin 4060))))) := by
  refine ⟨(ruP_involution_cases ht h2).imp (fun h => h.2) (fun h => h.2), ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨g, hg, rfl⟩
    exact Nat.card_congr (conjCentralizerEquiv hg t).toEquiv
  · rcases ruP_involution_cases ht h2 with ⟨hZ, h1⟩ | ⟨hA, h1⟩ <;>
      rcases ruP_involution_cases ht' h2' with ⟨hZ', h1'⟩ | ⟨hA', h1'⟩
    · exact exists_conj_of_mem_conjSet hZ hZ'
    · rw [h1, h1'] at hc
      norm_num at hc
    · rw [h1, h1'] at hc
      norm_num at hc
    · exact exists_conj_of_mem_conjSet hA hA'

theorem ru_involution_classes {K : Type*} [Group K] (hK : Nonempty (K ≃* NativeSporadic.Ru))
    {t t' : K} (ht : orderOf t = 2) (ht' : orderOf t' = 2) :
    (Nat.card (centralizer ({t} : Set K)) = 245760 ∨
      Nat.card (centralizer ({t} : Set K)) = 116480) ∧
    (IsConj t t' ↔
      Nat.card (centralizer ({t} : Set K)) = Nat.card (centralizer ({t'} : Set K))) := by
  obtain ⟨e₀⟩ := hK
  let E : K ≃* ruP := e₀.trans ruEquivP
  have hord : ∀ x : K, orderOf ((E x : ruP) : Equiv.Perm (Fin 4060)) = orderOf x := fun x => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hcard : ∀ x : K, Nat.card (centralizer ({x} : Set K)) =
      Nat.card ↥(ruP ⊓ centralizer ({((E x : ruP) : Equiv.Perm (Fin 4060))} :
        Set (Equiv.Perm (Fin 4060)))) := fun x => by
    rw [card_centralizer_mulEquiv E x, card_centralizer_subtype]
  obtain ⟨h1, h2⟩ := ruP_involution_classes (E t).2 (E t').2 (by rw [hord, ht])
    (by rw [hord, ht'])
  refine ⟨by rw [hcard]; exact h1, ?_⟩
  rw [hcard, hcard, ← h2, isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(E c : Equiv.Perm (Fin 4060)), (E c).2, by simp⟩
  · rintro ⟨g, hg, hgt⟩
    refine ⟨E.symm ⟨g, hg⟩, E.injective (Subtype.ext ?_)⟩
    simpa using hgt

theorem orderOf_mk_subgroup {G : Type*} [Group G] {L₀ : Subgroup G} {t : G} (htL : t ∈ L₀) :
    orderOf (⟨t, htL⟩ : L₀) = orderOf t :=
  Subgroup.orderOf_mk t htL

theorem ru_involution_classes_sub {G : Type*} [Group G] {L₀ : Subgroup G}
    (hL₀ : Nonempty (L₀ ≃* NativeSporadic.Ru)) {t t' : G} (htL : t ∈ L₀) (ht'L : t' ∈ L₀)
    (ht : orderOf t = 2) (ht' : orderOf t' = 2) :
    (Nat.card ↥(L₀ ⊓ centralizer ({t} : Set G)) = 245760 ∨
      Nat.card ↥(L₀ ⊓ centralizer ({t} : Set G)) = 116480) ∧
    ((∃ c ∈ L₀, c * t * c⁻¹ = t') ↔
      Nat.card ↥(L₀ ⊓ centralizer ({t} : Set G)) =
        Nat.card ↥(L₀ ⊓ centralizer ({t'} : Set G))) := by
  obtain ⟨h1, h2⟩ := ru_involution_classes hL₀ (t := ⟨t, htL⟩) (t' := ⟨t', ht'L⟩)
    (by rw [orderOf_mk_subgroup, ht]) (by rw [orderOf_mk_subgroup, ht'])
  rw [card_centralizer_subtype, card_centralizer_subtype] at h2
  rw [card_centralizer_subtype] at h1
  refine ⟨h1, ?_⟩
  rw [← h2, isConj_iff]
  constructor
  · rintro ⟨c, hc, hct⟩
    exact ⟨⟨c, hc⟩, Subtype.ext hct⟩
  · rintro ⟨c, hct⟩
    exact ⟨c, c.2, congrArg Subtype.val hct⟩

end CFSG.ComponentClassification.GMS78.RuB1
