module

public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup CFSG.Sporadic.RuSchreier

namespace FactsA

theorem card_centralizer_subtype {G : Type*} [Group G] (K : Subgroup G) (v : K) :
    Nat.card (centralizer ({v} : Set K)) =
      Nat.card (K ⊓ centralizer ({(v : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((x : K) : G), Subgroup.mem_inf.2 ⟨(x : K).2,
        mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2))⟩⟩
      invFun := fun y => ⟨⟨y, (Subgroup.mem_inf.1 y.2).1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mem_centralizer_conj_iff {Y : Type*} [Group Y] (c v x : Y) :
    x ∈ centralizer ({v} : Set Y) ↔ c * x * c⁻¹ ∈ centralizer ({c * v * c⁻¹} : Set Y) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc c * x * c⁻¹ * (c * v * c⁻¹) = c * (x * v) * c⁻¹ := by group
      _ = c * (v * x) * c⁻¹ := by rw [hx]
      _ = c * v * c⁻¹ * (c * x * c⁻¹) := by group
  · intro hx
    calc x * v = c⁻¹ * (c * x * c⁻¹ * (c * v * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * v * c⁻¹ * (c * x * c⁻¹)) * c := by rw [hx]
      _ = v * x := by group

theorem card_centralizer_eq_of_isConj {Y : Type*} [Group Y] {v w : Y} (h : IsConj v w) :
    Nat.card (centralizer ({v} : Set Y)) = Nat.card (centralizer ({w} : Set Y)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact Nat.card_congr
    ((MulAut.conj c).toEquiv.subtypeEquiv fun x => mem_centralizer_conj_iff c v x)

theorem card_centralizer_ruZ' :
    Nat.card (centralizer ({ruZ'} : Set ruP)) = 245760 := by
  rw [card_centralizer_subtype]
  have h : (ruP ⊓ centralizer ({(ruZ' : Equiv.Perm (Fin 4060))} : Set (Equiv.Perm (Fin 4060))) :
      Subgroup (Equiv.Perm (Fin 4060))) = ruC := ruC_eq_centralizer.symm
  rw [h, card_ruC]

theorem card_centralizer_ruA0' :
    Nat.card (centralizer ({ruA0'} : Set ruP)) = 116480 := by
  rw [card_centralizer_subtype]
  have h : (ruP ⊓ centralizer ({(ruA0' : Equiv.Perm (Fin 4060))} : Set (Equiv.Perm (Fin 4060))) :
      Subgroup (Equiv.Perm (Fin 4060))) = ruL := ruCentralizer_a
  rw [h, card_ruL]

theorem isConj_ruZ'_or_ruA0'
    {v : ruP} (hv : orderOf v = 2) :
    IsConj ruZ' v ∨ IsConj ruA0' v := by
  have hmem : (v : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} :=
    ⟨v.2, by rw [Subgroup.orderOf_coe]; exact hv⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with ⟨g, hg, hgv⟩ | ⟨g, hg, hgv⟩
  · exact Or.inl (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgv⟩)
  · exact Or.inr (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgv⟩)

theorem isConj_ruZ'_of_card
    {v : ruP} (hv : orderOf v = 2)
    (hc : Nat.card (centralizer ({v} : Set ruP)) = 245760) : IsConj ruZ' v := by
  rcases isConj_ruZ'_or_ruA0' hv with h | h
  · exact h
  · rw [← card_centralizer_eq_of_isConj h, card_centralizer_ruA0'] at hc
    exact absurd hc (by norm_num)

theorem isConj_ruA0'_of_card
    {v : ruP} (hv : orderOf v = 2)
    (hc : Nat.card (centralizer ({v} : Set ruP)) = 116480) : IsConj ruA0' v := by
  rcases isConj_ruZ'_or_ruA0' hv with h | h
  · rw [← card_centralizer_eq_of_isConj h, card_centralizer_ruZ'] at hc
    exact absurd hc (by norm_num)
  · exact h

theorem exists_sq_ruZ' :
    ∃ y : ruP, y ^ 2 = ruZ' := by
  obtain ⟨x, hx, hx2⟩ := Set.nonempty_of_ncard_ne_zero (s := {x | x ∈ ruP ∧ x ^ 2 = ruZ})
    (by rw [ncard_ruRoots]; norm_num)
  exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hx2)⟩

end FactsA

theorem ruP_card_eq :
    Nat.card ruP = 145926144000 :=
  card_ruP

theorem ruP_card_centralizer :
    ∀ v : ruP, orderOf v = 2 → Nat.card (centralizer ({v} : Set ruP)) = 245760 ∨
      Nat.card (centralizer ({v} : Set ruP)) = 116480 := by
  intro v hv
  rcases FactsA.isConj_ruZ'_or_ruA0' hv with h | h
  · rw [← FactsA.card_centralizer_eq_of_isConj h]
    exact Or.inl FactsA.card_centralizer_ruZ'
  · rw [← FactsA.card_centralizer_eq_of_isConj h]
    exact Or.inr FactsA.card_centralizer_ruA0'

theorem ruP_isConj_A :
    ∀ v w : ruP, orderOf v = 2 → orderOf w = 2 →
      Nat.card (centralizer ({v} : Set ruP)) = 245760 →
      Nat.card (centralizer ({w} : Set ruP)) = 245760 → IsConj v w :=
  fun _ _ hv hw hcv hcw =>
    (FactsA.isConj_ruZ'_of_card hv hcv).symm.trans (FactsA.isConj_ruZ'_of_card hw hcw)

theorem ruP_isConj_B :
    ∀ v w : ruP, orderOf v = 2 → orderOf w = 2 →
      Nat.card (centralizer ({v} : Set ruP)) = 116480 →
      Nat.card (centralizer ({w} : Set ruP)) = 116480 → IsConj v w :=
  fun _ _ hv hw hcv hcw =>
    (FactsA.isConj_ruA0'_of_card hv hcv).symm.trans (FactsA.isConj_ruA0'_of_card hw hcw)

theorem ruP_sq_A :
    ∀ v : ruP, orderOf v = 2 → Nat.card (centralizer ({v} : Set ruP)) = 245760 →
      ∃ y : ruP, y ^ 2 = v := by
  intro v hv hc
  obtain ⟨y, hy⟩ := FactsA.exists_sq_ruZ'
  obtain ⟨c, rfl⟩ := isConj_iff.1 (FactsA.isConj_ruZ'_of_card hv hc)
  exact ⟨c * y * c⁻¹, by rw [conj_pow, hy]⟩

end CFSG.EvenSporadicStandard.RuStd
