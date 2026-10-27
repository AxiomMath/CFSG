module

import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open
open scoped commutatorElement

namespace Lemma34

section Quasisimple

variable {G : Type*} [Group G] {A : Subgroup G}

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  push Not at hab
  have hsimple : IsSimpleGroup (Q ⧸ center Q) := h.2
  have : IsMulCommutative (Q ⧸ center Q) := ⟨⟨hab⟩⟩
  have : Nontrivial (Q ⧸ center Q) := hsimple.toNontrivial
  have : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ center Q)
      (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (Q ⧸ center Q) inferInstance

theorem commutator_self_eq (hq : CFSG.Open.IsQuasisimple A) : ⁅A, A⁆ = A :=
  isPerfect_iff.mp ⟨hq.1⟩

theorem exists_not_commute (hq : CFSG.Open.IsQuasisimple A) :
    ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_of_open hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, a.2, b, b.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

theorem not_le_centralizer_self (hq : CFSG.Open.IsQuasisimple A) :
    ¬ A ≤ centralizer (A : Set G) := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute hq
  exact hab (mem_centralizer_iff.mp (h hb) a ha)

theorem le_or_inf_le_centralizer (hq : CFSG.Open.IsQuasisimple A) {X : Subgroup G}
    (hAX : A ≤ normalizer (X : Set G)) : A ≤ X ∨ A ⊓ X ≤ centralizer (A : Set G) := by
  have hn : (X.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.mp (hAX g.2) n).mp hn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_of_open hq) hn with h | h
  · left
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ X.subgroupOf A := h ▸ mem_top _
    exact this
  · right
    intro y hy
    rw [mem_centralizer_iff]
    intro a ha
    have hyc := mem_center_iff.mp (h (show (⟨y, hy.1⟩ : A) ∈ X.subgroupOf A from hy.2)) ⟨a, ha⟩
    simpa using congrArg Subtype.val hyc

theorem mem_centralizer_of_mem (hq : CFSG.Open.IsQuasisimple A) {X : Subgroup G}
    (hAX : A ≤ normalizer (X : Set G)) (hcen : A ⊓ X ≤ centralizer (A : Set G)) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxX : x ∈ X) : x ∈ centralizer (A : Set G) := by
  have hperf : Group.IsPerfect A := ⟨hq.1⟩
  have hZ : zpowers x ≤ X ⊓ normalizer (A : Set G) := zpowers_le.mpr ⟨hxX, hxA⟩
  have h1 : ⁅A, zpowers x⁆ ≤ A ⊓ X := by
    rw [commutator_le]
    intro a ha z hz
    have hzX := (mem_inf.mp (hZ hz)).1
    have hzA := (mem_inf.mp (hZ hz)).2
    rw [commutatorElement_def]
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have : z * a⁻¹ * z⁻¹ ∈ A := (mem_normalizer_iff.mp hzA a⁻¹).mp (inv_mem ha)
      simpa [mul_assoc] using mul_mem ha this
    · have : a * z * a⁻¹ ∈ X := (mem_normalizer_iff.mp (hAX ha) z).mp hzX
      exact mul_mem this (inv_mem hzX)
  have h2 : ⁅⁅A, zpowers x⁆, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact h1.trans hcen
  have h3 := CFSG.LocalCores.perfect_double_commutator hperf h2
  rw [commutator_eq_bot_iff_le_centralizer] at h3
  rw [mem_centralizer_iff]
  intro a ha
  exact (mem_centralizer_iff.mp (h3 ha) x (mem_zpowers x)).symm

end Quasisimple

section Tight

variable {G : Type*} [Group G] {A : Subgroup G}

theorem mem_normalizer_of_dvd (hA : standardComponentIsStandard A) {P : Subgroup G} {g : G}
    (hPK : P ≤ centralizer (A : Set G))
    (hPg : P ≤ (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom)
    (hP : 2 ∣ Nat.card P) : g ∈ normalizer (A : Set G) :=
  hA.2.2.2.1 ▸ StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_le hA.2.2.1 hPK hPg hP

theorem mem_normalizer_of_commute (hA : standardComponentIsStandard A) {u g : G}
    (hu : u ∈ centralizer (A : Set G)) (hu2 : orderOf u = 2) (hg : g * u = u * g) :
    g ∈ normalizer (A : Set G) :=
  hA.mem_normalizer_of_commute hu hu2 hg

end Tight

section Hyp31

theorem eq_bot_of_normal_le_centralizer {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (h : Hyp31 A) {M : Subgroup G} (hM : M.Normal) (hMK : M ≤ centralizer (A : Set G)) :
    M = ⊥ := by
  by_contra hM1
  have heven : 2 ∣ Nat.card M := by
    by_contra hodd
    have hodd' : Odd (Nat.card M) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    have hle : M ≤ standardComponentOddCore G := le_sSup ⟨hM, hodd'⟩
    rw [h.oddCore, le_bot_iff] at hle
    exact hM1 hle
  apply h.not_normal
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  refine mem_normalizer_of_dvd h.standard hMK (fun x hx => ?_) heven
  refine ⟨g⁻¹ * x * g, hMK (hM.conj_mem' x hx g), ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Hyp31

section Involution

variable {G : Type*} [Group G] [Finite G]

theorem exists_involution_commute {X : Subgroup G} {u : G} (hu : u * u = 1)
    (huX : u ∈ normalizer (X : Set G)) (heven : Even (Nat.card X)) :
    ∃ y ∈ X, orderOf y = 2 ∧ y * u = u * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype X := Fintype.ofFinite X
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let f : Function.End X := fun x => ⟨u * x * u⁻¹, (mem_normalizer_iff.mp huX x).mp x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    apply Subtype.ext
    change u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    rw [hui]
    calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu, one_mul, mul_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  set C : Subgroup G := X ⊓ centralizer ({u} : Set G)
  let e : Function.fixedPoints f ≃ C :=
    { toFun := fun x => ⟨x.1, mem_inf.mpr ⟨x.1.2, by
        rw [mem_centralizer_singleton_iff]
        have h1 : u * (x.1 : G) * u⁻¹ = x.1 := congrArg Subtype.val x.2
        calc (x.1 : G) * u = u * x.1 * u⁻¹ * u := by rw [h1]
          _ = u * x.1 := by group⟩⟩
      invFun := fun c => ⟨⟨c, (mem_inf.mp c.2).1⟩, by
        apply Subtype.ext
        change u * (c : G) * u⁻¹ = c
        have h1 : (c : G) * u = u * c := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
        rw [← h1, mul_inv_cancel_right]⟩
      left_inv := fun x => rfl
      right_inv := fun c => rfl }
  have hCeven : 2 ∣ Nat.card C := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    have h2 : 2 ∣ Fintype.card X := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp heven
    convert (hmod.dvd_iff (dvd_refl 2)).mp h2
  obtain ⟨⟨y, hyC⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hCeven
  refine ⟨y, (mem_inf.mp hyC).1, by rwa [Subgroup.orderOf_mk] at hy, ?_⟩
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp hyC).2

end Involution

section Perfect

variable {G : Type*} [Group G]

theorem le_of_le_sup {A H M : Subgroup G} (hA : ⁅A, A⁆ = A) (hAH : A ≤ normalizer (H : Set G))
    (hMH : M ≤ normalizer (H : Set G)) (hMA : M ≤ centralizer (A : Set G)) (hle : A ≤ H ⊔ M) :
    A ≤ H := by
  have hsup : H ⊔ M = closure ((H : Set G) ∪ M) := by
    rw [Subgroup.closure_union, closure_eq, closure_eq]
  have key : ∀ x ∈ H ⊔ M, x ∈ normalizer (H : Set G) ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ H := by
    intro x hx
    rw [hsup] at hx
    induction hx using closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · refine ⟨le_normalizer hy, fun a ha => ?_⟩
        rw [commutatorElement_def]
        exact mul_mem ((mem_normalizer_iff.mp (hAH ha) y).mp hy) (inv_mem hy)
      · refine ⟨hMH hy, fun a ha => ?_⟩
        have hya : a * y = y * a := mem_centralizer_iff.mp (hMA hy) a ha
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hya]
        exact one_mem _
    | one =>
      exact ⟨one_mem _, fun a _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
    | mul y z _ _ hy hz =>
      refine ⟨mul_mem hy.1 hz.1, fun a ha => ?_⟩
      have heq : ⁅a, y * z⁆ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact mul_mem (hy.2 a ha) ((mem_normalizer_iff.mp hy.1 _).mp (hz.2 a ha))
    | inv y _ hy =>
      refine ⟨inv_mem hy.1, fun a ha => ?_⟩
      have heq : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact (mem_normalizer_iff.mp (inv_mem hy.1) _).mp (inv_mem (hy.2 a ha))
  rw [← hA]
  refine (commutator_mono le_rfl hle).trans ?_
  rw [commutator_le]
  intro a ha x hx
  exact (key x hx).2 a ha

end Perfect

section Conjugates

variable {G : Type*} [Group G]

abbrev conj (L : Subgroup G) (g : G) : Subgroup G :=
  L.map (MulAut.conj g).toMonoidHom

theorem mem_conj_iff {L : Subgroup G} {g x : G} : x ∈ conj L g ↔ g⁻¹ * x * g ∈ L := by
  rw [conj, mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_conj {L : Subgroup G} {g x : G} (hx : x ∈ L) : g * x * g⁻¹ ∈ conj L g :=
  mem_conj_iff.mpr (by simpa [mul_assoc] using hx)

theorem conj_conj (L : Subgroup G) (g h : G) : conj (conj L h) g = conj L (g * h) := by
  ext x
  simp only [mem_conj_iff, mul_inv_rev, mul_assoc]

theorem conj_one (L : Subgroup G) : conj L 1 = L := by
  ext x
  simp

theorem conj_eq_self_iff {L : Subgroup G} {g : G} : conj L g = L ↔ g ∈ normalizer (L : Set G) := by
  constructor
  · intro h
    rw [mem_normalizer_iff]
    intro x
    have hx := @mem_conj_iff _ _ L g (g * x * g⁻¹)
    rw [h, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hx
    exact hx.symm
  · intro hg
    ext x
    rw [mem_conj_iff]
    have := mem_normalizer_iff.mp (inv_mem hg) x
    rw [inv_inv] at this
    exact this.symm

theorem card_conj (L : Subgroup G) (g : G) : Nat.card (conj L g) = Nat.card L :=
  card_map_of_injective (MulAut.conj g).injective

theorem isSimpleGroup_conj (L : Subgroup G) [IsSimpleGroup L] (g : G) :
    IsSimpleGroup (conj L g) :=
  MulEquiv.isSimpleGroup (L.equivMapOfInjective _ (MulAut.conj g).injective).symm

theorem conj_le_of_normal {L N : Subgroup G} (hN : N.Normal) (hLN : L ≤ N) (g : G) :
    conj L g ≤ N := by
  intro x hx
  have h := hN.conj_mem _ (hLN (mem_conj_iff.mp hx)) g
  simpa [mul_assoc] using h

theorem le_normalizer_conj {L N : Subgroup G} (hN : N.Normal) (hNL : N ≤ normalizer (L : Set G))
    (g : G) : N ≤ normalizer (conj L g : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  rw [mem_conj_iff, mem_conj_iff]
  have hm : g⁻¹ * n * g ∈ N := hN.conj_mem' n hn g
  have h := mem_normalizer_iff.mp (hNL hm) (g⁻¹ * x * g)
  have heq : g⁻¹ * n * g * (g⁻¹ * x * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * x * n⁻¹) * g := by
    group
  rw [heq] at h
  exact h

theorem normalClosure_le_of_forall {L X : Subgroup G} (h : ∀ g : G, conj L g ≤ X) :
    normalClosure (L : Set G) ≤ X := by
  rw [normalClosure, closure_le]
  intro c hc
  obtain ⟨l, hl, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hc
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  exact h g (conj_mem_conj hl)

theorem inf_eq_bot_of_isSimpleGroup {X Y : Subgroup G} [IsSimpleGroup X] [IsSimpleGroup Y]
    (hXY : X ≤ normalizer (Y : Set G)) (hYX : Y ≤ normalizer (X : Set G)) (hne : X ≠ Y) :
    X ⊓ Y = ⊥ := by
  have h1 : ((X ⊓ Y).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨hnX, hnY⟩ := mem_inf.mp hn
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simpa using mul_mem (mul_mem g.2 hnX) (inv_mem g.2)
    · simpa using (mem_normalizer_iff.mp (hXY g.2) n).mp hnY
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X ⊓ Y).subgroupOf X) with h | h
  · rw [subgroupOf_eq_bot] at h
    exact le_bot_iff.mp (h le_rfl inf_le_left)
  · rw [subgroupOf_eq_top] at h
    have hXle : X ≤ Y := h.trans inf_le_right
    have h2 : (X.subgroupOf Y).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.mp (hYX g.2) n).mp hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf Y) with h' | h'
    · exfalso
      rw [subgroupOf_eq_bot] at h'
      have hbot : X = ⊥ := le_bot_iff.mp (h' le_rfl hXle)
      have : Nontrivial X := IsSimpleGroup.toNontrivial
      exact ((nontrivial_iff_ne_bot X).mp this) hbot
    · rw [subgroupOf_eq_top] at h'
      exact absurd (le_antisymm hXle h') hne

theorem commute_of_inf_eq_bot {X Y : Subgroup G} (hXY : X ≤ normalizer (Y : Set G))
    (hYX : Y ≤ normalizer (X : Set G)) (h : X ⊓ Y = ⊥) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) :
    x * y = y * x := by
  have h1 : ⁅x, y⁆ ∈ X := by
    rw [commutatorElement_def]
    have : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp (hYX hy) x⁻¹).mp (inv_mem hx)
    simpa [mul_assoc] using mul_mem hx this
  have h2 : ⁅x, y⁆ ∈ Y := by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hXY hx) y).mp hy) (inv_mem hy)
  have : ⁅x, y⁆ = 1 := by
    rw [← mem_bot, ← h]
    exact mem_inf.mpr ⟨h1, h2⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem le_normalizer_sup {A X Y : Subgroup G} (hX : A ≤ normalizer (X : Set G))
    (hY : A ≤ normalizer (Y : Set G)) : A ≤ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  intro a ha
  rw [← conj_eq_self_iff, conj, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conj_eq_self_iff.mpr (hX ha)) (conj_eq_self_iff.mpr (hY ha))

theorem le_normalizer_of_normal_subgroupOf {L N : Subgroup G} (hLN : L ≤ N)
    (h : (L.subgroupOf N).Normal) : N ≤ normalizer (L : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  have hc := (normal_subgroupOf_iff hLN).mp h
  refine ⟨fun hx => hc x n hx hn, fun hx => ?_⟩
  have := hc _ n⁻¹ hx (inv_mem hn)
  simpa [mul_assoc] using this

end Conjugates

end Lemma34

end CFSG.ComponentClassification.AS76b
