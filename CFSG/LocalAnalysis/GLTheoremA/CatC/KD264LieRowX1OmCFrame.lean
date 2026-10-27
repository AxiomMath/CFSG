module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCBasic
public import CFSG.Open.LocalVocabulary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open
open scoped commutatorElement

section Cards

variable {X : Type*} [Group X]

theorem card_sup_mul_card_inf_of_normal' (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc _ hAN, hc _ hB] at h
  exact h

end Cards

section Frame

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)

@[expose] def PairPerp (p q : V × V) : Prop :=
  polar Q p.1 q.1 = 0 ∧ polar Q p.1 q.2 = 0 ∧ polar Q p.2 q.1 = 0 ∧ polar Q p.2 q.2 = 0

variable {Q}

theorem PairPerp.symm {p q : V × V} (h : PairPerp Q p q) : PairPerp Q q p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [polar_comm]; exact h1
  · rw [polar_comm]; exact h3
  · rw [polar_comm]; exact h2
  · rw [polar_comm]; exact h4

variable (Q)

structure IsFrame (l : List (V × V)) : Prop where
  pair : ∀ p ∈ l, MinusPair Q p.1 p.2
  perp : l.Pairwise (PairPerp Q)

variable {Q}

theorem IsFrame.nil : IsFrame Q ([] : List (V × V)) :=
  ⟨fun _ h => absurd h (List.not_mem_nil), List.Pairwise.nil⟩

theorem isFrame_cons {p : V × V} {l : List (V × V)} :
    IsFrame Q (p :: l) ↔ MinusPair Q p.1 p.2 ∧ (∀ q ∈ l, PairPerp Q p q) ∧ IsFrame Q l := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [List.pairwise_cons] at h2
    exact ⟨h1 p (List.mem_cons_self), h2.1, fun q hq => h1 q (List.mem_cons_of_mem _ hq), h2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun q hq => ?_, List.pairwise_cons.2 ⟨h2, h4⟩⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h1
    · exact h3 q hq

theorem IsFrame.cons {p : V × V} {l : List (V × V)} (hp : MinusPair Q p.1 p.2)
    (hperp : ∀ q ∈ l, PairPerp Q p q) (hl : IsFrame Q l) : IsFrame Q (p :: l) :=
  isFrame_cons.2 ⟨hp, hperp, hl⟩

theorem IsFrame.tail {p : V × V} {l : List (V × V)} (h : IsFrame Q (p :: l)) : IsFrame Q l :=
  (isFrame_cons.1 h).2.2

theorem IsFrame.sublist {l l' : List (V × V)} (h : IsFrame Q l) (hs : l'.Sublist l) :
    IsFrame Q l' :=
  ⟨fun p hp => h.pair p (hs.subset hp), h.perp.sublist hs⟩

theorem IsFrame.perp_of_mem_of_ne {l : List (V × V)} (h : IsFrame Q l) {p q : V × V} (hp : p ∈ l)
    (hq : q ∈ l) (hne : p ≠ q) : PairPerp Q p q :=
  haveI : Std.Symm (PairPerp Q) := ⟨fun _ _ h => PairPerp.symm h⟩
  h.perp.forall hp hq hne

theorem MinusPair.ne {a b : V} (h : MinusPair Q a b) : a ≠ b := by
  rintro rfl
  have h1 := h.ab
  rw [polar_self_zero] at h1
  exact zero_ne_one h1

end Frame

section Torus

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)

@[expose] def rotSet (l : List (V × V)) : Set (V ≃ₗ[ZMod 2] V) :=
  {g | ∃ p ∈ l, g = rot Q p.1 p.2}

@[expose] def torus (l : List (V × V)) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  Subgroup.closure (rotSet Q l)

variable {Q}

theorem rotSet_cons (p : V × V) (l : List (V × V)) :
    rotSet Q (p :: l) = insert (rot Q p.1 p.2) (rotSet Q l) := by
  ext g
  simp only [rotSet, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨q, hq | hq, rfl⟩
    · exact Or.inl (by rw [hq])
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact ⟨p, Or.inl rfl, rfl⟩
    · exact ⟨q, Or.inr hq, rfl⟩

theorem torus_nil : torus Q ([] : List (V × V)) = ⊥ := by
  have : rotSet Q ([] : List (V × V)) = ∅ := by
    ext g
    simp [rotSet]
  rw [torus, this, Subgroup.closure_empty]

theorem torus_cons (p : V × V) (l : List (V × V)) :
    torus Q (p :: l) = Subgroup.zpowers (rot Q p.1 p.2) ⊔ torus Q l := by
  rw [torus, rotSet_cons, ← Set.singleton_union, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure]
  rfl

theorem rot_mem_torus {l : List (V × V)} {p : V × V} (hp : p ∈ l) : rot Q p.1 p.2 ∈ torus Q l :=
  Subgroup.subset_closure ⟨p, hp, rfl⟩

theorem torus_le_orthogonalGroup (l : List (V × V)) :
    torus Q l ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (Subgroup.closure_le _).2 (by
    rintro g ⟨p, -, rfl⟩
    exact rot_mem_orthogonalGroup p.1 p.2)

theorem torus_le_commutator {l : List (V × V)} (hl : IsFrame Q l) :
    torus Q l ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  (Subgroup.closure_le _).2 (by
    rintro g ⟨p, hp, rfl⟩
    exact rot_mem_commutator (hl.pair p hp))

theorem rotSet_pairwise_commute {l : List (V × V)} (hl : IsFrame Q l) :
    (rotSet Q l).Pairwise Commute := by
  rintro g ⟨p, hp, rfl⟩ h ⟨q, hq, rfl⟩ hne
  have hpq : p ≠ q := fun h => hne (by rw [h])
  obtain ⟨h1, h2, h3, h4⟩ := hl.perp_of_mem_of_ne hp hq hpq
  exact rot_commute_of_perp h1 h2 h3 h4

theorem torus_isMulCommutative {l : List (V × V)} (hl : IsFrame Q l) :
    IsMulCommutative (torus Q l) :=
  Subgroup.isMulCommutative_closure (rotSet_pairwise_commute hl)

theorem torus_commute {l : List (V × V)} (hl : IsFrame Q l) {x y : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ torus Q l) (hy : y ∈ torus Q l) : Commute x y := by
  haveI := torus_isMulCommutative hl
  exact congrArg Subtype.val ((torus_isMulCommutative hl).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem torus_pow_three {l : List (V × V)} (hl : IsFrame Q l) :
    ∀ x ∈ torus Q l, x ^ 3 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact rot_pow_three (hl.pair p hp)
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(torus_commute hl hx hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem torus_isElemAbelian {l : List (V × V)} (hl : IsFrame Q l) : IsElemAbelian 3 (torus Q l) :=
  ⟨torus_isMulCommutative hl, torus_pow_three hl⟩

theorem torus_fixes {l : List (V × V)} (hl : IsFrame Q l) {x : V}
    (hx : ∀ p ∈ l, polar Q x p.1 = 0 ∧ polar Q x p.2 = 0) : ∀ t ∈ torus Q l, t x = x := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨p, hp, rfl⟩ := ht
    exact rot_apply_of_perp (hl.pair p hp) (hx p hp).1 (hx p hp).2
  | one => rfl
  | mul s t hs ht ihs iht => rw [LinearEquiv.mul_apply, iht, ihs]
  | inv t ht iht =>
    show t.symm x = x
    exact (LinearEquiv.symm_apply_eq t).2 iht.symm

theorem torus_commute_rot {l : List (V × V)} (c d : V)
    (hperp : ∀ p ∈ l, polar Q p.1 c = 0 ∧ polar Q p.1 d = 0 ∧ polar Q p.2 c = 0 ∧
      polar Q p.2 d = 0) : ∀ t ∈ torus Q l, Commute t (rot Q c d) := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨p, hp, rfl⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := hperp p hp
    exact rot_commute_of_perp h1 h2 h3 h4
  | one => exact Commute.one_left _
  | mul s t hs ht ihs iht => exact ihs.mul_left iht
  | inv t ht iht => exact iht.inv_left

scoped instance finite_linearEquiv [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) (fun _ _ h => LinearEquiv.ext (congrFun h))

theorem card_torus [Finite V] {l : List (V × V)} (hl : IsFrame Q l) :
    Nat.card (torus Q l) = 3 ^ l.length := by
  induction l with
  | nil => simp [torus_nil]
  | cons p l ih =>
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set A := torus Q l with hA
    set ρ := rot Q p.1 p.2 with hρ
    have hcomm : ∀ t ∈ A, Commute t ρ := fun t ht =>
      torus_commute_rot p.1 p.2 (fun q hq => (hperp q hq).symm) t ht
    have hB : Subgroup.zpowers ρ ≤ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod 2] V)) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro h
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hc : ∀ (k : ℤ), ∀ a ∈ A, ρ ^ k * a * (ρ ^ k)⁻¹ = a := fun k a ha => by
        have := (hcomm a ha).symm.zpow_left k
        rw [mul_inv_eq_iff_eq_mul]
        exact this.eq
      refine ⟨fun hh => by rw [hc n h hh]; exact hh, fun hh => ?_⟩
      have h2 := hc (-n) _ hh
      rw [zpow_neg, inv_inv] at h2
      have h3 : (ρ ^ n)⁻¹ * (ρ ^ n * h * (ρ ^ n)⁻¹) * ρ ^ n = h := by group
      rw [h3] at h2
      rw [h2]
      exact hh
    have hne : ρ ≠ 1 := by
      intro h1
      have := rot_apply_left hp
      rw [← hρ, h1] at this
      exact hp.ne this
    have hord : orderOf ρ = 3 := orderOf_eq_prime (rot_pow_three hp) hne
    have hcardB : Nat.card (Subgroup.zpowers ρ) = 3 := by rw [Nat.card_zpowers, hord]
    have hρA : ρ ∉ A := by
      intro hρA
      have hfix := torus_fixes hl' (x := p.1) (fun q hq => ⟨(hperp q hq).1, (hperp q hq).2.1⟩) ρ hρA
      rw [hρ, rot_apply_left hp] at hfix
      exact hp.ne hfix.symm
    have hinf : Nat.card (A ⊓ Subgroup.zpowers ρ : Subgroup (V ≃ₗ[ZMod 2] V)) = 1 := by
      have hdvd : Nat.card (A ⊓ Subgroup.zpowers ρ : Subgroup (V ≃ₗ[ZMod 2] V)) ∣ 3 := by
        rw [← hcardB]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact h1
      · exfalso
        have heq : A ⊓ Subgroup.zpowers ρ = Subgroup.zpowers ρ :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcardB])
        have : ρ ∈ A ⊓ Subgroup.zpowers ρ := by rw [heq]; exact Subgroup.mem_zpowers ρ
        exact hρA this.1
    have h := card_sup_mul_card_inf_of_le_normalizer' hB
    rw [hinf, hcardB, mul_one, ih hl'] at h
    rw [torus_cons, sup_comm, h, List.length_cons, pow_succ]

end Torus

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
