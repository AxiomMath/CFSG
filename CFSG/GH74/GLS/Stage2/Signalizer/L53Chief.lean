module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem stab_mul {X Y : Subgroup M} (hY : Y.Normal) {a b : M} (ha : ∀ x ∈ X, ⁅x, a⁆ ∈ Y)
    (hb : ∀ x ∈ X, ⁅x, b⁆ ∈ Y) : ∀ x ∈ X, ⁅x, a * b⁆ ∈ Y := by
  intro x hx
  have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Y.mul_mem (ha x hx) (hY.conj_mem _ (hb x hx) a)

theorem stab_inv {X Y : Subgroup M} (hY : Y.Normal) {a : M} (ha : ∀ x ∈ X, ⁅x, a⁆ ∈ Y) :
    ∀ x ∈ X, ⁅x, a⁻¹⁆ ∈ Y := by
  intro x hx
  have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
    simp only [commutatorElement_def]; group
  rw [e]
  have := hY.conj_mem _ (Y.inv_mem (ha x hx)) a⁻¹
  simpa using this

@[expose] def stabSec (X Y : Subgroup M) (hY : Y.Normal) : Subgroup M where
  carrier := {m | ∀ x ∈ X, ⁅x, m⁆ ∈ Y}
  mul_mem' := fun ha hb => stab_mul hY ha hb
  one_mem' := by intro x _; simp
  inv_mem' := fun ha => stab_inv hY ha

theorem mem_stabSec {X Y : Subgroup M} {hY : Y.Normal} {m : M} :
    m ∈ stabSec X Y hY ↔ ∀ x ∈ X, ⁅x, m⁆ ∈ Y := Iff.rfl

theorem comm_zpowers_le_iff {X Y : Subgroup M} (hY : Y.Normal) {g : M} :
    ⁅X, zpowers g⁆ ≤ Y ↔ ∀ x ∈ X, ⁅x, g⁆ ∈ Y := by
  constructor
  · intro h x hx
    exact h (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers g))
  · intro h
    rw [Subgroup.commutator_le]
    intro x hx m hm
    have hg : g ∈ stabSec X Y hY := h
    exact (Subgroup.zpowers_le.mpr hg) hm x hx

@[expose] def IsChiefPair (X Y : Subgroup M) : Prop :=
  X.Normal ∧ Y.Normal ∧ Y < X ∧ ∀ Z : Subgroup M, Z.Normal → Y ≤ Z → Z ≤ X → Z = Y ∨ Z = X

theorem exists_chief_below [Finite M] {N : Subgroup M} (hN : N.Normal) (hne : N ≠ ⊥) :
    ∃ Y : Subgroup M, IsChiefPair N Y := by
  have hS : {Z : Subgroup M | Z.Normal ∧ Z < N}.Nonempty :=
    ⟨⊥, inferInstance, bot_lt_iff_ne_bot.mpr hne⟩
  obtain ⟨Y, hY⟩ := (Set.toFinite {Z : Subgroup M | Z.Normal ∧ Z < N}).exists_maximal hS
  refine ⟨Y, hN, hY.prop.1, hY.prop.2, fun Z hZ hYZ hZN => ?_⟩
  by_cases hZN' : Z = N
  · exact Or.inr hZN'
  · left
    exact hY.eq_of_ge ⟨hZ, lt_of_le_of_ne hZN hZN'⟩ hYZ

@[expose] def stabAll (X : Subgroup M) : Subgroup M where
  carrier := {m | ∀ X' Y' : Subgroup M, IsChiefPair X' Y' → X' ≤ X → ∀ x ∈ X', ⁅x, m⁆ ∈ Y'}
  mul_mem' := fun ha hb X' Y' hc hX' =>
    stab_mul hc.2.1 (fun x hx => ha X' Y' hc hX' x hx) (fun x hx => hb X' Y' hc hX' x hx)
  one_mem' := by intro X' Y' _ _ x _; simp
  inv_mem' := fun ha X' Y' hc hX' =>
    stab_inv hc.2.1 (fun x hx => ha X' Y' hc hX' x hx)

theorem mem_stabAll {X : Subgroup M} {m : M} :
    m ∈ stabAll X ↔
      ∀ X' Y' : Subgroup M, IsChiefPair X' Y' → X' ≤ X → ∀ x ∈ X', ⁅x, m⁆ ∈ Y' := Iff.rfl

instance stabAll_normal (X : Subgroup M) : (stabAll X).Normal where
  conj_mem := by
    intro m hm n X' Y' hc hX' x hx
    have e : ⁅x, n * m * n⁻¹⁆ = n * ⁅n⁻¹ * x * n, m⁆ * n⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : n⁻¹ * x * n ∈ X' := by
      have := hc.1.conj_mem x hx n⁻¹
      simpa using this
    exact hc.2.1.conj_mem _ (hm X' Y' hc hX' _ h1) n

theorem centralizes_of_stabAll [Finite M] {p : ℕ} [Fact p.Prime] {X : Subgroup M} (hXn : X.Normal)
    (hX : IsPGroup p ↥X) {c : M} (hc : ¬ p ∣ orderOf c) (hcs : c ∈ stabAll X) :
    ∀ x ∈ X, c * x * c⁻¹ = x := by
  have key : ∀ N : Subgroup M, N.Normal → N ≤ X → ∀ x ∈ N, c * x * c⁻¹ = x := by
    intro N
    induction N using WellFoundedLT.induction with
    | _ N ih =>
      intro hNn hNX
      by_cases hN : N = ⊥
      · intro x hx
        rw [hN, Subgroup.mem_bot] at hx
        rw [hx]; group
      · obtain ⟨Y, hY⟩ := exists_chief_below hNn hN
        have hYN : Y < N := hY.2.2.1
        have hcY : ∀ y ∈ Y, c * y * c⁻¹ = y := ih Y hYN hY.2.1 (hYN.le.trans hNX)
        refine centralizes_of_coprime (hX.to_le hNX) hYN.le hc hcY ?_
        intro x hx
        have h := hcs N Y hY hNX x⁻¹ (N.inv_mem hx)
        have e : ⁅x⁻¹, c⁆ = x⁻¹ * (c * x * c⁻¹) := by
          simp only [commutatorElement_def]; group
        rwa [e] at h
  exact key X hXn le_rfl

structure Setup (p : ℕ) (T A : Subgroup M) : Prop where
  normalT : T.Normal
  pT : IsPGroup p ↥T
  maxT : ∀ N : Subgroup M, N.Normal → IsPGroup p ↥N → N ≤ T
  centT : centralizer (T : Set M) ≤ T
  normalA : A.Normal
  leT : A ≤ T
  commTA : ⁅T, A⁆ ≤ A ⊓ centralizer (A : Set M)
  centTA : T ⊓ centralizer (A : Set M) ≤ A

namespace Setup

variable {p : ℕ} [Fact p.Prime] {T A : Subgroup M}

omit [Fact p.Prime] in
theorem normal_Z (hS : Setup p T A) : (A ⊓ centralizer (A : Set M)).Normal := by
  have := hS.normalA
  have : (centralizer (A : Set M)).Normal := Subgroup.normal_centralizer
  infer_instance

theorem eq_one_of_centralizes (hS : Setup p T A) {c : M} (hc : ¬ p ∣ orderOf c)
    (hcA : ∀ a ∈ A, c * a * c⁻¹ = a) : c = 1 := by
  have := hS.normalT
  have hZT : A ⊓ centralizer (A : Set M) ≤ T := inf_le_left.trans hS.leT
  have hcT : ∀ t ∈ T, c * t * c⁻¹ = t := by
    refine centralizes_of_coprime hS.pT hZT hc (fun y hy => hcA y hy.1) ?_
    intro t ht
    set u : M := t⁻¹ * (c * t * c⁻¹) with hu
    have huT : u ∈ T := T.mul_mem (T.inv_mem ht) (hS.normalT.conj_mem t ht c)
    have huC : u ∈ centralizer (A : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hw : ⁅t, a⁆ ∈ A ⊓ centralizer (A : Set M) :=
        hS.commTA (Subgroup.commutator_mem_commutator ht ha)
      have h1 : c * ⁅t, a⁆ * c⁻¹ = ⁅t, a⁆ := hcA _ hw.1
      have h2 : c * ⁅t, a⁆ * c⁻¹ = ⁅c * t * c⁻¹, a⁆ := by
        have ha' := hcA a ha
        have : c * ⁅t, a⁆ * c⁻¹ = ⁅c * t * c⁻¹, c * a * c⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [this, ha']
      have h3 : ⁅c * t * c⁻¹, a⁆ = ⁅t, a⁆ := h2.symm.trans h1
      simp only [commutatorElement_def] at h3
      have h4 : (c * t * c⁻¹) * a * (c * t * c⁻¹)⁻¹ = t * a * t⁻¹ := by
        have := congrArg (fun z => z * a) h3
        simpa [mul_assoc] using this
      have h5 : a * u = u * a := by
        rw [hu]
        have := congrArg (fun z => t⁻¹ * z * (c * t * c⁻¹)) h4
        have e : t⁻¹ * ((c * t * c⁻¹) * a * (c * t * c⁻¹)⁻¹) * (c * t * c⁻¹) =
            (t⁻¹ * (c * t * c⁻¹)) * a := by group
        have e2 : t⁻¹ * (t * a * t⁻¹) * (c * t * c⁻¹) = a * (t⁻¹ * (c * t * c⁻¹)) := by group
        rw [e, e2] at this
        exact this.symm
      exact h5
    have huA : u ∈ A := hS.centTA ⟨huT, huC⟩
    exact ⟨huA, huC⟩
  have hcC : c ∈ centralizer (T : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := hcT t ht
    calc t * c = c * t * c⁻¹ * c := by rw [this]
      _ = c * t := by group
  have hcT' : c ∈ T := hS.centT hcC
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS.pT) ⟨c, hcT'⟩
  have hok : orderOf c = p ^ k := by
    have : orderOf (⟨c, hcT'⟩ : ↥T) = orderOf c := Subgroup.orderOf_mk c hcT'
    rw [← this]; exact hk
  have hk0 : k = 0 := by
    by_contra hne
    exact hc (hok ▸ dvd_pow_self p hne)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hok
  exact hok

theorem stabAll_le [Finite M] (hS : Setup p T A) : stabAll A ≤ T := by
  have hA := hS.normalA
  refine hS.maxT _ inferInstance ?_
  rw [IsPGroup.iff_card]
  have hne : Nat.card ↥(stabAll A) ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne ?_⟩
  intro r hr hrd
  by_contra hrp
  have hrf : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hrd
  have hcp : ¬ p ∣ orderOf (c : M) := by
    rw [Subgroup.orderOf_coe, hc]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hr).mp h).symm
  have h1 := centralizes_of_stabAll hA (hS.pT.to_le hS.leT) hcp c.2
  have h2 : (c : M) = 1 := hS.eq_one_of_centralizes hcp h1
  have h3 : c = 1 := Subtype.ext h2
  rw [h3, orderOf_one] at hc
  exact hr.one_lt.ne hc

end Setup

theorem inv_conj_conj (r x : M) : r⁻¹ * (r * x * r⁻¹) * r = x := by group

theorem conj_inv_conj (r x : M) : r * (r⁻¹ * x * r) * r⁻¹ = x := by group

theorem nconj {Y : Subgroup M} (hY : Y.Normal) {x : M} (hx : x ∈ Y) (r : M) :
    r * x * r⁻¹ ∈ Y := hY.conj_mem x hx r

theorem nconj_inv {Y : Subgroup M} (hY : Y.Normal) {x : M} (hx : x ∈ Y) (r : M) :
    r⁻¹ * x * r ∈ Y := by
  have := hY.conj_mem x hx r⁻¹
  rwa [inv_inv] at this

theorem nconj_iff {Y : Subgroup M} (hY : Y.Normal) {x : M} (r : M) :
    r * x * r⁻¹ ∈ Y ↔ x ∈ Y :=
  ⟨fun h => by have := nconj_inv hY h r; rwa [inv_conj_conj] at this, fun h => nconj hY h r⟩

theorem nconj_inv_iff {Y : Subgroup M} (hY : Y.Normal) {x : M} (r : M) :
    r⁻¹ * x * r ∈ Y ↔ x ∈ Y :=
  ⟨fun h => by have := nconj hY h r; rwa [conj_inv_conj] at this, fun h => nconj_inv hY h r⟩

theorem comm_self_le {T X Y : Subgroup M} (hT : Group.IsNilpotent ↥T) (hTn : T.Normal)
    (hXT : X ≤ T) (hc : IsChiefPair X Y) : ⁅X, X⁆ ≤ Y := by
  have hXn := hc.1
  have hYn := hc.2.1
  have hYX : Y < X := hc.2.2.1
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup M, Z = ⁅X, T⁆ ⊔ Y := ⟨_, rfl⟩
  have hZn : Z.Normal := by rw [hZ]; infer_instance
  have hZX : Z ≤ X := by
    rw [hZ]; exact sup_le (Subgroup.commutator_le_left X T) hYX.le
  have hYZ : Y ≤ Z := by rw [hZ]; exact le_sup_right
  have hTY : T ≤ normalizer (Y : Set M) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact (nconj_iff hYn t).symm
  rcases hc.2.2.2 Z hZn hYZ hZX with h | h
  · have : ⁅X, T⁆ ≤ Y := by rw [← h, hZ]; exact le_sup_left
    exact (Subgroup.commutator_mono_right hXT).trans this
  · exfalso
    have hXle : X ≤ ⁅X, T⁆ ⊔ Y := by rw [← hZ, h]
    exact hYX.not_ge (le_of_le_comm_sup hT hXT hTY hXle)

end CFSG.GH74.GLS.Stage2.Signalizer.L53
