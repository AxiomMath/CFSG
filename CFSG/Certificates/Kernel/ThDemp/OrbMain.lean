module

public import CFSG.Certificates.Kernel.ThDemp.OrbitCount
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Certificates.ThDemp.OrbMain

open MulAction CFSG.Certificates.ThDemp.OrbitCount

@[expose] def sOf : Fin 9 → ℕ := ![5376, 126, 48, 9, 3, 5, 5, 155, 155]

structure SuborbitHyp {G X : Type*} [Group G] [MulAction G X] [Finite G] (D : Subgroup G) (u : X)
    (p : Fin 10 → X) : Prop where
  cardG : Nat.card G ≤ 90745943887872000
  cardD : Nat.card D = 319979520
  fixD : D ≤ stabilizer G u
  mem : ∀ i, p i ∈ orbit G u
  stab : ∀ i : Fin 9, Nat.card (stabilizer D (p i.castSucc)) = sOf i
  orb9 : (orbit D (p 9)).ncard = 248
  dis56 : p 6 ∉ orbit D (p 5)
  dis78 : p 8 ∉ orbit D (p 7)

variable {G X : Type*} [Group G] [MulAction G X] [Finite G] {D : Subgroup G} {u : X}
  {p : Fin 10 → X}

@[expose] def pts (u : X) (p : Fin 10 → X) : Fin 11 → X := Fin.cons u p

@[expose] def oSize : Fin 11 → ℕ :=
  ![1, 59520, 2539520, 6666240, 35553280, 106659840, 63995904, 63995904, 2064384, 2064384, 248]

namespace SuborbitHyp

variable (H : SuborbitHyp D u p)
include H

theorem finD : Finite D := Subgroup.instFiniteSubtypeMem D

theorem orbit_u : orbit D u = {u} := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    exact H.fixD d.2
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    exact mem_orbit_self _

theorem ncard_orbit (i : Fin 11) : (orbit D (pts u p i)).ncard = oSize i := by
  have : Finite D := H.finD
  have hpos : ∀ s, 0 < s → ∀ i : Fin 9, Nat.card (stabilizer D (p i.castSucc)) = s →
      (orbit D (p i.castSucc)).ncard = 319979520 / s := by
    intro s hs i hi
    have h := ncard_orbit_mul_card_stabilizer D (p i.castSucc)
    rw [hi, H.cardD] at h
    rw [← h, Nat.mul_div_cancel _ hs]
  fin_cases i
  · change (orbit D u).ncard = 1
    rw [H.orbit_u, Set.ncard_singleton]
  · exact hpos 5376 (by norm_num) 0 (H.stab 0)
  · exact hpos 126 (by norm_num) 1 (H.stab 1)
  · exact hpos 48 (by norm_num) 2 (H.stab 2)
  · exact hpos 9 (by norm_num) 3 (H.stab 3)
  · exact hpos 3 (by norm_num) 4 (H.stab 4)
  · exact hpos 5 (by norm_num) 5 (H.stab 5)
  · exact hpos 5 (by norm_num) 6 (H.stab 6)
  · exact hpos 155 (by norm_num) 7 (H.stab 7)
  · exact hpos 155 (by norm_num) 8 (H.stab 8)
  · exact H.orb9

theorem ncard_eq_of_mem {a b : X} (h : b ∈ orbit D a) : (orbit D b).ncard = (orbit D a).ncard := by
  rw [orbit_eq_iff.mpr h]

theorem disjoint (i j : Fin 11) (hij : i ≠ j) : pts u p j ∉ orbit D (pts u p i) := by
  intro h
  have e := H.ncard_eq_of_mem h
  rw [H.ncard_orbit, H.ncard_orbit] at e
  have s56 : p 5 ∉ orbit D (p 6) := fun h' => H.dis56 (by
    rw [orbit_eq_iff.mpr h']
    exact mem_orbit_self _)
  have s78 : p 7 ∉ orbit D (p 8) := fun h' => H.dis78 (by
    rw [orbit_eq_iff.mpr h']
    exact mem_orbit_self _)
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact absurd e (by decide)
    | exact H.dis56 h
    | exact s56 h
    | exact H.dis78 h
    | exact s78 h

theorem cover : stabilizer G u = D ∧ ∀ x ∈ orbit G u, ∃ i, x ∈ orbit D (pts u p i) := by
  refine stabilizer_eq_and_cover D u H.fixD (pts u p) ?_ (fun i j hij => H.disjoint i j hij) ?_
  · intro i
    refine Fin.cases (mem_orbit_self u) (fun j => H.mem j) i
  · refine H.cardG.trans ?_
    rw [Finset.sum_congr rfl (fun i _ => H.ncard_orbit i), H.cardD]
    norm_num [Fin.sum_univ_succ, oSize]

theorem ncard_fix_le (x : G) :
    {q ∈ orbit G u | x • q = q}.ncard ≤ ∑ i, {q ∈ orbit D (pts u p i) | x • q = q}.ncard := by
  classical
  have hsub : {q ∈ orbit G u | x • q = q} ⊆ ⋃ i, {q ∈ orbit D (pts u p i) | x • q = q} := by
    rintro q ⟨hq, hx⟩
    obtain ⟨i, hi⟩ := H.cover.2 q hq
    exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩
  refine (Set.ncard_le_ncard hsub (Set.finite_iUnion fun i =>
    (Set.finite_range (fun d : D => d • pts u p i)).subset (fun q hq => hq.1))).trans ?_
  exact Set.ncard_iUnion_le_of_fintype _

end SuborbitHyp

theorem fix_le_div {f s c t C : ℕ} (hs : 0 < s) (h : f * s ≤ C * t) (hC : C ≤ c) :
    f ≤ c * t / s := by
  rw [Nat.le_div_iff_mul_le hs]
  exact h.trans (Nat.mul_le_mul_right _ hC)

theorem orderOf_of_isConj {M : Type*} [Group M] {x t : M} (h : IsConj x t) : orderOf t = orderOf x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hs : SemiconjBy c x t := by
    rw [SemiconjBy, ← hc, inv_mul_cancel_right]
  exact (SemiconjBy.orderOf_eq c hs).symm

theorem no_conj_of_coprime {M : Type*} [Group M] (S : Subgroup M) {x : M} {n : ℕ}
    (hx : orderOf x = n) (hn : 1 < n) (hcop : Nat.Coprime n (Nat.card S)) :
    ∀ t ∈ S, ¬ IsConj x t := by
  intro t ht hc
  have hdvd : orderOf t ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S ht
  rw [orderOf_of_isConj hc, hx] at hdvd
  have : n = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

noncomputable def conjSet (D : Subgroup G) [Finite D] (p : X) (x : D) : Finset D := by
  classical
  have : Fintype D := Fintype.ofFinite D
  exact Finset.univ.filter (fun t => t ∈ stabilizer D p ∧ IsConj x t)

theorem mem_conjSet {D : Subgroup G} [Finite D] {p : X} {x t : D} :
    t ∈ conjSet D p x ↔ t ∈ stabilizer D p ∧ IsConj x t := by
  classical
  unfold conjSet
  simp

theorem fix_mul_le_conjSet (D : Subgroup G) [Finite D] (p : X) (x : D) :
    {q ∈ orbit D p | x • q = q}.ncard * Nat.card (stabilizer D p) ≤
      Nat.card (Subgroup.centralizer ({x} : Set D)) * (conjSet D p x).card :=
  ncard_fix_mul_le D p x (conjSet D p x) (fun t ht hc => mem_conjSet.mpr ⟨ht, hc⟩)

theorem card_conjSet_le (D : Subgroup G) [Finite D] (p : X) (x : D) (T : Finset D)
    (hT : ∀ t ∈ stabilizer D p, IsConj x t → t ∈ T) : (conjSet D p x).card ≤ T.card :=
  Finset.card_le_card fun t ht => hT t (mem_conjSet.mp ht).1 (mem_conjSet.mp ht).2

theorem card_conjSet_add_le (D : Subgroup G) [Finite D] (p : X) (x : D) (E : Finset D)
    (hE : ∀ e ∈ E, e ∈ stabilizer D p ∧ ¬ IsConj x e) :
    (conjSet D p x).card + E.card ≤ Nat.card (stabilizer D p) := by
  classical
  have : Fintype D := Fintype.ofFinite D
  set S : Finset D := Finset.univ.filter (· ∈ stabilizer D p)
  have hS : S.card = Nat.card (stabilizer D p) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun t => by simp [S])
  rw [← hS, ← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun t ht => ?_
    rcases Finset.mem_union.mp ht with h | h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_conjSet.mp h).1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hE t h).1⟩
  · rw [Finset.disjoint_left]
    intro t h1 h2
    exact (hE t h2).2 (mem_conjSet.mp h1).2

theorem fix_le_of {f s C c t k : ℕ} (h : f * s ≤ C * t) (hC : C ≤ c) (hk : c * t < (k + 1) * s) :
    f ≤ k := by
  by_contra hf
  have : (k + 1) * s ≤ f * s := Nat.mul_le_mul_right _ (by omega)
  have h2 : C * t ≤ c * t := Nat.mul_le_mul_right _ hC
  omega

noncomputable def powSet (D : Subgroup G) (y : D) : Finset D := by
  classical
  exact (Finset.range 31).image (fun k => y ^ k)

theorem card_powSet (D : Subgroup G) (y : D) (hy : orderOf y = 31) : (powSet D y).card = 31 := by
  classical
  unfold powSet
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb e
    have := pow_injOn_Iio_orderOf (x := y)
    rw [hy] at this
    exact this (by simpa using ha) (by simpa using hb) e

theorem powSet_spec (D : Subgroup G) (p : X) {y x : D} (hyp : y ∈ stabilizer D p)
    (hy : orderOf y = 31) (hx : orderOf x = 5) :
    ∀ e ∈ powSet D y, e ∈ stabilizer D p ∧ ¬ IsConj x e := by
  classical
  intro e he
  unfold powSet at he
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp he
  refine ⟨Subgroup.pow_mem _ hyp k, fun hc => ?_⟩
  have h1 := orderOf_of_isConj hc
  have h2 : orderOf (y ^ k) ∣ 31 := by
    rw [← hy]
    exact orderOf_pow_dvd k
  rw [h1, hx] at h2
  norm_num at h2

namespace SuborbitHyp

variable (H : SuborbitHyp D u p)
include H

theorem card_cent_inf (x : D) :
    Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ stabilizer G u) =
      Nat.card (Subgroup.centralizer ({x} : Set D)) := by
  rw [H.cover.1]
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨g.1, g.2.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp g.2.1))⟩
      invFun := fun c => ⟨c.1.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2)), c.1.2⟩
      left_inv := fun g => rfl
      right_inv := fun c => rfl }

theorem fix_u (x : D) : {q ∈ orbit D (pts u p 0) | x • q = q}.ncard ≤ 1 := by
  have : {q ∈ orbit D (pts u p 0) | x • q = q} ⊆ {u} := by
    rintro q ⟨hq, -⟩
    change q ∈ orbit D u at hq
    rwa [H.orbit_u] at hq
  exact (Set.ncard_le_ncard this (Set.finite_singleton u)).trans (Set.ncard_singleton u).le

theorem fix_coprime (x : D) {n : ℕ} (hx : orderOf x = n) (hn : 1 < n) (i : Fin 10)
    (hcop : Nat.Coprime n (Nat.card (stabilizer D (p i)))) :
    {q ∈ orbit D (p i) | x • q = q}.ncard = 0 := by
  have : Finite D := H.finD
  have h := fix_mul_le_conjSet D (p i) x
  have he : conjSet D (p i) x = ∅ := by
    classical
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t ht
    exact no_conj_of_coprime _ hx hn hcop t (mem_conjSet.mp ht).1 (mem_conjSet.mp ht).2
  rw [he, Finset.card_empty, Nat.mul_zero] at h
  have hpos : 0 < Nat.card (stabilizer D (p i)) := Nat.card_pos
  exact Nat.eq_zero_of_le_zero (Nat.le_of_mul_le_mul_right (by simpa using h) hpos)

theorem card_stab9 : Nat.card (stabilizer D (p 9)) = 1290240 := by
  have : Finite D := H.finD
  have h := ncard_orbit_mul_card_stabilizer D (p 9)
  rw [H.orb9, H.cardD] at h
  omega

theorem card_centralizer_five (x : D) (hx : orderOf x = 5)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set D)) ≤ 30)
    (h9 : {q ∈ orbit D (p 9) | x • q = q}.ncard ≤ 3) (ya yb : D) (ha : ya ∈ stabilizer D (p 7))
    (hb : yb ∈ stabilizer D (p 8)) (hoa : orderOf ya = 31) (hob : orderOf yb = 31) :
    Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) ≤ 3000 := by
  have : Finite D := H.finD
  have hz : ∀ i : Fin 9, Nat.Coprime 5 (sOf i) →
      {q ∈ orbit D (p i.castSucc) | (x : G) • q = q}.ncard = 0 := by
    intro i hi
    refine H.fix_coprime x hx (by norm_num) i.castSucc ?_
    rw [H.stab i]
    exact hi
  have h5 : ∀ i : Fin 9, sOf i = 5 → {q ∈ orbit D (p i.castSucc) | (x : G) • q = q}.ncard ≤ 24 := by
    intro i hi
    have hs : Nat.card (stabilizer D (p i.castSucc)) = 5 := by
      rw [H.stab i, hi]
    have h1 := fix_mul_le_conjSet D (p i.castSucc) x
    have h2 := card_conjSet_add_le D (p i.castSucc) x {1} (by
      intro e he
      rw [Finset.mem_singleton] at he
      subst he
      refine ⟨Subgroup.one_mem _, fun hc => ?_⟩
      have := orderOf_of_isConj hc
      rw [orderOf_one, hx] at this
      norm_num at this)
    rw [hs, Finset.card_singleton] at h2
    rw [hs] at h1
    exact fix_le_of h1 hC (by omega)
  have h155 : ∀ i : Fin 9, sOf i = 155 → ∀ y : D, y ∈ stabilizer D (p i.castSucc) →
      orderOf y = 31 → {q ∈ orbit D (p i.castSucc) | (x : G) • q = q}.ncard ≤ 24 := by
    intro i hi y hy hyo
    have hs : Nat.card (stabilizer D (p i.castSucc)) = 155 := by
      rw [H.stab i, hi]
    have h1 := fix_mul_le_conjSet D (p i.castSucc) x
    have h2 := card_conjSet_add_le D (p i.castSucc) x (powSet D y) (powSet_spec D _ hy hyo hx)
    rw [hs, card_powSet D y hyo] at h2
    rw [hs] at h1
    exact fix_le_of h1 hC (by omega)
  have hsum := H.ncard_fix_le (x : G)
  have hfix : {q ∈ orbit G u | (x : G) • q = q}.ncard ≤ 100 := by
    refine hsum.trans ?_
    simp only [Fin.sum_univ_succ]
    have e0 : {q ∈ orbit D (pts u p 0) | (x : G) • q = q}.ncard ≤ 1 := H.fix_u x
    have e1 : {q ∈ orbit D (p 0) | (x : G) • q = q}.ncard = 0 := hz 0 (by decide)
    have e2 : {q ∈ orbit D (p 1) | (x : G) • q = q}.ncard = 0 := hz 1 (by decide)
    have e3 : {q ∈ orbit D (p 2) | (x : G) • q = q}.ncard = 0 := hz 2 (by decide)
    have e4 : {q ∈ orbit D (p 3) | (x : G) • q = q}.ncard = 0 := hz 3 (by decide)
    have e5 : {q ∈ orbit D (p 4) | (x : G) • q = q}.ncard = 0 := hz 4 (by decide)
    have e6 : {q ∈ orbit D (p 5) | (x : G) • q = q}.ncard ≤ 24 := h5 5 rfl
    have e7 : {q ∈ orbit D (p 6) | (x : G) • q = q}.ncard ≤ 24 := h5 6 rfl
    have e8 : {q ∈ orbit D (p 7) | (x : G) • q = q}.ncard ≤ 24 := h155 7 rfl ya ha hoa
    have e9 : {q ∈ orbit D (p 8) | (x : G) • q = q}.ncard ≤ 24 := h155 8 rfl yb hb hob
    have e10 : {q ∈ orbit D (p 9) | (x : G) • q = q}.ncard ≤ 3 := h9
    change {q ∈ orbit D (pts u p 0) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 0) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 1) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 2) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 3) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 4) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 5) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 6) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 7) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 8) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 9) | (x : G) • q = q}.ncard + 0)))))))))) ≤ 100
    omega
  have hcent := card_centralizer_le u (x : G) (H.fixD x.2)
  rw [H.card_cent_inf x] at hcent
  calc Nat.card (Subgroup.centralizer ({(x : G)} : Set G))
      ≤ {q ∈ orbit G u | (x : G) • q = q}.ncard * Nat.card (Subgroup.centralizer ({x} : Set D)) :=
        hcent
    _ ≤ 100 * 30 := Nat.mul_le_mul hfix hC

theorem card_centralizer_thirtyone (x : D) (hx : orderOf x = 31)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set D)) ≤ 31)
    (T7 T8 : Finset D) (hT7 : T7.card ≤ 5) (hT8 : T8.card ≤ 5)
    (h7 : ∀ t ∈ stabilizer D (p 7), IsConj x t → t ∈ T7)
    (h8 : ∀ t ∈ stabilizer D (p 8), IsConj x t → t ∈ T8)
    (ω₁ ω₂ : X) (h12 : ω₁ ≠ ω₂) (hω₁ : ω₁ ∈ orbit G u) (hω₂ : ω₂ ∈ orbit G u)
    (hx₁ : (x : G) • ω₁ = ω₁) (hx₂ : (x : G) • ω₂ = ω₂)
    (hc : ∀ c ∈ Subgroup.centralizer ({(x : G)} : Set G), c • u ≠ ω₁ ∧ c • u ≠ ω₂) :
    Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) ≤ 31 := by
  have : Finite D := H.finD
  have hz : ∀ i : Fin 9, Nat.Coprime 31 (sOf i) →
      {q ∈ orbit D (p i.castSucc) | (x : G) • q = q}.ncard = 0 := by
    intro i hi
    refine H.fix_coprime x hx (by norm_num) i.castSucc ?_
    rw [H.stab i]
    exact hi
  have h9 : {q ∈ orbit D (p 9) | (x : G) • q = q}.ncard = 0 :=
    H.fix_coprime x hx (by norm_num) 9 (by rw [H.card_stab9]; decide)
  have h155 : ∀ i : Fin 9, sOf i = 155 → ∀ T : Finset D, T.card ≤ 5 →
      (∀ t ∈ stabilizer D (p i.castSucc), IsConj x t → t ∈ T) →
      {q ∈ orbit D (p i.castSucc) | (x : G) • q = q}.ncard ≤ 1 := by
    intro i hi T hT hTs
    have hs : Nat.card (stabilizer D (p i.castSucc)) = 155 := by
      rw [H.stab i, hi]
    have h1 := fix_mul_le_conjSet D (p i.castSucc) x
    have h2 := card_conjSet_le D (p i.castSucc) x T hTs
    rw [hs] at h1
    exact fix_le_of (h1.trans (Nat.mul_le_mul_left _ h2)) hC (by omega)
  have hfix : {q ∈ orbit G u | (x : G) • q = q}.ncard ≤ 3 := by
    refine (H.ncard_fix_le (x : G)).trans ?_
    simp only [Fin.sum_univ_succ]
    have e0 : {q ∈ orbit D (pts u p 0) | (x : G) • q = q}.ncard ≤ 1 := H.fix_u x
    have e1 : {q ∈ orbit D (p 0) | (x : G) • q = q}.ncard = 0 := hz 0 (by decide)
    have e2 : {q ∈ orbit D (p 1) | (x : G) • q = q}.ncard = 0 := hz 1 (by decide)
    have e3 : {q ∈ orbit D (p 2) | (x : G) • q = q}.ncard = 0 := hz 2 (by decide)
    have e4 : {q ∈ orbit D (p 3) | (x : G) • q = q}.ncard = 0 := hz 3 (by decide)
    have e5 : {q ∈ orbit D (p 4) | (x : G) • q = q}.ncard = 0 := hz 4 (by decide)
    have e6 : {q ∈ orbit D (p 5) | (x : G) • q = q}.ncard = 0 := hz 5 (by decide)
    have e7 : {q ∈ orbit D (p 6) | (x : G) • q = q}.ncard = 0 := hz 6 (by decide)
    have e8 : {q ∈ orbit D (p 7) | (x : G) • q = q}.ncard ≤ 1 := h155 7 rfl T7 hT7 h7
    have e9 : {q ∈ orbit D (p 8) | (x : G) • q = q}.ncard ≤ 1 := h155 8 rfl T8 hT8 h8
    change {q ∈ orbit D (pts u p 0) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 0) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 1) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 2) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 3) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 4) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 5) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 6) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 7) | (x : G) • q = q}.ncard + ({q ∈ orbit D (p 8) | (x : G) • q = q}.ncard +
      ({q ∈ orbit D (p 9) | (x : G) • q = q}.ncard + 0)))))))))) ≤ 3
    omega
  set C := Subgroup.centralizer ({(x : G)} : Set G)
  have hfin : {q ∈ orbit G u | (x : G) • q = q}.Finite :=
    (Set.finite_range (fun g : G => g • u)).subset (fun q hq => hq.1)
  have hsub : orbit C u ⊆ {q ∈ orbit G u | (x : G) • q = q} \ {ω₁, ω₂} := by
    rintro q ⟨c, rfl⟩
    refine ⟨⟨mem_orbit_of_mem_orbit_subgroup (mem_orbit _ _), ?_⟩, ?_⟩
    · have hcx : c.1 * x = x * c.1 := Subgroup.mem_centralizer_singleton_iff.mp c.2
      change (x : G) • (c.1 • u) = c.1 • u
      rw [← mul_smul, ← hcx, mul_smul, H.fixD x.2]
    · rintro (h | h)
      · exact (hc c.1 c.2).1 h
      · exact (hc c.1 c.2).2 h
  have hcard2 : ({q ∈ orbit G u | (x : G) • q = q} \ {ω₁, ω₂}).ncard ≤ 1 := by
    have hsub2 : ({ω₁, ω₂} : Set X) ⊆ {q ∈ orbit G u | (x : G) • q = q} := by
      rintro q (rfl | rfl)
      · exact ⟨hω₁, hx₁⟩
      · exact ⟨hω₂, hx₂⟩
    rw [Set.ncard_diff hsub2, Set.ncard_pair h12]
    omega
  have horb : (orbit C u).ncard ≤ 1 :=
    (Set.ncard_le_ncard hsub hfin.diff).trans hcard2
  have h1 := ncard_orbit_mul_card_stabilizer C u
  have e : stabilizer C u ≃ ↥(C ⊓ stabilizer G u) :=
    { toFun := fun s => ⟨s.1.1, s.1.2, s.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, H.card_cent_inf x] at h1
  calc Nat.card C = (orbit C u).ncard * Nat.card (Subgroup.centralizer ({x} : Set D)) := h1.symm
    _ ≤ 1 * 31 := Nat.mul_le_mul horb hC
    _ = 31 := by norm_num

end SuborbitHyp

end CFSG.Certificates.ThDemp.OrbMain

end
