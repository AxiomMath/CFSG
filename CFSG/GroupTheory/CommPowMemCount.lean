module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

public section

open scoped Pointwise

namespace CFSG.GroupTheory

private def powMemSubgroup {G : Type*} [Group G] {C A D : Subgroup G}
    (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) : Subgroup G where
  carrier := {x : G | x ∈ D ∧ x ^ n ∈ A}
  one_mem' := ⟨D.one_mem, by simpa using A.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxD, hxA⟩ ⟨hyD, hyA⟩
    refine ⟨D.mul_mem hxD hyD, ?_⟩
    rw [Commute.mul_pow (hC x (hDC hxD) y (hDC hyD)) n]
    exact A.mul_mem hxA hyA
  inv_mem' := by
    rintro x ⟨hxD, hxA⟩
    exact ⟨D.inv_mem hxD, by rw [inv_pow]; exact A.inv_mem hxA⟩

private def powTorsionSubgroup {G : Type*} [Group G] {C D : Subgroup G}
    (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) : Subgroup G where
  carrier := {d : G | d ∈ D ∧ d ^ n = 1}
  one_mem' := ⟨D.one_mem, one_pow n⟩
  mul_mem' := by
    rintro x y ⟨hxD, hx⟩ ⟨hyD, hy⟩
    refine ⟨D.mul_mem hxD hyD, ?_⟩
    rw [Commute.mul_pow (hC x (hDC hxD) y (hDC hyD)) n, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨hxD, hx⟩
    exact ⟨D.inv_mem hxD, by rw [inv_pow, hx, inv_one]⟩

private theorem powTorsionSubgroup_le_powMemSubgroup {G : Type*} [Group G]
    {C A D : Subgroup G} (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    powTorsionSubgroup hDC hC n ≤ powMemSubgroup (A := A) hDC hC n := by
  rintro d ⟨hdD, hd⟩
  exact ⟨hdD, by rw [hd]; exact A.one_mem⟩

private theorem inf_powMemSubgroup_eq_inf {G : Type*} [Group G]
    {C A D : Subgroup G} (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    A ⊓ powMemSubgroup (A := A) hDC hC n = A ⊓ D := by
  apply le_antisymm
  · rintro x ⟨hxA, hxD, -⟩
    exact ⟨hxA, hxD⟩
  · rintro x ⟨hxA, hxD⟩
    exact ⟨hxA, hxD, A.pow_mem hxA n⟩

private theorem powMemSet_eq_mul {G : Type*} [Group G] {C A D : Subgroup G}
    (hAC : A ≤ C) (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hCAD : ∀ c ∈ C, ∃ a ∈ A, ∃ d ∈ D, c = a * d) (n : ℕ) :
    {c : G | c ∈ C ∧ c ^ n ∈ A} =
      (A : Set G) * (powMemSubgroup (A := A) hDC hC n : Set G) := by
  ext c
  constructor
  · rintro ⟨hcC, hcA⟩
    obtain ⟨a, haA, d, hdD, hcad⟩ := hCAD c hcC
    have hpow : (a * d) ^ n = a ^ n * d ^ n :=
      Commute.mul_pow (hC a (hAC haA) d (hDC hdD)) n
    have hdA : d ^ n ∈ A := by
      have h : d ^ n = (a ^ n)⁻¹ * c ^ n := by
        rw [hcad, hpow]
        group
      rw [h]
      exact A.mul_mem (A.inv_mem (A.pow_mem haA n)) hcA
    exact ⟨a, haA, d, ⟨hdD, hdA⟩, hcad.symm⟩
  · rintro ⟨a, haA, x, ⟨hxD, hxA⟩, rfl⟩
    refine ⟨C.mul_mem (hAC haA) (hDC hxD), ?_⟩
    rw [Commute.mul_pow (hC a (hAC haA) x (hDC hxD)) n]
    exact A.mul_mem (A.pow_mem haA n) hxA

private def powMap {G : Type*} [Group G] {C A D : Subgroup G}
    (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    ↥(powMemSubgroup (A := A) hDC hC n) →* ↥(A ⊓ D) where
  toFun x := ⟨x.1 ^ n, ⟨x.2.2, D.pow_mem x.2.1 n⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (x.1 * y.1) ^ n = x.1 ^ n * y.1 ^ n
    exact Commute.mul_pow (hC x.1 (hDC x.2.1) y.1 (hDC y.2.1)) n

private theorem powMap_ker {G : Type*} [Group G] {C A D : Subgroup G}
    (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    (powMap (A := A) hDC hC n).ker =
      (powTorsionSubgroup hDC hC n).subgroupOf (powMemSubgroup (A := A) hDC hC n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have h : x.1 ^ n = 1 := by
      have h' := congrArg (fun y : ↥(A ⊓ D) => (y : G)) hx
      simpa [powMap] using h'
    exact ⟨x.2.1, h⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hx.2

private theorem powMap_ker_card {G : Type*} [Group G] {C A D : Subgroup G}
    (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    Nat.card (powMap (A := A) hDC hC n).ker = Nat.card (powTorsionSubgroup hDC hC n) := by
  rw [powMap_ker]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (powTorsionSubgroup_le_powMemSubgroup (A := A) hDC hC n)).toEquiv

private theorem powMemSubgroup_finite {G : Type*} [Group G] {C A D : Subgroup G}
    [Finite A] (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ)
    (hT : (powTorsionSubgroup hDC hC n : Set G).Finite) :
    Finite ↥(powMemSubgroup (A := A) hDC hC n) := by
  haveI : Finite ↥(powTorsionSubgroup hDC hC n) := hT.to_subtype
  have hker : (powMap (A := A) hDC hC n).ker =
      (powTorsionSubgroup hDC hC n).subgroupOf (powMemSubgroup (A := A) hDC hC n) :=
    powMap_ker hDC hC n
  have hkerFin : Finite (powMap (A := A) hDC hC n).ker := by
    rw [hker]
    exact Finite.of_equiv ↥(powTorsionSubgroup hDC hC n)
      (Subgroup.subgroupOfEquivOfLe
        (powTorsionSubgroup_le_powMemSubgroup (A := A) hDC hC n)).symm.toEquiv
  have hrangeFin : Finite (powMap (A := A) hDC hC n).range := by
    haveI : Finite ↥(A ⊓ D) := Finite.Set.subset (A : Set G) (fun x hx => hx.1)
    exact Subtype.finite
  exact (MonoidHom.finite_iff_finite_ker_range (powMap (A := A) hDC hC n)).mpr
    ⟨hkerFin, hrangeFin⟩

private theorem powMemSubgroup_card_le {G : Type*} [Group G] {C A D : Subgroup G}
    [Finite A] (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    Nat.card (powMemSubgroup (A := A) hDC hC n) ≤
      Nat.card ↥(A ⊓ D) * Nat.card (powTorsionSubgroup hDC hC n) := by
  have hcard := Subgroup.card_ker_mul_card_range (powMap (A := A) hDC hC n)
  have hker := powMap_ker_card (A := A) hDC hC n
  have hrange : Nat.card (powMap (A := A) hDC hC n).range ≤ Nat.card ↥(A ⊓ D) := by
    haveI : Finite ↥(A ⊓ D) := Finite.Set.subset (A : Set G) (fun x hx => hx.1)
    exact Nat.card_le_card_of_injective
      (fun x : (powMap (A := A) hDC hC n).range => (x.1 : ↥(A ⊓ D)))
      (fun x y h => Subtype.ext h)
  calc
    Nat.card (powMemSubgroup (A := A) hDC hC n) =
        Nat.card (powMap (A := A) hDC hC n).ker * Nat.card (powMap (A := A) hDC hC n).range :=
      hcard.symm
    _ = Nat.card (powTorsionSubgroup hDC hC n) *
        Nat.card (powMap (A := A) hDC hC n).range := by rw [hker]
    _ ≤ Nat.card (powTorsionSubgroup hDC hC n) * Nat.card ↥(A ⊓ D) :=
      Nat.mul_le_mul_left _ hrange
    _ = Nat.card ↥(A ⊓ D) * Nat.card (powTorsionSubgroup hDC hC n) := Nat.mul_comm _ _

private def powMulHom {G : Type*} [Group G] {A X : Subgroup G}
    (hc : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) : ↥A × ↥X →* G where
  toFun p := (p.1 : G) * (p.2 : G)
  map_one' := by simp
  map_mul' p q := by
    have hcomm : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) :=
      (hc (q.1 : G) q.1.2 (p.2 : G) p.2.2).symm
    change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
      ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
    calc
      ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
      _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hcomm]
      _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group

private noncomputable def powMulHomKerEquiv {G : Type*} [Group G] {A X : Subgroup G}
    (hc : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) :
    (powMulHom hc).ker ≃ ↥(A ⊓ X) where
  toFun k :=
    ⟨(k.1.1 : G), k.1.1.2, by
      have hk : (k.1.1 : G) * (k.1.2 : G) = 1 := k.2
      rw [eq_inv_of_mul_eq_one_left hk]
      exact X.inv_mem k.1.2.2⟩
  invFun b :=
    ⟨(⟨b.1, b.2.1⟩, ⟨b.1⁻¹, X.inv_mem b.2.2⟩), by
      change (b.1 : G) * (b.1 : G)⁻¹ = 1
      simp⟩
  left_inv k := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (eq_inv_of_mul_eq_one_right k.2).symm
  right_inv b := by
    apply Subtype.ext
    rfl

private theorem powMulHom_ker_card {G : Type*} [Group G] {A X : Subgroup G}
    (hc : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) :
    Nat.card (powMulHom hc).ker = Nat.card ↥(A ⊓ X) :=
  Nat.card_congr (powMulHomKerEquiv hc)

private theorem powMulHom_range {G : Type*} [Group G] {A X : Subgroup G}
    (hc : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) :
    (powMulHom hc).range = A ⊔ X := by
  apply le_antisymm
  · rintro g ⟨p, rfl⟩
    exact (A ⊔ X).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  · refine sup_le ?_ ?_
    · intro a ha
      exact ⟨(⟨a, ha⟩, 1), by simp [powMulHom]⟩
    · intro x hx
      exact ⟨(1, ⟨x, hx⟩), by simp [powMulHom]⟩

private theorem powMulHom_card {G : Type*} [Group G] {A X : Subgroup G}
    (hc : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) :
    Nat.card ↥(A ⊔ X) * Nat.card ↥(A ⊓ X) = Nat.card A * Nat.card X := by
  have h := Subgroup.card_ker_mul_card_range (powMulHom hc)
  rw [powMulHom_range hc, powMulHom_ker_card hc, Nat.card_prod] at h
  rw [Nat.mul_comm (Nat.card ↥(A ⊓ X)) (Nat.card ↥(A ⊔ X))] at h
  exact h

private theorem card_join_eq_card_mul_set {G : Type*} [Group G] {A X : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) :
    Nat.card ↥(A ⊔ X) = Nat.card ↥((A : Set G) * (X : Set G)) := by
  classical
  have hsupSet : ((A ⊔ X : Subgroup G) : Set G) = (A : Set G) * (X : Set G) := by
    ext g
    constructor
    · intro hg
      have hg' : g ∈ (powMulHom hcomm).range := by
        rw [powMulHom_range hcomm]
        exact hg
      obtain ⟨p, hp⟩ := hg'
      exact ⟨p.1, p.1.2, p.2, p.2.2, hp⟩
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact (A ⊔ X).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hx)
  refine Nat.card_congr ?_
  refine ⟨fun x => ⟨x.1, by
    change (x.1 : G) ∈ ((A : Set G) * (X : Set G))
    rw [← hsupSet]
    exact x.2⟩, fun x => ⟨x.1, by
    change (x.1 : G) ∈ ((A ⊔ X : Subgroup G) : Set G)
    rw [hsupSet]
    exact x.2⟩, fun _ => rfl, fun _ => rfl⟩

private theorem card_mul_set_le_torsion {G : Type*} [Group G] {C A D : Subgroup G} [Finite A]
    (hAC : A ≤ C) (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    Nat.card ↥((A : Set G) * (powMemSubgroup (A := A) hDC hC n : Set G)) ≤
      Nat.card A * Nat.card (powTorsionSubgroup hDC hC n) := by
  classical
  let X := powMemSubgroup (A := A) hDC hC n
  let T := powTorsionSubgroup hDC hC n
  have hXleD : X ≤ D := fun _ hx => hx.1
  have hcomm : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a :=
    fun a ha x hx => hC a (hAC ha) x (hDC (hXleD hx))
  have hinf : A ⊓ X = A ⊓ D := inf_powMemSubgroup_eq_inf hDC hC n
  have hXcard : Nat.card X ≤ Nat.card ↥(A ⊓ D) * Nat.card T :=
    powMemSubgroup_card_le hDC hC n
  have hcard : Nat.card ↥(A ⊔ X) * Nat.card ↥(A ⊓ X) = Nat.card A * Nat.card X :=
    powMulHom_card hcomm
  have hAXcard : Nat.card ↥(A ⊔ X) = Nat.card ↥((A : Set G) * (X : Set G)) :=
    card_join_eq_card_mul_set hcomm
  haveI : Nonempty ↥(A ⊓ D) := ⟨⟨1, A.one_mem, D.one_mem⟩⟩
  haveI : Finite ↥(A ⊓ D) := Finite.Set.subset (A : Set G) (fun x hx => hx.1)
  have hpos : 0 < Nat.card ↥(A ⊓ D) := Nat.card_pos
  have hle : Nat.card A * Nat.card X ≤
      Nat.card A * (Nat.card ↥(A ⊓ D) * Nat.card T) :=
    Nat.mul_le_mul_left _ hXcard
  have h1 : Nat.card ↥(A ⊔ X) * Nat.card ↥(A ⊓ X) ≤
      (Nat.card A * Nat.card T) * Nat.card ↥(A ⊓ D) := by
    rw [hcard]
    calc
      Nat.card A * Nat.card X ≤ Nat.card A * (Nat.card ↥(A ⊓ D) * Nat.card T) := hle
      _ = (Nat.card A * Nat.card T) * Nat.card ↥(A ⊓ D) := by
        rw [← Nat.mul_assoc, Nat.mul_right_comm]
  rw [hAXcard, hinf] at h1
  exact Nat.le_of_mul_le_mul_right h1 hpos

private theorem encard_pow_mem_eq_card_mul_set {G : Type*} [Group G] {C A D : Subgroup G}
    [Finite A] (hAC : A ≤ C) (hDC : D ≤ C)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hCAD : ∀ c ∈ C, ∃ a ∈ A, ∃ d ∈ D, c = a * d) (n : ℕ)
    (hT : (powTorsionSubgroup hDC hC n : Set G).Finite) :
    {c : G | c ∈ C ∧ c ^ n ∈ A}.encard =
      (Nat.card ↥((A : Set G) *
        (powMemSubgroup (A := A) hDC hC n : Set G)) : ℕ∞) := by
  classical
  have hXfin : Finite ↥(powMemSubgroup (A := A) hDC hC n) :=
    powMemSubgroup_finite hDC hC n hT
  have hAXfin : ((A : Set G) * (powMemSubgroup (A := A) hDC hC n : Set G)).Finite :=
    Set.Finite.mul (Set.toFinite (A : Set G)) (Set.finite_coe_iff.mpr hXfin)
  rw [powMemSet_eq_mul hAC hDC hC hCAD n]
  rw [← Set.Finite.cast_ncard_eq hAXfin, Nat.card_coe_set_eq]

private theorem encard_pow_mem_le_of_finite {G : Type*} [Group G] {C A D : Subgroup G}
    [Finite A] (hAC : A ≤ C) (hDC : D ≤ C)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hCAD : ∀ c ∈ C, ∃ a ∈ A, ∃ d ∈ D, c = a * d) (n : ℕ)
    (hT : (powTorsionSubgroup hDC hC n : Set G).Finite) :
    {c : G | c ∈ C ∧ c ^ n ∈ A}.encard ≤
      Nat.card A * {d : G | d ∈ D ∧ d ^ n = 1}.encard := by
  have hEq := encard_pow_mem_eq_card_mul_set hAC hDC hC hCAD n hT
  have hle := card_mul_set_le_torsion hAC hDC hC n
  have hTset : ({d : G | d ∈ D ∧ d ^ n = 1} : Set G) =
      (powTorsionSubgroup hDC hC n : Set G) := rfl
  rw [hEq, hTset, ← Set.Finite.cast_ncard_eq hT,
    ← Nat.card_coe_set_eq (powTorsionSubgroup hDC hC n : Set G), ← Nat.cast_mul]
  exact ENat.coe_le_coe.mpr hle

private theorem encard_pow_mem_le_of_infinite {G : Type*} [Group G] {C A D : Subgroup G}
    [Finite A] (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ)
    (hT : ¬ (powTorsionSubgroup hDC hC n : Set G).Finite) :
    {c : G | c ∈ C ∧ c ^ n ∈ A}.encard ≤
      Nat.card A * {d : G | d ∈ D ∧ d ^ n = 1}.encard := by
  have hTinf : ({d : G | d ∈ D ∧ d ^ n = 1} : Set G).Infinite :=
    Set.not_finite.mp (by
      rwa [show (powTorsionSubgroup hDC hC n : Set G) = {d : G | d ∈ D ∧ d ^ n = 1}
        from rfl] at hT)
  have hAne : (Nat.card A : ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥A)).ne'
  rw [hTinf.encard_eq, ENat.mul_top hAne]
  exact le_top


theorem encard_pow_mem_le_card_mul_encard {G : Type*} [Group G] {C A D : Subgroup G} [Finite A]
    (hAC : A ≤ C) (hDC : D ≤ C) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hCAD : ∀ c ∈ C, ∃ a ∈ A, ∃ d ∈ D, c = a * d) (n : ℕ) :
    {c : G | c ∈ C ∧ c ^ n ∈ A}.encard ≤ Nat.card A * {d : G | d ∈ D ∧ d ^ n = 1}.encard := by
  classical
  by_cases hT : (powTorsionSubgroup hDC hC n : Set G).Finite
  · exact encard_pow_mem_le_of_finite hAC hDC hC hCAD n hT
  · exact encard_pow_mem_le_of_infinite hDC hC n hT


end CFSG.GroupTheory
