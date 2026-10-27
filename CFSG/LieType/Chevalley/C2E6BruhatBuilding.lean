module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.LieType.Chevalley.CosetBuilding

open scoped Pointwise

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)

structure IsWeylDistanceBuilding {C : Type*} (δ : C → C → W) : Prop where
  nonempty : Nonempty C
  eq_one_iff : ∀ x y, δ x y = 1 ↔ x = y
  mul_simple : ∀ x y z i, δ y z = cs.simple i →
    (δ x z = δ x y ∨ δ x z = δ x y * cs.simple i) ∧
      (cs.length (δ x y * cs.simple i) = cs.length (δ x y) + 1 → δ x z = δ x y * cs.simple i)
  exists_simple : ∀ x y i, ∃ z, δ y z = cs.simple i ∧ δ x z = δ x y * cs.simple i

@[expose] def residue {C : Type*} (δ : C → C → W) (J : Set ι) (x : C) : Set C :=
  {y | Relation.ReflTransGen (fun a b => ∃ i ∈ J, δ a b = cs.simple i) x y}

variable {G : Type*} [Group G] (B : Subgroup G) (D : W → Set G)

structure IsBruhatPartition : Prop where
  doubleCoset : ∀ w, ∃ g, D w = (B : Set G) * {g} * B
  partition : ∀ g : G, ∃! w, g ∈ D w
  one : D 1 = B
  inv : ∀ w, (D w)⁻¹ = D w⁻¹
  mul_of_length_add : ∀ w i, cs.length (w * cs.simple i) = cs.length w + 1 →
    D w * D (cs.simple i) = D (w * cs.simple i)
  mul_of_length_sub : ∀ w i, cs.length (w * cs.simple i) + 1 = cs.length w →
    D w * D (cs.simple i) = D (w * cs.simple i) ∪ D w

open _root_.Classical in
@[expose] def cosetDistance (x y : G ⧸ B) : W :=
  if h : ∃ w, (Quotient.out x)⁻¹ * Quotient.out y ∈ D w then h.choose else 1

variable {cs B D}

namespace IsBruhatPartition

variable (hD : IsBruhatPartition cs B D)
include hD

theorem mul_mem_left {w : W} {x : G} (hx : x ∈ D w) {b : G} (hb : b ∈ B) : b * x ∈ D w := by
  obtain ⟨g, hg⟩ := hD.doubleCoset w
  rw [hg] at hx ⊢
  obtain ⟨y, hy, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, z, hz, rfl⟩ := Set.mem_mul.mp hy
  rw [Set.mem_singleton_iff] at hz
  rw [hz, show b * (b₁ * g * b₂) = b * b₁ * g * b₂ by group]
  exact Set.mul_mem_mul (Set.mul_mem_mul (B.mul_mem hb hb₁) (Set.mem_singleton g)) hb₂

theorem mul_mem_right {w : W} {x : G} (hx : x ∈ D w) {b : G} (hb : b ∈ B) : x * b ∈ D w := by
  obtain ⟨g, hg⟩ := hD.doubleCoset w
  rw [hg] at hx ⊢
  obtain ⟨y, hy, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, z, hz, rfl⟩ := Set.mem_mul.mp hy
  rw [Set.mem_singleton_iff] at hz
  rw [hz, show b₁ * g * b₂ * b = b₁ * g * (b₂ * b) by group]
  exact Set.mul_mem_mul (Set.mul_mem_mul hb₁ (Set.mem_singleton g)) (B.mul_mem hb₂ hb)

theorem nonempty (w : W) : (D w).Nonempty := by
  obtain ⟨g, hg⟩ := hD.doubleCoset w
  rw [hg]
  exact ⟨g, ⟨g, ⟨1, B.one_mem, g, rfl, one_mul g⟩, 1, B.one_mem, mul_one g⟩⟩

theorem eq_of_mem {w w' : W} {x : G} (hx : x ∈ D w) (hx' : x ∈ D w') : w = w' :=
  (hD.partition x).unique hx hx'

theorem mem_inv {w : W} {x : G} (hx : x ∈ D w) : x⁻¹ ∈ D w⁻¹ := by
  rw [← hD.inv w, Set.mem_inv, inv_inv]
  exact hx

theorem mul_mem_simple {w : W} {i : ι} {x y : G} (hx : x ∈ D w) (hy : y ∈ D (cs.simple i)) :
    (x * y ∈ D (w * cs.simple i) ∨ x * y ∈ D w) ∧
      (cs.length (w * cs.simple i) = cs.length w + 1 → x * y ∈ D (w * cs.simple i)) := by
  have hxy : x * y ∈ D w * D (cs.simple i) := Set.mul_mem_mul hx hy
  refine ⟨?_, fun h => by rwa [hD.mul_of_length_add w i h] at hxy⟩
  rcases cs.length_mul_simple w i with h | h
  · rw [hD.mul_of_length_add w i h] at hxy
    exact Or.inl hxy
  · rwa [hD.mul_of_length_sub w i h] at hxy

theorem subset_mul (w : W) (i : ι) : D (w * cs.simple i) ⊆ D w * D (cs.simple i) := by
  rcases cs.length_mul_simple w i with h | h
  · rw [hD.mul_of_length_add w i h]
  · rw [hD.mul_of_length_sub w i h]
    exact Set.subset_union_left

end IsBruhatPartition

omit [Group G] in
theorem simple_ne_one (i : ι) : cs.simple i ≠ 1 := by
  intro h
  have := cs.length_simple i
  rw [h, cs.length_one] at this
  exact absurd this (by norm_num)

theorem cosetDistance_mk (hD : IsBruhatPartition cs B D) (g h : G) (w : W) :
    cosetDistance B D (g : G ⧸ B) (h : G ⧸ B) = w ↔ g⁻¹ * h ∈ D w := by
  obtain ⟨b₁, hb₁⟩ := QuotientGroup.mk_out_eq_mul B g
  obtain ⟨b₂, hb₂⟩ := QuotientGroup.mk_out_eq_mul B h
  have key : ∀ u, (Quotient.out (g : G ⧸ B))⁻¹ * Quotient.out (h : G ⧸ B) ∈ D u ↔
      g⁻¹ * h ∈ D u := by
    intro u
    rw [hb₁, hb₂]
    constructor
    · intro hu
      have := hD.mul_mem_right (hD.mul_mem_left hu b₁.2) (B.inv_mem b₂.2)
      simpa [mul_assoc] using this
    · intro hu
      have := hD.mul_mem_right (hD.mul_mem_left hu (B.inv_mem b₁.2)) b₂.2
      simpa [mul_assoc] using this
  obtain ⟨u, hu, -⟩ := hD.partition (g⁻¹ * h)
  have hex : ∃ w, (Quotient.out (g : G ⧸ B))⁻¹ * Quotient.out (h : G ⧸ B) ∈ D w :=
    ⟨u, (key u).mpr hu⟩
  rw [cosetDistance, dite_eq_left hex]
  have hc := (key _).mp hex.choose_spec
  constructor
  · rintro rfl
    exact hc
  · intro hw
    exact hD.eq_of_mem hc hw

section Main

variable (hD : IsBruhatPartition cs B D)
include hD

theorem cosetDistance_mk_eq (g h : G) {w : W} (hw : g⁻¹ * h ∈ D w) :
    cosetDistance B D (g : G ⧸ B) (h : G ⧸ B) = w :=
  (cosetDistance_mk hD g h w).mpr hw

theorem mem_cosetDistance_mk (g h : G) :
    g⁻¹ * h ∈ D (cosetDistance B D (g : G ⧸ B) (h : G ⧸ B)) :=
  (cosetDistance_mk hD g h _).mp rfl

theorem cosetDistance_eq_one_iff (x y : G ⧸ B) : cosetDistance B D x y = 1 ↔ x = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [cosetDistance_mk hD, hD.one, SetLike.mem_coe, QuotientGroup.eq]

theorem cosetDistance_mul_simple (x y z : G ⧸ B) (i : ι)
    (hyz : cosetDistance B D y z = cs.simple i) :
    (cosetDistance B D x z = cosetDistance B D x y ∨
        cosetDistance B D x z = cosetDistance B D x y * cs.simple i) ∧
      (cs.length (cosetDistance B D x y * cs.simple i) =
          cs.length (cosetDistance B D x y) + 1 →
        cosetDistance B D x z = cosetDistance B D x y * cs.simple i) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have h₁ := mem_cosetDistance_mk hD g h
  have h₂ : h⁻¹ * k ∈ D (cs.simple i) := (cosetDistance_mk hD h k _).mp hyz
  have hk : g⁻¹ * k = g⁻¹ * h * (h⁻¹ * k) := by group
  obtain ⟨h₃, h₄⟩ := hD.mul_mem_simple h₁ h₂
  refine ⟨?_, fun hl => cosetDistance_mk_eq hD g k (hk ▸ h₄ hl)⟩
  rcases h₃ with h₃ | h₃
  · exact Or.inr (cosetDistance_mk_eq hD g k (hk ▸ h₃))
  · exact Or.inl (cosetDistance_mk_eq hD g k (hk ▸ h₃))

theorem exists_cosetDistance_simple (x y : G ⧸ B) (i : ι) :
    ∃ z, cosetDistance B D y z = cs.simple i ∧
      cosetDistance B D x z = cosetDistance B D x y * cs.simple i := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  set w := cosetDistance B D (g : G ⧸ B) (h : G ⧸ B)
  have hw : g⁻¹ * h ∈ D w := mem_cosetDistance_mk hD g h
  rcases cs.length_mul_simple w i with hl | hl
  · obtain ⟨v, hv⟩ := hD.nonempty (cs.simple i)
    refine ⟨((h * v : G) : G ⧸ B), cosetDistance_mk_eq hD h (h * v) (by simpa using hv),
      cosetDistance_mk_eq hD g (h * v) ?_⟩
    rw [← mul_assoc]
    exact (hD.mul_mem_simple hw hv).2 hl
  · have hl' : cs.length (w * cs.simple i * cs.simple i) =
        cs.length (w * cs.simple i) + 1 := by
      rw [mul_assoc, cs.simple_mul_simple_self, mul_one]
      omega
    have hmul := hD.mul_of_length_add (w * cs.simple i) i hl'
    rw [mul_assoc, cs.simple_mul_simple_self, mul_one] at hmul
    have hw' : g⁻¹ * h ∈ D (w * cs.simple i) * D (cs.simple i) := hmul ▸ hw
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hw'
    refine ⟨((g * u : G) : G ⧸ B), cosetDistance_mk_eq hD h (g * u) ?_,
      cosetDistance_mk_eq hD g (g * u) (by simpa using hu)⟩
    have : h⁻¹ * (g * u) = v⁻¹ := by
      have hh : h = g * (u * v) := by rw [huv]; group
      rw [hh]
      group
    rw [this]
    have := hD.mem_inv hv
    rwa [cs.inv_simple] at this

theorem isWeylDistanceBuilding : IsWeylDistanceBuilding cs (cosetDistance B D) where
  nonempty := ⟨((1 : G) : G ⧸ B)⟩
  eq_one_iff := cosetDistance_eq_one_iff hD
  mul_simple x y z i hyz := cosetDistance_mul_simple hD x y z i hyz
  exists_simple := exists_cosetDistance_simple hD

omit [Group G] hD in
theorem exists_word_of_mem_closure {J : Set ι} {w : W}
    (hw : w ∈ Subgroup.closure (cs.simple '' J)) :
    ∃ l : List ι, (∀ i ∈ l, i ∈ J) ∧ cs.wordProd l = w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨[i], by simpa using hi, cs.wordProd_singleton i⟩
  | one => exact ⟨[], by simp, cs.wordProd_nil⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨l', hl', rfl⟩ := hy
    exact ⟨l ++ l', fun i hi => (List.mem_append.mp hi).elim (hl i) (hl' i),
      cs.wordProd_append l l'⟩
  | inv x _ hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨l.reverse, fun i hi => hl i (List.mem_reverse.mp hi), cs.wordProd_reverse l⟩

omit [Group G] hD in
theorem wordProd_mem_closure {J : Set ι} {l : List ι} (hl : ∀ i ∈ l, i ∈ J) :
    cs.wordProd l ∈ Subgroup.closure (cs.simple '' J) := by
  induction l with
  | nil => exact (Subgroup.closure _).one_mem
  | cons i l ih =>
    rw [cs.wordProd_cons]
    exact (Subgroup.closure _).mul_mem (Subgroup.subset_closure ⟨i, hl i (by simp), rfl⟩)
      (ih fun j hj => hl j (by simp [hj]))

theorem gallery_of_word {J : Set ι} (l : List ι) (hl : ∀ i ∈ l, i ∈ J) (g x : G)
    (hx : x ∈ D (cs.wordProd l)) :
    Relation.ReflTransGen (fun a b => ∃ i ∈ J, cosetDistance B D a b = cs.simple i)
      (g : G ⧸ B) ((g * x : G) : G ⧸ B) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    rw [cs.wordProd_nil, hD.one] at hx
    have : ((g * x : G) : G ⧸ B) = (g : G ⧸ B) := by
      rw [QuotientGroup.eq]
      simpa using B.inv_mem hx
    rw [this]
  | append_singleton l i ih =>
    rw [cs.wordProd_append, cs.wordProd_singleton] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp (hD.subset_mul _ i hx)
    refine Relation.ReflTransGen.tail (ih (fun j hj => hl j (by simp [hj])) y hy)
      ⟨i, hl i (by simp), cosetDistance_mk_eq hD (g * y) (g * (y * z))
        (by simpa [mul_assoc] using hz)⟩

theorem mul_mem_iUnion {J : Set ι} {w : W} (hw : w ∈ Subgroup.closure (cs.simple '' J))
    {x : G} (hx : x ∈ D w) (l : List ι) (hl : ∀ i ∈ l, i ∈ J) {y : G}
    (hy : y ∈ D (cs.wordProd l)) :
    ∃ u ∈ Subgroup.closure (cs.simple '' J), x * y ∈ D u := by
  induction l using List.reverseRecOn generalizing y with
  | nil =>
    rw [cs.wordProd_nil, hD.one] at hy
    exact ⟨w, hw, hD.mul_mem_right hx hy⟩
  | append_singleton l i ih =>
    rw [cs.wordProd_append, cs.wordProd_singleton] at hy
    obtain ⟨y', hy', z, hz, rfl⟩ := Set.mem_mul.mp (hD.subset_mul _ i hy)
    obtain ⟨u, hu, hxy⟩ := ih (fun j hj => hl j (by simp [hj])) hy'
    have hi : cs.simple i ∈ Subgroup.closure (cs.simple '' J) :=
      Subgroup.subset_closure ⟨i, hl i (by simp), rfl⟩
    rw [← mul_assoc]
    rcases (hD.mul_mem_simple hxy hz).1 with h | h
    · exact ⟨u * cs.simple i, (Subgroup.closure _).mul_mem hu hi, h⟩
    · exact ⟨u, hu, h⟩

@[expose] def parabolic (J : Set ι) : Subgroup G where
  carrier := ⋃ w ∈ Subgroup.closure (cs.simple '' J), D w
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_iUnion] at hx hy ⊢
    obtain ⟨w, hw, hx⟩ := hx
    obtain ⟨w', hw', hy⟩ := hy
    obtain ⟨l, hl, rfl⟩ := exists_word_of_mem_closure hw'
    obtain ⟨u, hu, h⟩ := mul_mem_iUnion hD hw hx l hl hy
    exact ⟨u, hu, h⟩
  one_mem' := by
    simp only [Set.mem_iUnion]
    exact ⟨1, (Subgroup.closure _).one_mem, by rw [hD.one]; exact B.one_mem⟩
  inv_mem' {x} hx := by
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨w, hw, hx⟩ := hx
    exact ⟨w⁻¹, (Subgroup.closure _).inv_mem hw, hD.mem_inv hx⟩

theorem coe_parabolic (J : Set ι) :
    (parabolic hD J : Set G) = ⋃ w ∈ Subgroup.closure (cs.simple '' J), D w := rfl

theorem residue_mk (J : Set ι) (g : G) :
    residue cs (cosetDistance B D) J (g : G ⧸ B) =
      (fun x : G => (x : G ⧸ B)) '' (g • (parabolic hD J : Set G)) := by
  ext y
  constructor
  · intro hy
    induction hy with
    | refl => exact ⟨g, ⟨1, (parabolic hD J).one_mem, by simp⟩, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := ih
      obtain ⟨i, hi, hδ⟩ := hbc
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective c
      have hq : (g • p)⁻¹ * k ∈ D (cs.simple i) := (cosetDistance_mk hD _ k _).mp hδ
      have hqP : (g • p)⁻¹ * k ∈ (parabolic hD J : Set G) := by
        rw [coe_parabolic, Set.mem_iUnion₂]
        exact ⟨cs.simple i, Subgroup.subset_closure ⟨i, hi, rfl⟩, hq⟩
      refine ⟨k, ⟨p * ((g • p)⁻¹ * k), (parabolic hD J).mul_mem hp hqP, ?_⟩, rfl⟩
      simp only [smul_eq_mul]
      group
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [coe_parabolic, Set.mem_iUnion₂] at hp
    obtain ⟨w, hw, hpw⟩ := hp
    obtain ⟨l, hl, rfl⟩ := exists_word_of_mem_closure hw
    exact gallery_of_word hD l hl g p hpw

theorem cosetDistance_smul (a : G) (x y : G ⧸ B) :
    cosetDistance B D (a • x) (a • y) = cosetDistance B D x y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul]
  refine cosetDistance_mk_eq hD _ _ ?_
  rw [show (a * g)⁻¹ * (a * h) = g⁻¹ * h by group]
  exact mem_cosetDistance_mk hD g h

theorem residue_singleton_mk (i : ι) (g : G) :
    residue cs (cosetDistance B D) {i} (g : G ⧸ B) =
      insert (g : G ⧸ B) ((fun x : G => (x : G ⧸ B)) '' (g • D (cs.simple i))) := by
  rw [residue_mk hD, coe_parabolic]
  have hcl : Subgroup.closure (cs.simple '' {i}) = Subgroup.zpowers (cs.simple i) := by
    rw [Set.image_singleton, Subgroup.zpowers_eq_closure]
  ext y
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_smul_set, smul_eq_mul,
    Set.mem_iUnion, exists_prop]
  have hsq : cs.simple i ^ (2 : ℤ) = 1 := by rw [zpow_two, cs.simple_mul_simple_self]
  constructor
  · rintro ⟨x, ⟨p, ⟨w, hw, hp⟩, rfl⟩, rfl⟩
    rw [hcl] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, hsq, one_zpow, hD.one] at hp
      rw [QuotientGroup.eq]
      simpa using B.inv_mem hp
    · right
      rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one] at hp
      exact ⟨g * p, ⟨p, hp, rfl⟩, rfl⟩
  · rintro (rfl | ⟨x, ⟨p, hp, rfl⟩, rfl⟩)
    · refine ⟨g * 1, ⟨1, ⟨1, (Subgroup.closure _).one_mem, ?_⟩, rfl⟩, by simp⟩
      rw [hD.one]
      exact B.one_mem
    · exact ⟨g * p, ⟨p, ⟨cs.simple i, Subgroup.subset_closure ⟨i, rfl, rfl⟩, hp⟩, rfl⟩, rfl⟩

theorem ncard_residue_singleton (i : ι)
    (hfin : ((fun x : G => (x : G ⧸ B)) '' D (cs.simple i)).Finite) (y : G ⧸ B) :
    (residue cs (cosetDistance B D) {i} y).ncard =
      ((fun x : G => (x : G ⧸ B)) '' D (cs.simple i)).ncard + 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [residue_singleton_mk hD]
  have himg : (fun x : G => (x : G ⧸ B)) '' (g • D (cs.simple i)) =
      (fun z : G ⧸ B => g • z) '' ((fun x : G => (x : G ⧸ B)) '' D (cs.simple i)) := by
    ext z
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨(x : G ⧸ B), ⟨x, hx, rfl⟩, by rw [MulAction.Quotient.smul_mk, smul_eq_mul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨g * x, ⟨x, hx, rfl⟩, by rw [MulAction.Quotient.smul_mk, smul_eq_mul]⟩
  have hinj : Function.Injective fun z : G ⧸ B => g • z := MulAction.injective g
  have hnot : (g : G ⧸ B) ∉ (fun x : G => (x : G ⧸ B)) '' (g • D (cs.simple i)) := by
    rintro ⟨x, ⟨d, hd, rfl⟩, hx⟩
    have hdB : d ∈ B := by
      have := QuotientGroup.eq.mp hx
      simpa using this
    have h1 : d ∈ D 1 := by rw [hD.one]; exact hdB
    exact simple_ne_one i (hD.eq_of_mem hd h1)
  rw [Set.ncard_insert_of_notMem hnot (himg ▸ hfin.image _), himg,
    Set.ncard_image_of_injective _ hinj]

omit [Group W] hD in
theorem smul_eq_self_iff (a : G) :
    (∀ x : G ⧸ B, a • x = x) ↔ ∀ h : G, h⁻¹ * a * h ∈ B := by
  constructor
  · intro ha h
    have := ha (h : G ⧸ B)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at this
    have := B.inv_mem this
    simpa [mul_assoc] using this
  · intro ha x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have := B.inv_mem (ha h)
    simpa [mul_assoc] using this

end Main

theorem bruhat_double_cosets_give_building {G : Type*} [Group G] (B : Subgroup G)
    (D : W → Set G) (hcoset : ∀ w, ∃ g, D w = (B : Set G) * {g} * B)
    (hpart : ∀ g : G, ∃! w, g ∈ D w) (hone : D 1 = B) (hinv : ∀ w, (D w)⁻¹ = D w⁻¹)
    (hadd : ∀ w i, cs.length (w * cs.simple i) = cs.length w + 1 →
      D w * D (cs.simple i) = D (w * cs.simple i))
    (hsub : ∀ w i, cs.length (w * cs.simple i) + 1 = cs.length w →
      D w * D (cs.simple i) = D (w * cs.simple i) ∪ D w) :
    (∀ (g h : G) (w : W), cosetDistance B D (g : G ⧸ B) (h : G ⧸ B) = w ↔ g⁻¹ * h ∈ D w) ∧
    IsWeylDistanceBuilding cs (cosetDistance B D) ∧
    (∀ J : Set ι, ∃ P : Subgroup G,
      (P : Set G) = ⋃ w ∈ Subgroup.closure (cs.simple '' J), D w ∧
      ∀ g : G, residue cs (cosetDistance B D) J (g : G ⧸ B) =
        (fun x : G => (x : G ⧸ B)) '' (g • (P : Set G))) ∧
    (∀ (a : G) (x y : G ⧸ B), cosetDistance B D (a • x) (a • y) = cosetDistance B D x y) ∧
    (∀ (a : G) (x y : G ⧸ B) (i : ι),
      (cosetDistance B D (a • x) (a • y) = 1 ∨ cosetDistance B D (a • x) (a • y) = cs.simple i) ↔
        (cosetDistance B D x y = 1 ∨ cosetDistance B D x y = cs.simple i)) ∧
    (∀ i : ι, ((fun x : G => (x : G ⧸ B)) '' D (cs.simple i)).Finite → ∀ y : G ⧸ B,
      (residue cs (cosetDistance B D) {i} y).ncard =
        ((fun x : G => (x : G ⧸ B)) '' D (cs.simple i)).ncard + 1) ∧
    ∀ a : G, (∀ x : G ⧸ B, a • x = x) ↔ ∀ h : G, h⁻¹ * a * h ∈ B := by
  have hD : IsBruhatPartition cs B D := ⟨hcoset, hpart, hone, hinv, hadd, hsub⟩
  refine ⟨cosetDistance_mk hD, isWeylDistanceBuilding hD,
    fun J => ⟨parabolic hD J, coe_parabolic hD J, residue_mk hD J⟩, cosetDistance_smul hD,
    fun a x y i => by rw [cosetDistance_smul hD], ncard_residue_singleton hD, smul_eq_self_iff⟩

end CFSG.LieType.Chevalley.CosetBuilding
