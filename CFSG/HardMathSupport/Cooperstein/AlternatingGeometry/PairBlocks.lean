module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

section Model

variable (ι : Type*)

@[expose] def blockFix : Subgroup (Perm (ι × Bool)) where
  carrier := {σ | ∀ x, (σ x).1 = x.1}
  mul_mem' := by
    intro a b ha hb x
    exact (ha (b x)).trans (hb x)
  one_mem' := fun _ => rfl
  inv_mem' := by
    intro a ha x
    have := ha (a⁻¹ x)
    simp at this
    exact this.symm

@[expose] def blockStab : Subgroup (Perm (ι × Bool)) where
  carrier := {σ | ∀ x y, (σ x).1 = (σ y).1 ↔ x.1 = y.1}
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  one_mem' := fun _ _ => Iff.rfl
  inv_mem' := by
    intro a ha x y
    have := ha (a⁻¹ x) (a⁻¹ y)
    simp at this
    exact this.symm

variable {ι}

theorem mem_blockFix {σ : Perm (ι × Bool)} : σ ∈ blockFix ι ↔ ∀ x, (σ x).1 = x.1 := Iff.rfl

theorem mem_blockStab {σ : Perm (ι × Bool)} :
    σ ∈ blockStab ι ↔ ∀ x y, (σ x).1 = (σ y).1 ↔ x.1 = y.1 := Iff.rfl

theorem blockFix_le_blockStab : blockFix ι ≤ blockStab ι := by
  intro σ hσ x y
  rw [mem_blockFix.1 hσ, mem_blockFix.1 hσ]

@[expose] def blockPerm (g : ι → Perm Bool) : Perm (ι × Bool) := prodCongrRight g

theorem blockPerm_apply (g : ι → Perm Bool) (i : ι) (b : Bool) :
    blockPerm g (i, b) = (i, g i b) := rfl

variable (ι)

@[expose] def blockPermHom : (ι → Perm Bool) →* Perm (ι × Bool) where
  toFun := blockPerm
  map_one' := by
    ext ⟨i, b⟩ <;> rfl
  map_mul' g h := by
    ext ⟨i, b⟩ <;> rfl

variable {ι}

theorem blockPermHom_injective : Function.Injective (blockPermHom ι) := by
  intro g h hgh
  funext i
  ext b
  have := congrArg (fun σ : Perm (ι × Bool) => (σ (i, b)).2) hgh
  simpa [blockPermHom, blockPerm_apply] using this

theorem blockPermHom_mem (g : ι → Perm Bool) : blockPermHom ι g ∈ blockFix ι := fun _ => rfl

theorem range_blockPermHom : (blockPermHom ι).range = blockFix ι := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    exact blockPermHom_mem g
  · intro hσ
    have hσ' : σ⁻¹ ∈ blockFix ι := inv_mem hσ
    have key : ∀ (τ : Perm (ι × Bool)), τ ∈ blockFix ι → ∀ (i : ι) (b : Bool),
        (i, (τ (i, b)).2) = τ (i, b) := fun τ hτ i b => Prod.ext (hτ (i, b)).symm rfl
    refine ⟨fun i =>
      { toFun := fun b => (σ (i, b)).2
        invFun := fun b => (σ⁻¹ (i, b)).2
        left_inv := fun b => by
          have h := key σ hσ i b
          have : σ⁻¹ (i, (σ (i, b)).2) = (i, b) := by
            rw [h]; simp
          simp [this]
        right_inv := fun b => by
          have h := key σ⁻¹ hσ' i b
          have : σ (i, (σ⁻¹ (i, b)).2) = (i, b) := by
            rw [h]; simp
          show (σ (i, (σ⁻¹ (i, b)).2)).2 = b
          rw [this] }, ?_⟩
    ext ⟨i, b⟩
    · simp [blockPermHom, blockPerm_apply, (hσ (i, b))]
    · simp [blockPermHom, blockPerm_apply]

theorem sign_blockPerm [Fintype ι] [DecidableEq ι] (g : ι → Perm Bool) : sign (blockPerm g) = ∏ i, sign (g i) :=
  sign_prodCongrRight g

theorem perm_bool_comm (a b : Perm Bool) : a * b = b * a := by
  revert a b; decide

theorem perm_bool_sq (a : Perm Bool) : a * a = 1 := by
  revert a; decide

theorem blockFix_mul_comm {σ τ : Perm (ι × Bool)} (hσ : σ ∈ blockFix ι) (hτ : τ ∈ blockFix ι) :
    σ * τ = τ * σ := by
  rw [← range_blockPermHom] at hσ hτ
  obtain ⟨g, rfl⟩ := hσ
  obtain ⟨h, rfl⟩ := hτ
  rw [← map_mul, ← map_mul]
  congr 1
  funext i
  exact perm_bool_comm _ _

theorem blockFix_sq {σ : Perm (ι × Bool)} (hσ : σ ∈ blockFix ι) : σ * σ = 1 := by
  rw [← range_blockPermHom] at hσ
  obtain ⟨g, rfl⟩ := hσ
  rw [← map_mul, ← map_one (blockPermHom ι)]
  congr 1
  funext i
  exact perm_bool_sq _

end Model

section AltLevel

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev AltB := ↥(alternatingGroup (ι × Bool))

@[expose] def EA : Subgroup (AltB ι) := (blockFix ι).subgroupOf (alternatingGroup (ι × Bool))

@[expose] def NA : Subgroup (AltB ι) := (blockStab ι).subgroupOf (alternatingGroup (ι × Bool))

variable {ι}

theorem mem_EA {x : AltB ι} : x ∈ EA ι ↔ (x : Perm (ι × Bool)) ∈ blockFix ι := Iff.rfl

theorem mem_NA {x : AltB ι} : x ∈ NA ι ↔ (x : Perm (ι × Bool)) ∈ blockStab ι := Iff.rfl

theorem EA_mul_comm {x y : AltB ι} (hx : x ∈ EA ι) (hy : y ∈ EA ι) : x * y = y * x :=
  Subtype.ext (blockFix_mul_comm hx hy)

theorem EA_mul_self {x : AltB ι} (hx : x ∈ EA ι) : x * x = 1 := Subtype.ext (blockFix_sq hx)

@[expose] def blockSign : (ι → Perm Bool) →* ℤˣ := sign.comp (blockPermHom ι)

theorem blockSign_apply (g : ι → Perm Bool) : blockSign g = ∏ i, sign (g i) :=
  sign_blockPerm g

theorem blockSign_surjective [Nonempty ι] : Function.Surjective (blockSign (ι := ι)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · refine ⟨fun i => if i = i₀ then swap false true else 1, ?_⟩
    rw [blockSign_apply]
    have : ∀ i, sign (if i = i₀ then swap false true else (1 : Perm Bool)) =
        if i = i₀ then -1 else 1 := by
      intro i
      split_ifs
      · exact sign_swap (by decide)
      · exact map_one _
    simp only [this]
    simp

theorem card_EA [Nonempty ι] : Nat.card (EA ι) = 2 ^ (Fintype.card ι - 1) := by
  classical
  have h1 : Nat.card (EA ι) = Nat.card ↥(blockFix ι ⊓ alternatingGroup (ι × Bool)) := by
    rw [← Subgroup.subgroupOf_map_subtype]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  have h2 : blockFix ι ⊓ alternatingGroup (ι × Bool) = (blockSign (ι := ι)).ker.map (blockPermHom ι) := by
    rw [← range_blockPermHom, ← Subgroup.map_comap_eq]
    congr 1
  have h3 : Nat.card ↥(blockFix ι ⊓ alternatingGroup (ι × Bool)) = Nat.card (blockSign (ι := ι)).ker := by
    rw [h2]
    exact Subgroup.card_map_of_injective blockPermHom_injective
  have h4 := Subgroup.card_ker_mul_card_range (blockSign (ι := ι))
  rw [MonoidHom.range_eq_top_of_surjective _ blockSign_surjective, Subgroup.card_top] at h4
  have h5 : Nat.card (ι → Perm Bool) = 2 ^ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_perm, Fintype.card_bool]
    rfl
  have h6 : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
  rw [h5, h6] at h4
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 := ⟨Fintype.card ι - 1, by omega⟩
  rw [h1, h3, hm, Nat.add_sub_cancel]
  rw [hm, pow_succ] at h4
  omega

theorem swap_mem_blockFix {u v : ι × Bool} (h : u.1 = v.1) : swap u v ∈ blockFix ι := by
  intro x
  rw [swap_apply_def]
  split_ifs with h1 h2
  · rw [h1]; exact h.symm
  · rw [h2]; exact h
  · rfl

theorem conj_mem_blockFix {σ τ : Perm (ι × Bool)} (hσ : σ ∈ blockStab ι) (hτ : τ ∈ blockFix ι) :
    σ * τ * σ⁻¹ ∈ blockFix ι := by
  intro x
  simp only [Perm.mul_apply]
  have h := (hσ (τ (σ⁻¹ x)) (σ⁻¹ x)).2 (hτ _)
  rw [h]
  simp

theorem exists_even_blockFix {a b : ι × Bool} (hι : 2 ≤ Fintype.card ι) (h : a.1 = b.1) :
    ∃ e : Perm (ι × Bool), e ∈ blockFix ι ∧ e ∈ alternatingGroup (ι × Bool) ∧ e a = b := by
  by_cases hab : a = b
  · exact ⟨1, one_mem _, one_mem _, by simp [hab]⟩
  · obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a.1
    have hz : (j, false) ≠ (j, true) := by simp
    have haz : a ≠ (j, false) := fun h' => hj (by rw [h'])
    have haz' : a ≠ (j, true) := fun h' => hj (by rw [h'])
    refine ⟨swap a b * swap (j, false) (j, true), mul_mem (swap_mem_blockFix h)
      (swap_mem_blockFix rfl), ?_, ?_⟩
    · rw [mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hz]
      decide
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne haz haz', swap_apply_left]

theorem mem_blockStab_of_normalizer {x : AltB ι} (hι : 2 ≤ Fintype.card ι)
    (hx : x ∈ Subgroup.normalizer ((EA ι : Subgroup (AltB ι)) : Set (AltB ι))) {a b : ι × Bool} (h : a.1 = b.1) :
    ((x : Perm (ι × Bool)) a).1 = ((x : Perm (ι × Bool)) b).1 := by
  obtain ⟨e, he, hea, hab⟩ := exists_even_blockFix hι h
  have hmem : (⟨e, hea⟩ : AltB ι) ∈ EA ι := he
  have := ((Subgroup.mem_normalizer_iff.1 hx) _).1 hmem
  have h2 : ((x : Perm (ι × Bool)) * e * (x : Perm (ι × Bool))⁻¹) ∈ blockFix ι := this
  have h3 := h2 ((x : Perm (ι × Bool)) a)
  have h4 : (((x : Perm (ι × Bool)) * e * (x : Perm (ι × Bool))⁻¹) ((x : Perm (ι × Bool)) a)) =
      (x : Perm (ι × Bool)) b := by
    simp [Perm.mul_apply, hab]
  rw [h4] at h3
  exact h3.symm

theorem normalizer_EA (hι : 2 ≤ Fintype.card ι) : Subgroup.normalizer ((EA ι : Subgroup (AltB ι)) : Set (AltB ι)) = NA ι := by
  ext x
  constructor
  · intro hx a b
    have hx' : x⁻¹ ∈ Subgroup.normalizer ((EA ι : Subgroup (AltB ι)) : Set (AltB ι)) := inv_mem hx
    constructor
    · intro hab
      have := mem_blockStab_of_normalizer hι hx' (a := (x : Perm (ι × Bool)) a)
        (b := (x : Perm (ι × Bool)) b) hab
      simpa using this
    · exact mem_blockStab_of_normalizer hι hx
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' : (x⁻¹ : AltB ι) ∈ NA ι := inv_mem hx
    constructor
    · intro hy
      exact conj_mem_blockFix hx hy
    · intro hy
      have := conj_mem_blockFix hx' hy
      change (y : Perm (ι × Bool)) ∈ blockFix ι
      simpa [mul_assoc] using this

@[expose] noncomputable def blockMap (σ : Perm (ι × Bool)) (hσ : σ ∈ blockStab ι) : Perm ι :=
  Equiv.ofBijective (fun a => (σ (a, false)).1)
    (Finite.injective_iff_bijective.1 (fun a a' h => (hσ (a, false) (a', false)).1 h))

theorem blockMap_apply {σ : Perm (ι × Bool)} (hσ : σ ∈ blockStab ι) (x : ι × Bool) :
    blockMap σ hσ x.1 = (σ x).1 :=
  (hσ (x.1, false) x).2 rfl

@[expose] noncomputable def blockAction : NA ι →* Perm ι where
  toFun x := blockMap (x.1 : Perm (ι × Bool)) (mem_NA.1 x.2)
  map_one' := by
    ext a
    rfl
  map_mul' x y := by
    ext a
    have h3 : blockMap (y.1.1 : Perm (ι × Bool)) (mem_NA.1 y.2) a = (y.1.1 (a, false)).1 :=
      blockMap_apply (mem_NA.1 y.2) (a, false)
    have h1 : blockMap (x.1.1 : Perm (ι × Bool)) (mem_NA.1 x.2) (y.1.1 (a, false)).1 =
        (x.1.1 (y.1.1 (a, false))).1 := blockMap_apply (mem_NA.1 x.2) _
    show (x.1.1 (y.1.1 (a, false))).1 = blockMap (x.1.1 : Perm (ι × Bool)) (mem_NA.1 x.2)
      (blockMap (y.1.1 : Perm (ι × Bool)) (mem_NA.1 y.2) a)
    rw [h3, h1]

theorem blockAction_apply (x : NA ι) (p : ι × Bool) :
    blockAction x p.1 = (x.1.1 p).1 :=
  blockMap_apply (mem_NA.1 x.2) p

theorem blockAction_surjective : Function.Surjective (blockAction (ι := ι)) := by
  intro π
  have hsign : sign (prodCongrLeft fun _ : Bool => π) = 1 := by
    rw [sign_prodCongrLeft, Fintype.prod_bool]
    exact Int.units_mul_self _
  have hfst : ∀ p : ι × Bool, (prodCongrLeft (fun _ : Bool => π) p).1 = π p.1 := fun _ => rfl
  have hstab : (prodCongrLeft fun _ : Bool => π) ∈ blockStab ι := by
    intro x y
    rw [hfst, hfst]
    exact π.injective.eq_iff
  refine ⟨⟨⟨prodCongrLeft fun _ : Bool => π, mem_alternatingGroup.2 hsign⟩, hstab⟩, ?_⟩
  ext a
  have := blockAction_apply (⟨⟨prodCongrLeft fun _ : Bool => π, mem_alternatingGroup.2 hsign⟩,
    hstab⟩ : NA ι) (a, false)
  simpa using this.trans (hfst (a, false))

theorem ker_blockAction : (blockAction (ι := ι)).ker = (EA ι).subgroupOf (NA ι) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h p
    have := blockAction_apply x p
    rw [h] at this
    exact this.symm
  · intro h
    ext a
    show blockAction x a = a
    exact (blockAction_apply x (a, false)).trans (h (a, false))

theorem le_EA_of_normal_isPGroup (hι : 5 ≤ Fintype.card ι) {Q : Subgroup (NA ι)} [Q.Normal]
    (hQ : IsPGroup 2 Q) : Q ≤ (EA ι).subgroupOf (NA ι) := by
  rw [← ker_blockAction]
  intro q hq
  by_contra hq1
  have hnorm : (Q.map blockAction).Normal := Subgroup.Normal.map ‹Q.Normal› _ blockAction_surjective
  have hp : IsPGroup 2 (Q.map blockAction) := hQ.map _
  have hnt : Nontrivial (Q.map blockAction) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨blockAction q, q, hq, rfl⟩, fun h => hq1 ?_⟩
    exact MonoidHom.mem_ker.2 (congrArg Subtype.val h)
  have hle := alternatingGroup_le_of_normal (α := ι) (by rwa [Nat.card_eq_fintype_card])
    (N := Q.map blockAction) hnt
  have hdvd : Nat.card (alternatingGroup ι) ∣ Nat.card (Q.map blockAction) :=
    Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hι2 : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := ι)
  rw [Nat.card_eq_fintype_card (α := Perm ι), Fintype.card_perm] at h2
  have h3 : 3 ∣ Nat.factorial (Fintype.card ι) :=
    Nat.dvd_factorial (by norm_num) (by omega)
  have h4 : 3 ∣ Nat.card (alternatingGroup ι) := by
    have : 3 ∣ 2 * Nat.card (alternatingGroup ι) := by rwa [h2]
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
  have h5 : 3 ∣ 2 ^ k := hk ▸ h4.trans hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
  omega

end AltLevel

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
