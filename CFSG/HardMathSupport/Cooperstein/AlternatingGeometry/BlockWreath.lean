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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

section Wreath

variable (ι κ : Type*)

@[expose] def wPermHom : (ι → Perm κ) →* Perm (ι × κ) where
  toFun g := prodCongrRight g
  map_one' := by
    ext ⟨i, k⟩ <;> rfl
  map_mul' g h := by
    ext ⟨i, k⟩ <;> rfl

variable {ι κ}

theorem wPermHom_apply (g : ι → Perm κ) (i : ι) (k : κ) : wPermHom ι κ g (i, k) = (i, g i k) :=
  rfl

theorem wPermHom_injective : Function.Injective (wPermHom ι κ) := by
  intro g h hgh
  funext i
  ext k
  have := congrArg (fun σ : Perm (ι × κ) => (σ (i, k)).2) hgh
  simpa [wPermHom_apply] using this

theorem mem_range_wPermHom {σ : Perm (ι × κ)} :
    σ ∈ (wPermHom ι κ).range ↔ ∀ x, (σ x).1 = x.1 := by
  constructor
  · rintro ⟨g, rfl⟩ x
    rfl
  · intro hσ
    have hσ' : ∀ x, (σ⁻¹ x).1 = x.1 := by
      intro x
      have := hσ (σ⁻¹ x)
      simp at this
      exact this.symm
    have key : ∀ (τ : Perm (ι × κ)), (∀ x, (τ x).1 = x.1) → ∀ (i : ι) (k : κ),
        (i, (τ (i, k)).2) = τ (i, k) := fun τ hτ i k => Prod.ext (hτ (i, k)).symm rfl
    refine ⟨fun i =>
      { toFun := fun k => (σ (i, k)).2
        invFun := fun k => (σ⁻¹ (i, k)).2
        left_inv := fun k => by
          have h := key σ hσ i k
          have : σ⁻¹ (i, (σ (i, k)).2) = (i, k) := by
            rw [h]; simp
          simp [this]
        right_inv := fun k => by
          have h := key σ⁻¹ hσ' i k
          have : σ (i, (σ⁻¹ (i, k)).2) = (i, k) := by
            rw [h]; simp
          show (σ (i, (σ⁻¹ (i, k)).2)).2 = k
          rw [this] }, ?_⟩
    ext ⟨i, k⟩
    · simp [wPermHom_apply, hσ (i, k)]
    · simp [wPermHom_apply]

end Wreath

section Block

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] def wFix (D : Subgroup (Perm κ)) (ι : Type*) : Subgroup (Perm (ι × κ)) :=
  (Subgroup.pi Set.univ fun _ : ι => D).map (wPermHom ι κ)

theorem mem_wFix {D : Subgroup (Perm κ)} {σ : Perm (ι × κ)} :
    σ ∈ wFix D ι ↔ ∃ g : ι → Perm κ, (∀ i, g i ∈ D) ∧ wPermHom ι κ g = σ := by
  unfold wFix
  simp only [Subgroup.mem_map, Subgroup.mem_pi, Set.mem_univ, true_implies]

theorem sign_wPermHom (g : ι → Perm κ) : sign (wPermHom ι κ g) = ∏ i, sign (g i) :=
  sign_prodCongrRight g

theorem wFix_apply_fst {D : Subgroup (Perm κ)} {σ : Perm (ι × κ)} (hσ : σ ∈ wFix D ι)
    (x : ι × κ) : (σ x).1 = x.1 := by
  obtain ⟨g, -, rfl⟩ := mem_wFix.1 hσ
  rfl

structure WreathHyp (D : Subgroup (Perm κ)) : Prop where
  pgroup : IsPGroup 2 D
  trans : ∀ a b : κ, ∃ d ∈ D, d a = b
  odd : ∃ d ∈ D, sign d = -1
  selfNorm : ∀ s : Perm κ, (∀ d ∈ D, s * d * s⁻¹ ∈ D) → s ∈ D

theorem exists_even_wFix_component {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) (i : ι) {d : Perm κ} (hd : d ∈ D) :
    ∃ g : ι → Perm κ, (∀ j, g j ∈ D) ∧ g i = d ∧
      wPermHom ι κ g ∈ alternatingGroup (ι × κ) := by
  classical
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  obtain ⟨do', hdo, hdo_sign⟩ := hD.odd
  set d' : Perm κ := if sign d = 1 then 1 else do' with hd'
  have hd'D : d' ∈ D := by
    rw [hd']; split_ifs
    · exact one_mem _
    · exact hdo
  have hsign : sign d * sign d' = 1 := by
    rw [hd']
    split_ifs with h
    · simp [h]
    · rcases Int.units_eq_one_or (sign d) with h' | h'
      · exact absurd h' h
      · rw [h', hdo_sign]; decide
  refine ⟨fun l => if l = i then d else if l = j then d' else 1, ?_, ?_, ?_⟩
  · intro l
    show (if l = i then d else if l = j then d' else 1) ∈ D
    split_ifs
    · exact hd
    · exact hd'D
    · exact one_mem _
  · simp
  · rw [mem_alternatingGroup, sign_wPermHom]
    rw [Fintype.prod_eq_mul i j (Ne.symm hji)]
    · simp [hji, hsign]
    · intro x hx
      simp [hx.1, hx.2]

theorem exists_even_wFix_apply {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) {x y : ι × κ} (h : x.1 = y.1) :
    ∃ e ∈ wFix D ι, e ∈ alternatingGroup (ι × κ) ∧ e x = y := by
  obtain ⟨d, hdD, hdx⟩ := hD.trans x.2 y.2
  obtain ⟨g, hgD, hgi, hgalt⟩ := exists_even_wFix_component hD hι x.1 hdD
  refine ⟨wPermHom ι κ g, mem_wFix.2 ⟨g, hgD, rfl⟩, hgalt, ?_⟩
  obtain ⟨i, k⟩ := x
  obtain ⟨i', k'⟩ := y
  simp only at h hdx
  subst h
  simp [wPermHom_apply, hgi, hdx]

@[expose] def wStab (ι κ : Type*) : Subgroup (Perm (ι × κ)) where
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

theorem mem_wStab {σ : Perm (ι × κ)} : σ ∈ wStab ι κ ↔ ∀ x y, (σ x).1 = (σ y).1 ↔ x.1 = y.1 :=
  Iff.rfl

@[expose] noncomputable def wBlockMap [Nonempty κ] (σ : Perm (ι × κ)) (hσ : σ ∈ wStab ι κ) :
    Perm ι :=
  Equiv.ofBijective (fun a => (σ (a, Classical.arbitrary κ)).1)
    (Finite.injective_iff_bijective.1 (fun _ _ h => (hσ _ _).1 h))

theorem wBlockMap_apply [Nonempty κ] {σ : Perm (ι × κ)} (hσ : σ ∈ wStab ι κ) (x : ι × κ) :
    wBlockMap σ hσ x.1 = (σ x).1 :=
  (hσ (x.1, Classical.arbitrary κ) x).2 rfl

abbrev AltW (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :=
  ↥(alternatingGroup (ι × κ))

@[expose] def wR (D : Subgroup (Perm κ)) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (AltW ι κ) :=
  (wFix D ι).subgroupOf (alternatingGroup (ι × κ))

@[expose] def wN (D : Subgroup (Perm κ)) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (AltW ι κ) :=
  Subgroup.normalizer ((wR D ι : Subgroup (AltW ι κ)) : Set (AltW ι κ))

theorem mem_wR {D : Subgroup (Perm κ)} {x : AltW ι κ} :
    x ∈ wR D ι ↔ (x : Perm (ι × κ)) ∈ wFix D ι := Iff.rfl

theorem apply_fst_eq_of_mem_wN {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) {x : AltW ι κ} (hx : x ∈ wN D ι) {a b : ι × κ} (h : a.1 = b.1) :
    ((x : Perm (ι × κ)) a).1 = ((x : Perm (ι × κ)) b).1 := by
  obtain ⟨e, he, hea, hab⟩ := exists_even_wFix_apply hD hι h
  have hmem : (⟨e, hea⟩ : AltW ι κ) ∈ wR D ι := he
  have h2 : ((x : Perm (ι × κ)) * e * (x : Perm (ι × κ))⁻¹) ∈ wFix D ι :=
    ((Subgroup.mem_normalizer_iff.1 hx) _).1 hmem
  have h3 := wFix_apply_fst h2 ((x : Perm (ι × κ)) a)
  have h4 : (((x : Perm (ι × κ)) * e * (x : Perm (ι × κ))⁻¹) ((x : Perm (ι × κ)) a)) =
      (x : Perm (ι × κ)) b := by
    simp [Perm.mul_apply, hab]
  rw [h4] at h3
  exact h3.symm

theorem mem_wStab_of_mem_wN {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) {x : AltW ι κ} (hx : x ∈ wN D ι) :
    (x : Perm (ι × κ)) ∈ wStab ι κ := by
  intro a b
  have hx' : x⁻¹ ∈ wN D ι := inv_mem hx
  constructor
  · intro hab
    have := apply_fst_eq_of_mem_wN hD hι hx' (a := (x : Perm (ι × κ)) a)
      (b := (x : Perm (ι × κ)) b) hab
    simpa using this
  · exact apply_fst_eq_of_mem_wN hD hι hx

@[expose] noncomputable def wAction [Nonempty κ] {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) : ↥(wN D ι) →* Perm ι where
  toFun x := wBlockMap (x.1.1 : Perm (ι × κ)) (mem_wStab_of_mem_wN hD hι x.2)
  map_one' := by
    ext a
    rfl
  map_mul' x y := by
    ext a
    have h3 : wBlockMap (y.1.1 : Perm (ι × κ)) (mem_wStab_of_mem_wN hD hι y.2) a =
        (y.1.1 (a, Classical.arbitrary κ)).1 :=
      wBlockMap_apply (mem_wStab_of_mem_wN hD hι y.2) (a, Classical.arbitrary κ)
    have h1 : wBlockMap (x.1.1 : Perm (ι × κ)) (mem_wStab_of_mem_wN hD hι x.2)
        (y.1.1 (a, Classical.arbitrary κ)).1 =
        (x.1.1 (y.1.1 (a, Classical.arbitrary κ))).1 :=
      wBlockMap_apply (mem_wStab_of_mem_wN hD hι x.2) _
    show (x.1.1 (y.1.1 (a, Classical.arbitrary κ))).1 =
      wBlockMap (x.1.1 : Perm (ι × κ)) (mem_wStab_of_mem_wN hD hι x.2)
        (wBlockMap (y.1.1 : Perm (ι × κ)) (mem_wStab_of_mem_wN hD hι y.2) a)
    rw [h3, h1]

theorem wAction_apply [Nonempty κ] {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) (x : ↥(wN D ι)) (p : ι × κ) :
    wAction hD hι x p.1 = (x.1.1 p).1 :=
  wBlockMap_apply (mem_wStab_of_mem_wN hD hι x.2) p

theorem mem_wFix_of_mem_ker [Nonempty κ] {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) {x : ↥(wN D ι)} (hx : x ∈ (wAction hD hι).ker) :
    (x.1.1 : Perm (ι × κ)) ∈ wFix D ι := by
  have hfst : ∀ p : ι × κ, (x.1.1 p).1 = p.1 := by
    intro p
    have := wAction_apply hD hι x p
    rw [MonoidHom.mem_ker.1 hx] at this
    exact this.symm
  have hrange : (x.1.1 : Perm (ι × κ)) ∈ (wPermHom ι κ).range := by
    exact mem_range_wPermHom.2 hfst
  obtain ⟨s, hs⟩ := hrange
  have hsD : ∀ i, s i ∈ D := by
    intro i
    apply hD.selfNorm
    intro d hd
    obtain ⟨g, hgD, hgi, hgalt⟩ := exists_even_wFix_component hD hι i hd
    have hmem : (⟨wPermHom ι κ g, hgalt⟩ : AltW ι κ) ∈ wR D ι := mem_wFix.2 ⟨g, hgD, rfl⟩
    have h2 : ((x.1.1 : Perm (ι × κ)) * wPermHom ι κ g * (x.1.1 : Perm (ι × κ))⁻¹) ∈ wFix D ι :=
      ((Subgroup.mem_normalizer_iff.1 x.2) _).1 hmem
    obtain ⟨g', hg'D, hg'⟩ := mem_wFix.1 h2
    rw [← hs, ← map_inv, ← map_mul, ← map_mul] at hg'
    have := wPermHom_injective hg'
    have hi := congrFun this i
    have : g' i = s i * d * (s i)⁻¹ := by
      rw [hi]
      simp [hgi]
    rw [← this]
    exact hg'D i
  exact mem_wFix.2 ⟨s, hsD, hs⟩

theorem isPGroup_ker_wAction [Nonempty κ] {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hι : 2 ≤ Fintype.card ι) : IsPGroup 2 (wAction hD hι).ker := by
  obtain ⟨m, hm⟩ := hD.pgroup.exists_card_eq
  intro g
  refine ⟨m, ?_⟩
  obtain ⟨s, hsD, hs⟩ := mem_wFix.1 (mem_wFix_of_mem_ker hD hι g.2)
  have hpow : ∀ i, (s i) ^ (2 ^ m) = 1 := by
    intro i
    have h1 : (⟨s i, hsD i⟩ : ↥D) ^ Nat.card ↥D = 1 := pow_card_eq_one'
    rw [hm] at h1
    simpa using congrArg Subtype.val h1
  have hs2 : (g.1.1 : Perm (ι × κ)) ^ (2 ^ m) = 1 := by
    rw [← hs, ← map_pow]
    have : s ^ (2 ^ m) = 1 := by
      funext i
      simpa using hpow i
    rw [this, map_one]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simpa using hs2

@[expose] def wLift (π : Perm ι) : Perm (ι × κ) := prodCongrLeft fun _ : κ => π

theorem wLift_apply (π : Perm ι) (i : ι) (k : κ) : wLift π (i, k) = (π i, k) := rfl

theorem wLift_inv (π : Perm ι) : (wLift π : Perm (ι × κ))⁻¹ = wLift π⁻¹ := by
  refine inv_eq_of_mul_eq_one_left ?_
  ext ⟨i, k⟩ <;> simp [wLift_apply, Perm.mul_apply]

theorem wLift_mem_wStab (π : Perm ι) : (wLift π : Perm (ι × κ)) ∈ wStab ι κ := by
  intro x y
  show π x.1 = π y.1 ↔ x.1 = y.1
  exact π.injective.eq_iff

theorem wLift_conj_mem_wFix {D : Subgroup (Perm κ)} (π : Perm ι) {σ : Perm (ι × κ)}
    (hσ : σ ∈ wFix D ι) : wLift π * σ * (wLift π)⁻¹ ∈ wFix D ι := by
  obtain ⟨g, hgD, rfl⟩ := mem_wFix.1 hσ
  refine mem_wFix.2 ⟨fun i => g (π⁻¹ i), fun i => hgD _, ?_⟩
  rw [wLift_inv]
  ext ⟨i, k⟩ <;> simp [wLift_apply, wPermHom_apply]

theorem wLift_sign (hκ : Even (Fintype.card κ)) (π : Perm ι) : sign (wLift π : Perm (ι × κ)) = 1 := by
  have : sign (wLift π : Perm (ι × κ)) = ∏ _k : κ, sign π := sign_prodCongrLeft _
  rw [this, Finset.prod_const, Finset.card_univ]
  rcases Int.units_eq_one_or (sign π) with h | h
  · rw [h]; simp
  · rw [h]; exact Even.neg_one_pow hκ

theorem wLift_mem_wN {D : Subgroup (Perm κ)} (hκ : Even (Fintype.card κ)) (π : Perm ι) :
    (⟨wLift π, mem_alternatingGroup.2 (wLift_sign hκ π)⟩ : AltW ι κ) ∈ wN D ι := by
  rw [wN, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact wLift_conj_mem_wFix π hh
  · intro hh
    have := wLift_conj_mem_wFix (D := D) π⁻¹ hh
    rw [← wLift_inv] at this
    show (h : Perm (ι × κ)) ∈ wFix D ι
    simpa [mul_assoc] using this

theorem exists_blockAction [Nonempty κ] {D : Subgroup (Perm κ)} (hD : WreathHyp D)
    (hκ : Even (Fintype.card κ)) (hι : 2 ≤ Fintype.card ι) :
    ∃ ρ : ↥(wN D ι) →* Perm ι, Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  refine ⟨wAction hD hι, ?_, isPGroup_ker_wAction hD hι⟩
  intro π
  refine ⟨⟨_, wLift_mem_wN hκ π⟩, ?_⟩
  ext a
  have := wAction_apply hD hι ⟨_, wLift_mem_wN (D := D) hκ π⟩ (a, Classical.arbitrary κ)
  exact this

end Block

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
