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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Semidihedral.Principal

@[expose] def centralIdempotents (A : Type*) [Ring A] : Set A :=
  {e | e ∈ Subring.center A ∧ IsIdempotentElem e}

@[expose] def IsPrimitiveCentralIdempotent {A : Type*} [Ring A] (e : A) : Prop :=
  e ∈ centralIdempotents A ∧ e ≠ 0 ∧
    ∀ e₁ ∈ centralIdempotents A, ∀ e₂ ∈ centralIdempotents A, e₁ * e₂ = 0 → e₁ + e₂ = e →
      e₁ = 0 ∨ e₂ = 0

section Basic

variable {A B : Type*} [Ring A] [Ring B]

theorem zero_mem_centralIdempotents : (0 : A) ∈ centralIdempotents A :=
  ⟨Subring.zero_mem _, IsIdempotentElem.zero⟩

theorem one_mem_centralIdempotents : (1 : A) ∈ centralIdempotents A :=
  ⟨Subring.one_mem _, IsIdempotentElem.one⟩

theorem mul_mem_centralIdempotents {e e' : A} (he : e ∈ centralIdempotents A)
    (he' : e' ∈ centralIdempotents A) : e * e' ∈ centralIdempotents A :=
  ⟨Subring.mul_mem _ he.1 he'.1,
    he.2.mul_of_commute ((Subring.mem_center_iff.mp he.1 e').symm) he'.2⟩

theorem one_sub_mem_centralIdempotents {e : A} (he : e ∈ centralIdempotents A) :
    1 - e ∈ centralIdempotents A :=
  ⟨Subring.sub_mem _ (Subring.one_mem _) he.1, he.2.one_sub⟩

theorem add_mem_centralIdempotents {e e' : A} (he : e ∈ centralIdempotents A)
    (he' : e' ∈ centralIdempotents A) (horth : e * e' = 0) : e + e' ∈ centralIdempotents A := by
  refine ⟨Subring.add_mem _ he.1 he'.1, ?_⟩
  have hcomm : e' * e = 0 := by rw [Subring.mem_center_iff.mp he.1 e', horth]
  unfold IsIdempotentElem
  rw [add_mul, mul_add, mul_add, horth, hcomm, he.2.eq, he'.2.eq, add_zero, zero_add]

theorem map_mem_centralIdempotents (f : A →+* B) (hf : Function.Surjective f) {e : A}
    (he : e ∈ centralIdempotents A) : f e ∈ centralIdempotents B := by
  refine ⟨Subring.mem_center_iff.mpr fun y => ?_, he.2.map f⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subring.mem_center_iff.mp he.1 x]

structure CentralIdempotentCorrespondence (f : A →+* B) : Prop where
  bijOn : Set.BijOn f (centralIdempotents A) (centralIdempotents B)
  preserves_mul : ∀ e ∈ centralIdempotents A, ∀ e' ∈ centralIdempotents A, f (e * e') = f e * f e'
  preserves_one_sub : ∀ e ∈ centralIdempotents A, f (1 - e) = 1 - f e
  preserves_add : ∀ e ∈ centralIdempotents A, ∀ e' ∈ centralIdempotents A, e * e' = 0 →
    f (e + e') = f e + f e'
  orthogonal_iff : ∀ e ∈ centralIdempotents A, ∀ e' ∈ centralIdempotents A,
    e * e' = 0 ↔ f e * f e' = 0
  inverse_preserves : ∀ ē ∈ centralIdempotents B, ∀ ē' ∈ centralIdempotents B,
    Function.invFunOn f (centralIdempotents A) (ē * ē') =
        Function.invFunOn f (centralIdempotents A) ē *
          Function.invFunOn f (centralIdempotents A) ē' ∧
      Function.invFunOn f (centralIdempotents A) (1 - ē) =
        1 - Function.invFunOn f (centralIdempotents A) ē ∧
      (ē * ē' = 0 → Function.invFunOn f (centralIdempotents A) ē *
          Function.invFunOn f (centralIdempotents A) ē' = 0 ∧
        Function.invFunOn f (centralIdempotents A) (ē + ē') =
          Function.invFunOn f (centralIdempotents A) ē +
            Function.invFunOn f (centralIdempotents A) ē')
  primitive_iff : ∀ e ∈ centralIdempotents A,
    IsPrimitiveCentralIdempotent e ↔ IsPrimitiveCentralIdempotent (f e)
  primitive_bijOn : Set.BijOn f {e : A | IsPrimitiveCentralIdempotent e}
    {e : B | IsPrimitiveCentralIdempotent e}

theorem CentralIdempotentCorrespondence.of_bijOn (f : A →+* B)
    (hbij : Set.BijOn f (centralIdempotents A) (centralIdempotents B)) :
    CentralIdempotentCorrespondence f := by
  have hzero : ∀ e ∈ centralIdempotents A, f e = 0 → e = 0 := fun e he h =>
    hbij.injOn he zero_mem_centralIdempotents (h.trans (map_zero f).symm)
  have horth : ∀ e ∈ centralIdempotents A, ∀ e' ∈ centralIdempotents A,
      e * e' = 0 ↔ f e * f e' = 0 := by
    intro e he e' he'
    constructor
    · intro h
      rw [← map_mul, h, map_zero]
    · intro h
      exact hzero _ (mul_mem_centralIdempotents he he') (by rw [map_mul, h])
  have hprim : ∀ e ∈ centralIdempotents A,
      IsPrimitiveCentralIdempotent e ↔ IsPrimitiveCentralIdempotent (f e) := by
    intro e he
    constructor
    · rintro ⟨-, hne, hdec⟩
      refine ⟨hbij.mapsTo he, fun h => hne (hzero e he h), ?_⟩
      intro ē₁ hē₁ ē₂ hē₂ hmul hsum
      obtain ⟨e₁, he₁, rfl⟩ := hbij.surjOn hē₁
      obtain ⟨e₂, he₂, rfl⟩ := hbij.surjOn hē₂
      have h12 : e₁ * e₂ = 0 := (horth e₁ he₁ e₂ he₂).mpr hmul
      have hsum' : e₁ + e₂ = e := hbij.injOn (add_mem_centralIdempotents he₁ he₂ h12) he
        (by rw [map_add, hsum])
      rcases hdec e₁ he₁ e₂ he₂ h12 hsum' with h | h
      · left
        rw [h, map_zero]
      · right
        rw [h, map_zero]
    · rintro ⟨-, hne, hdec⟩
      refine ⟨he, fun h => hne (by rw [h, map_zero]), ?_⟩
      intro e₁ he₁ e₂ he₂ hmul hsum
      rcases hdec (f e₁) (hbij.mapsTo he₁) (f e₂) (hbij.mapsTo he₂) (by rw [← map_mul, hmul,
        map_zero]) (by rw [← map_add, hsum]) with h | h
      · exact Or.inl (hzero e₁ he₁ h)
      · exact Or.inr (hzero e₂ he₂ h)
  have hinv : ∀ ē ∈ centralIdempotents B,
      Function.invFunOn f (centralIdempotents A) ē ∈ centralIdempotents A ∧
        f (Function.invFunOn f (centralIdempotents A) ē) = ē := fun ē hē =>
    ⟨Function.invFunOn_mem (hbij.surjOn hē), Function.invFunOn_eq (hbij.surjOn hē)⟩
  refine ⟨hbij, fun e _ e' _ => map_mul f e e', fun e _ => by rw [map_sub, map_one],
    fun e _ e' _ _ => map_add f e e', horth, ?_, hprim, ?_⟩
  · intro ē hē ē' hē'
    obtain ⟨hg, hfg⟩ := hinv ē hē
    obtain ⟨hg', hfg'⟩ := hinv ē' hē'
    refine ⟨?_, ?_, fun hmul => ?_⟩
    · obtain ⟨hgm, hfgm⟩ := hinv _ (mul_mem_centralIdempotents hē hē')
      exact hbij.injOn hgm (mul_mem_centralIdempotents hg hg') (by rw [hfgm, map_mul, hfg, hfg'])
    · obtain ⟨hgc, hfgc⟩ := hinv _ (one_sub_mem_centralIdempotents hē)
      exact hbij.injOn hgc (one_sub_mem_centralIdempotents hg)
        (by rw [hfgc, map_sub, map_one, hfg])
    · have h0 : Function.invFunOn f (centralIdempotents A) ē *
          Function.invFunOn f (centralIdempotents A) ē' = 0 :=
        (horth _ hg _ hg').mpr (by rw [hfg, hfg', hmul])
      refine ⟨h0, ?_⟩
      obtain ⟨hga, hfga⟩ := hinv _ (add_mem_centralIdempotents hē hē' hmul)
      exact hbij.injOn hga (add_mem_centralIdempotents hg hg' h0)
        (by rw [hfga, map_add, hfg, hfg'])
  · refine ⟨fun e he => (hprim e he.1).mp he, ?_, ?_⟩
    · intro e he e' he' h
      exact hbij.injOn he.1 he'.1 h
    · intro ē hē
      obtain ⟨e, he, rfl⟩ := hbij.surjOn hē.1
      exact ⟨e, (hprim e he).mpr hē, rfl⟩

end Basic

section Nilpotent

variable {A B : Type*} [Ring A] [Ring B]

theorem mem_span_range_central_iff {m : ℕ} {c : Fin m → A} (hc : ∀ i, c i ∈ Subring.center A)
    {x : A} : x ∈ Ideal.span (Set.range c) ↔ ∃ a : Fin m → A, x = ∑ i, c i * a i := by
  rw [Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, Finset.sum_congr rfl fun i _ => (Subring.mem_center_iff.mp (hc i) (a i))⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, Finset.sum_congr rfl fun i _ => (Subring.mem_center_iff.mp (hc i) (a i))⟩

theorem isTwoSided_span_central {m : ℕ} (c : Fin m → A) (hc : ∀ i, c i ∈ Subring.center A) :
    (Ideal.span (Set.range c)).IsTwoSided := by
  refine Ideal.IsTwoSided.mk fun {a} b ha => ?_
  obtain ⟨r, rfl⟩ := (mem_span_range_central_iff hc).mp ha
  rw [Finset.sum_mul]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [mul_assoc, ← Subring.mem_center_iff.mp (hc i) (r i * b)]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem idempotent_eq_zero_of_mem_nilpotent {J : Ideal A} {d : ℕ} (hd : 1 ≤ d)
    (hnil : J ^ d = ⊥) {x : A} (hx : IsIdempotentElem x) (hxJ : x ∈ J) : x = 0 := by
  have hpow := Ideal.pow_mem_pow hxJ d
  rw [hnil, Ideal.mem_bot] at hpow
  rw [← hx.pow_succ_eq (d - 1), Nat.sub_add_cancel hd]
  exact hpow

theorem corner_mem_span_central_pow {m : ℕ} (c : Fin m → A) (hc : ∀ i, c i ∈ Subring.center A)
    {u v : A} (hu : IsIdempotentElem u) (hv : IsIdempotentElem v)
    (hJ : ∀ x, u * x * v ∈ Ideal.span (Set.range c)) (n : ℕ) :
    ∀ x, u * x * v ∈ Ideal.span (Set.range c) ^ n := by
  induction n with
  | zero =>
    intro x
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro x
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hJ x)
    have hexp : u * x * v = ∑ i, (u * a i * v) * c i := by
      calc u * x * v = (u * u) * x * (v * v) := by rw [hu.eq, hv.eq]
        _ = u * (u * x * v) * v := by simp only [mul_assoc]
        _ = u * (∑ i, a i * c i) * v := by rw [ha]
        _ = ∑ i, (u * a i * v) * c i := by
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            have hcv : c i * v = v * c i := (Subring.mem_center_iff.mp (hc i) v).symm
            simp only [mul_assoc, hcv]
    rw [hexp, Submodule.pow_succ]
    exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_mul (ih (a i)) (Ideal.subset_span ⟨i, rfl⟩)

theorem centralIdempotentCorrespondence_of_ker_eq_span_central (k : Type*) [Field k]
    [Algebra k A] (p : ℕ) [Fact p.Prime] [CharP k p] (f : A →+* B) (hf : Function.Surjective f)
    {m : ℕ} (c : Fin m → A) (hc : ∀ i, c i ∈ Subring.center A)
    (hker : RingHom.ker f = Ideal.span (Set.range c))
    {d : ℕ} (hd : 1 ≤ d) (hnil : Ideal.span (Set.range c) ^ d = ⊥) :
    CentralIdempotentCorrespondence f := by
  set J := Ideal.span (Set.range c) with hJ
  have hmemJ : ∀ x, f x = 0 → x ∈ J := fun x hx => by rw [← hker]; exact hx
  apply CentralIdempotentCorrespondence.of_bijOn
  refine ⟨fun e he => map_mem_centralIdempotents f hf he, ?_, ?_⟩
  ·
    intro e he e' he' hee'
    have hfe : f e * f e = f e := (he.2.map f).eq
    have hfe' : f e' * f e' = f e' := (he'.2.map f).eq
    have h1 : e * (1 - e') = 0 := by
      refine idempotent_eq_zero_of_mem_nilpotent hd hnil
        (mul_mem_centralIdempotents he (one_sub_mem_centralIdempotents he')).2 (hmemJ _ ?_)
      rw [map_mul, map_sub, map_one, ← hee', mul_sub, mul_one, hfe, sub_self]
    have h2 : e' * (1 - e) = 0 := by
      refine idempotent_eq_zero_of_mem_nilpotent hd hnil
        (mul_mem_centralIdempotents he' (one_sub_mem_centralIdempotents he)).2 (hmemJ _ ?_)
      rw [map_mul, map_sub, map_one, hee', mul_sub, mul_one, hfe', sub_self]
    have h1' : e = e * e' := by rw [mul_sub, mul_one, sub_eq_zero] at h1; exact h1
    have h2' : e' = e' * e := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2
    calc e = e * e' := h1'
      _ = e' * e := (Subring.mem_center_iff.mp he.1 e').symm
      _ = e' := h2'.symm
  ·
    intro ē hē
    obtain ⟨a, rfl⟩ := hf ē
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact ⟨a, ⟨Subring.mem_center_iff.mpr fun g => Subsingleton.elim _ _,
        Subsingleton.elim _ _⟩, rfl⟩
    have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    have hpd : d ≤ p ^ d := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    have hsq : a * a - a ∈ J := hmemJ _ (by rw [map_sub, map_mul, hē.2.eq, sub_self])
    set e := a ^ p ^ d with he_def
    have hidem : IsIdempotentElem e := by
      have h1 : (a * a - a) ^ p ^ d = (a * a) ^ p ^ d - a ^ p ^ d :=
        sub_pow_char_pow_of_commute p d ((Commute.refl a).mul_left (Commute.refl a))
      have h2 : (a * a - a) ^ p ^ d = 0 := by
        have hmem := Ideal.pow_mem_pow hsq (p ^ d)
        have hle : J ^ p ^ d ≤ J ^ d := Ideal.pow_le_pow_right hpd
        rw [hnil] at hle
        exact Ideal.mem_bot.mp (hle hmem)
      have h3 : e * e = (a * a) ^ p ^ d := ((Commute.refl a).mul_pow _).symm
      unfold IsIdempotentElem
      rw [h3]
      rw [h2] at h1
      exact (sub_eq_zero.mp h1.symm)
    have hfe : f e = f a := by
      rw [he_def, map_pow, ← Nat.sub_add_cancel (Nat.one_le_pow d p (Fact.out : p.Prime).pos),
        hē.2.pow_succ_eq]
    have hcentralB := Subring.mem_center_iff.mp hē.1
    have hcorner₁ : ∀ x, e * x * (1 - e) ∈ J := fun x => hmemJ _ (by
      rw [map_mul, map_mul, map_sub, map_one, hfe, ← hcentralB (f x), mul_assoc, mul_sub,
        mul_one, hē.2.eq, sub_self, mul_zero])
    have hcorner₂ : ∀ x, (1 - e) * x * e ∈ J := fun x => hmemJ _ (by
      rw [map_mul, map_mul, map_sub, map_one, hfe, mul_assoc, hcentralB (f x), ← mul_assoc,
        sub_mul, one_mul, hē.2.eq, sub_self, zero_mul])
    have hzero₁ : ∀ x, e * x * (1 - e) = 0 := fun x => by
      have := corner_mem_span_central_pow c hc hidem hidem.one_sub hcorner₁ d x
      rw [hnil, Ideal.mem_bot] at this
      exact this
    have hzero₂ : ∀ x, (1 - e) * x * e = 0 := fun x => by
      have := corner_mem_span_central_pow c hc hidem.one_sub hidem hcorner₂ d x
      rw [hnil, Ideal.mem_bot] at this
      exact this
    refine ⟨e, ⟨Subring.mem_center_iff.mpr fun x => ?_, hidem⟩, hfe⟩
    have h1 := hzero₁ x
    have h2 := hzero₂ x
    rw [mul_sub, mul_one, sub_eq_zero] at h1
    rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at h2
    rw [h2, ← h1]

theorem central_nilpotent_quotient_central_idempotents (k : Type*) [Field k] [Algebra k A]
    (p : ℕ) [Fact p.Prime] [CharP k p] {m : ℕ} (c : Fin m → A)
    (hc : ∀ i, c i ∈ Subring.center A) {d : ℕ} (hd : 1 ≤ d)
    (hnil : Ideal.span (Set.range c) ^ d = ⊥) :
    haveI := isTwoSided_span_central c hc
    CentralIdempotentCorrespondence (Ideal.Quotient.mk (Ideal.span (Set.range c))) := by
  have := isTwoSided_span_central c hc
  exact centralIdempotentCorrespondence_of_ker_eq_span_central k p _
    Ideal.Quotient.mk_surjective c hc Ideal.mk_ker hd hnil

end Nilpotent

end CFSG.Semidihedral.Principal
