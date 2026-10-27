module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open Module

@[expose, instance_reducible] def zmod2AddCommGroup : AddCommGroup (ZMod 2) :=
  (inferInstance : CommRing (ZMod 2)).toAddCommGroup

@[expose] def permAct {Ω : Type*} (σ : Equiv.Perm Ω) (x : Ω → ZMod 2) : Ω → ZMod 2 := fun i => x (σ.symm i)

variable {Ω : Type*}

@[expose] def orbSetoid (B : Subgroup (Equiv.Perm Ω)) : Setoid Ω where
  r x y := ∃ σ ∈ B, σ x = y
  iseqv :=
    ⟨fun x => ⟨1, B.one_mem, rfl⟩,
     fun {x y} ⟨σ, hσ, h⟩ => ⟨σ⁻¹, B.inv_mem hσ, by rw [← h]; exact σ.symm_apply_apply x⟩,
     fun ⟨σ, hσ, h⟩ ⟨τ, hτ, h'⟩ => ⟨τ * σ, B.mul_mem hτ hσ, by rw [← h', ← h]; rfl⟩⟩

variable (B : Subgroup (Equiv.Perm Ω))

@[expose] def orbOf (x : Ω) : Quotient (orbSetoid B) := Quotient.mk _ x

theorem orbOf_eq_iff {x y : Ω} : orbOf B x = orbOf B y ↔ ∃ σ ∈ B, σ x = y :=
  Quotient.eq (r := orbSetoid B)

theorem orbOf_apply {σ : Equiv.Perm Ω} (hσ : σ ∈ B) (x : Ω) : orbOf B (σ x) = orbOf B x :=
  ((orbOf_eq_iff B).mpr ⟨σ, hσ, rfl⟩).symm

theorem orbOf_surjective : Function.Surjective (orbOf B) := Quotient.mk_surjective

section Fibers

variable [Fintype Ω]

noncomputable instance orbFintype : Fintype (Quotient (orbSetoid B)) := Fintype.ofFinite _

theorem card_eq_sum_fiber_card :
    Fintype.card Ω = ∑ O : Quotient (orbSetoid B), Nat.card {a // orbOf B a = O} := by
  classical
  have h := Nat.card_sigma (β := fun O : Quotient (orbSetoid B) => {a // orbOf B a = O})
  rw [← h, Nat.card_congr (Equiv.sigmaFiberEquiv (orbOf B)), Nat.card_eq_fintype_card]

theorem card_le_prod_fibers (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) :
    Nat.card B ≤ ∏ O : Quotient (orbSetoid B), Nat.card {a // orbOf B a = O} := by
  classical
  let rep : Quotient (orbSetoid B) → Ω := Quotient.out
  have hrep : ∀ O, orbOf B (rep O) = O := fun O => Quotient.out_eq O
  let Θ : B → ((O : Quotient (orbSetoid B)) → {a // orbOf B a = O}) := fun g O =>
    ⟨g.1 (rep O), by rw [orbOf_apply B g.2, hrep]⟩
  have hinj : Function.Injective Θ := by
    intro g₁ g₂ h
    have h' : ∀ O, g₁.1 (rep O) = g₂.1 (rep O) := fun O => congrArg Subtype.val (congrFun h O)
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨σ, hσ, hσx⟩ := (orbOf_eq_iff B).mp ((hrep (orbOf B x)).trans rfl)
    have hc : ∀ (g : B) (y : Ω), g.1 (σ y) = σ (g.1 y) := fun g y =>
      congrArg (fun p : Equiv.Perm Ω => p y) (hcomm g.1 g.2 σ hσ)
    rw [← hσx, hc g₁, hc g₂, h']
  calc Nat.card B ≤ Nat.card ((O : Quotient (orbSetoid B)) → {a // orbOf B a = O}) :=
        Nat.card_le_card_of_injective Θ hinj
    _ = ∏ O : Quotient (orbSetoid B), Nat.card {a // orbOf B a = O} := Nat.card_pi

end Fibers

section Vectors

@[expose] def evenWeight (Ω : Type*) [Fintype Ω] : Submodule (ZMod 2) (Ω → ZMod 2) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb]; simp
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at *
    rw [hx]; simp

@[expose] def fixedVectors : Submodule (ZMod 2) (Ω → ZMod 2) where
  carrier := {x | ∀ σ ∈ B, permAct σ x = x}
  add_mem' := by
    intro a b ha hb σ hσ
    funext i
    have h1 := congrFun (ha σ hσ) i
    have h2 := congrFun (hb σ hσ) i
    simp only [permAct, Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2]
  zero_mem' := by intro σ _; rfl
  smul_mem' := by
    intro c x hx σ hσ
    funext i
    have h1 := congrFun (hx σ hσ) i
    simp only [permAct, Pi.smul_apply] at h1 ⊢
    rw [h1]

theorem fixed_apply_eq {x : Ω → ZMod 2} (hx : x ∈ fixedVectors B) {a b : Ω}
    (hab : orbOf B a = orbOf B b) : x a = x b := by
  obtain ⟨σ, hσ, rfl⟩ := (orbOf_eq_iff B).mp hab
  have h := congrFun (hx σ⁻¹ (B.inv_mem hσ)) a
  simpa [permAct, Equiv.Perm.inv_def] using h.symm

variable [Fintype Ω]

theorem finrank_fixedVectors_le :
    finrank (ZMod 2) (fixedVectors B) ≤ Fintype.card (Quotient (orbSetoid B)) := by
  classical
  let Φ : fixedVectors B →ₗ[ZMod 2] (Quotient (orbSetoid B) → ZMod 2) :=
    { toFun := fun x O => x.1 (Quotient.out O)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hinj : Function.Injective Φ := by
    intro x y h
    apply Subtype.ext
    funext a
    have hx := fixed_apply_eq B x.2 (a := a) (b := Quotient.out (orbOf B a))
      (Quotient.out_eq (orbOf B a)).symm
    have hy := fixed_apply_eq B y.2 (a := a) (b := Quotient.out (orbOf B a))
      (Quotient.out_eq (orbOf B a)).symm
    rw [hx, hy]
    exact congrFun h (orbOf B a)
  calc finrank (ZMod 2) (fixedVectors B)
      ≤ finrank (ZMod 2) (Quotient (orbSetoid B) → ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card (Quotient (orbSetoid B)) := Module.finrank_fintype_fun_eq_card (ZMod 2)

theorem exists_fixed_not_even (O₀ : Quotient (orbSetoid B))
    (hodd : Odd (Nat.card {a // orbOf B a = O₀})) :
    ∃ x ∈ fixedVectors B, x ∉ evenWeight Ω := by
  classical
  refine ⟨fun a => if orbOf B a = O₀ then 1 else 0, ?_, ?_⟩
  · intro σ hσ
    funext i
    have h1 : orbOf B (σ.symm i) = orbOf B i := orbOf_apply B (B.inv_mem hσ) i
    simp only [permAct]
    rw [h1]
  · intro hx
    have h1 : ∑ a : Ω, (if orbOf B a = O₀ then (1 : ZMod 2) else 0) = 0 := hx
    rw [Finset.sum_boole] at h1
    have h2 : (Finset.univ.filter (fun a => orbOf B a = O₀)).card = Nat.card {a // orbOf B a = O₀} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h2] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (ZMod.natCast_eq_zero_iff_even.mp h1)

theorem finrank_evenWeight_inf_fixed_lt (hodd : Odd (Fintype.card Ω)) :
    finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) + 1 ≤
      Fintype.card (Quotient (orbSetoid B)) := by
  classical
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  obtain ⟨O₀, hO₀⟩ : ∃ O, Odd (Nat.card {a // orbOf B a = O}) := by
    by_contra hcon
    push Not at hcon
    have heven : Even (Fintype.card Ω) := by
      rw [card_eq_sum_fiber_card B]
      exact Finset.even_sum _ (fun O _ => Nat.not_odd_iff_even.mp (hcon O))
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨x, hx, hxE⟩ := exists_fixed_not_even B O₀ hO₀
  have hlt : evenWeight Ω ⊓ fixedVectors B < fixedVectors B := by
    refine lt_of_le_of_ne inf_le_right (fun h => hxE ?_)
    have : x ∈ evenWeight Ω ⊓ fixedVectors B := by rw [h]; exact hx
    exact this.1
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := finrank_fixedVectors_le B
  omega

end Vectors

section Generation

variable [Fintype Ω] [DecidableEq Ω]

theorem perm_mem_closure_swaps {ι : Type*} (f : Ω → ι) (σ : Equiv.Perm Ω)
    (hσ : ∀ x, f (σ x) = f x) :
    σ ∈ Subgroup.closure {τ : Equiv.Perm Ω | ∃ a b, a ≠ b ∧ f a = f b ∧ τ = Equiv.swap a b} := by
  classical
  induction' hn : (Finset.univ.filter (fun x => σ x ≠ x)).card using Nat.strong_induction_on
    with n ih generalizing σ
  by_cases h1 : σ = 1
  · rw [h1]; exact Subgroup.one_mem _
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    exact h1 (Equiv.ext hc)
  have hτmem : Equiv.swap x (σ x) ∈
      {τ : Equiv.Perm Ω | ∃ a b, a ≠ b ∧ f a = f b ∧ τ = Equiv.swap a b} :=
    ⟨x, σ x, fun h => hx h.symm, (hσ x).symm, rfl⟩
  have hτf : ∀ z, f (Equiv.swap x (σ x) z) = f z := by
    intro z
    by_cases hzx : z = x
    · rw [hzx, Equiv.swap_apply_left]; exact (hσ x)
    by_cases hzy : z = σ x
    · rw [hzy, Equiv.swap_apply_right]; exact (hσ x).symm
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
  have hσ'f : ∀ z, f ((Equiv.swap x (σ x) * σ) z) = f z := fun z => by
    simp only [Equiv.Perm.mul_apply]
    rw [hτf, hσ]
  have hsub : (Finset.univ.filter (fun z => (Equiv.swap x (σ x) * σ) z ≠ z)) ⊂
      (Finset.univ.filter (fun z => σ z ≠ z)) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, by simpa using hx, ?_⟩
      rw [Finset.mem_filter]
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      intro hσz
      apply hz
      simp only [Equiv.Perm.mul_apply, hσz]
      by_cases hzx : z = x
      · subst hzx
        exact absurd hσz hx
      by_cases hzy : z = σ x
      · exfalso
        have : σ z = σ x := by rw [hσz, hzy]
        exact hzx (σ.injective this)
      exact Equiv.swap_apply_of_ne_of_ne hzx hzy
  have hlt := Finset.card_lt_card hsub
  have hσ'mem := ih _ (hn ▸ hlt) (Equiv.swap x (σ x) * σ) hσ'f rfl
  have hσeq : σ = Equiv.swap x (σ x) * (Equiv.swap x (σ x) * σ) := by
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  rw [hσeq]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hτmem) hσ'mem

omit [Fintype Ω] in
theorem swap_preserves_fibers {ι : Type*} (f : Ω → ι) {a b : Ω} (hab : f a = f b) (z : Ω) :
    f (Equiv.swap a b z) = f z := by
  by_cases hza : z = a
  · rw [hza, Equiv.swap_apply_left]; exact hab.symm
  by_cases hzb : z = b
  · rw [hzb, Equiv.swap_apply_right]; exact hab
  rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

theorem succ_lt_two_pow {k : ℕ} (hk : 2 ≤ k) : k + 1 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

end Generation

section DimEven

theorem finrank_ker_add_finrank_range {V V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [AddCommGroup V₂] [Module (ZMod 2) V₂] (φ : V →ₗ[ZMod 2] V₂) :
    finrank (ZMod 2) (LinearMap.range φ) + finrank (ZMod 2) (LinearMap.ker φ) =
      finrank (ZMod 2) V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  exact LinearMap.finrank_range_add_finrank_ker φ

theorem finrank_evenWeight (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    finrank (ZMod 2) (evenWeight Ω) = Fintype.card Ω - 1 := by
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  let φ : (Ω → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i : Ω, LinearMap.proj i
  have hker : evenWeight Ω = LinearMap.ker φ := by
    ext x
    simp [evenWeight, φ, LinearMap.sum_apply]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨i₀⟩ := (inferInstance : Nonempty Ω)
    classical
    refine ⟨Pi.single i₀ c, ?_⟩
    simp [φ, LinearMap.sum_apply]
  have h1 := finrank_ker_add_finrank_range φ
  have h2 : finrank (ZMod 2) (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
  rw [hker]
  have h3 : finrank (ZMod 2) (Ω → ZMod 2) = Fintype.card Ω :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  omega

end DimEven

section Main

variable [Fintype Ω] [DecidableEq Ω]

theorem even_weight_action_inequality_transpositions
    (hodd : Odd (Fintype.card Ω)) (B : Subgroup (Equiv.Perm Ω)) [CFSG.IsElementaryAbelian 2 B]
    {r : ℕ} (hr : Nat.card B = 2 ^ r)
    (h : finrank (ZMod 2) (evenWeight Ω) ≤
      finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) + r) :
    ∃ s : Finset (Finset Ω), (∀ Δ ∈ s, Δ.card = 2) ∧ (s : Set (Finset Ω)).PairwiseDisjoint id ∧
      s.card = r ∧
      B = Subgroup.closure {σ | ∃ Δ ∈ s, ∃ a ∈ Δ, ∃ b ∈ Δ, a ≠ b ∧ σ = Equiv.swap a b} ∧
      (∀ σ ∈ B, ∀ x, (∀ Δ ∈ s, x ∉ Δ) → σ x = x) ∧
      finrank (ZMod 2) (evenWeight Ω) =
        finrank (ZMod 2) ↥(evenWeight Ω ⊓ fixedVectors B) + r := by
  classical
  have hΩne : Nonempty Ω := by
    rw [← Fintype.card_pos_iff]
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := B)).comm ⟨g, hg⟩ ⟨h, hh⟩)
  let s' : Quotient (orbSetoid B) → ℕ := fun O => Nat.card {a // orbOf B a = O}
  have hpos : ∀ O, 1 ≤ s' O := by
    intro O
    obtain ⟨a, ha⟩ := orbOf_surjective B O
    have : Nonempty {a // orbOf B a = O} := ⟨⟨a, ha⟩⟩
    exact Nat.card_pos
  have hm : Fintype.card Ω = ∑ O, s' O := card_eq_sum_fiber_card B
  have hE := finrank_evenWeight Ω
  have hC := finrank_evenWeight_inf_fixed_lt B hodd
  have hu : Fintype.card Ω = (∑ O, (s' O - 1)) + Fintype.card (Quotient (orbSetoid B)) := by
    rw [hm, Fintype.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun O _ => (Nat.sub_add_cancel (hpos O)).symm
  have hΩpos : 1 ≤ Fintype.card Ω := Fintype.card_pos_iff.mpr hΩne
  have hur : (∑ O, (s' O - 1)) ≤ r := by omega
  have hprodB : 2 ^ r ≤ ∏ O, s' O := hr ▸ card_le_prod_fibers B hcomm
  have hpow : ∀ O, s' O ≤ 2 ^ (s' O - 1) := by
    intro O
    have h1 := hpos O
    have h2 : s' O - 1 < 2 ^ (s' O - 1) := Nat.lt_two_pow_self
    omega
  have hle2 : ∀ O, s' O ≤ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨O₀, hO₀⟩ := hcon
    have hstrict : s' O₀ < 2 ^ (s' O₀ - 1) := by
      have := succ_lt_two_pow (k := s' O₀ - 1) (by omega)
      have h3 : s' O₀ - 1 + 1 = s' O₀ := Nat.sub_add_cancel (hpos O₀)
      rw [h3] at this
      exact this
    have hlt : ∏ O, s' O < ∏ O, 2 ^ (s' O - 1) :=
      Finset.prod_lt_prod₀ (fun O _ => hpos O) (fun O _ => hpow O) ⟨O₀, Finset.mem_univ _, hstrict⟩
    rw [Finset.prod_pow_eq_pow_sum] at hlt
    have h4 : 2 ^ (∑ O, (s' O - 1)) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hur
    omega
  have hs12 : ∀ O, s' O = 1 ∨ s' O = 2 := fun O => by
    have := hpos O; have := hle2 O; omega
  have hpoweq : ∀ O, s' O = 2 ^ (s' O - 1) := fun O => by
    rcases hs12 O with h1 | h1 <;> rw [h1] <;> norm_num
  have hprodeq : ∏ O, s' O = 2 ^ (∑ O, (s' O - 1)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun O _ => hpoweq O
  have hru : r = ∑ O, (s' O - 1) := by
    have h1 : 2 ^ r ≤ 2 ^ (∑ O, (s' O - 1)) := hprodeq ▸ hprodB
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hPcard : Fintype.card {g : Equiv.Perm Ω // orbOf B ∘ g = orbOf B} = 2 ^ r := by
    rw [DomMulAct.stabilizer_card (orbOf B), hru, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun O _ => ?_
    have h1 : Fintype.card {a // orbOf B a = O} = s' O := (Nat.card_eq_fintype_card).symm
    rw [h1]
    rcases hs12 O with h2 | h2 <;> rw [h2] <;> simp
  let ι : B → {g : Equiv.Perm Ω // orbOf B ∘ g = orbOf B} := fun g =>
    ⟨g.1, funext (orbOf_apply B g.2)⟩
  have hι : Function.Injective ι := fun g₁ g₂ h =>
    Subtype.ext (congrArg (fun p : {g : Equiv.Perm Ω // orbOf B ∘ g = orbOf B} => p.1) h)
  have hbij : Function.Bijective ι := by
    refine hι.bijective_of_nat_card_le ?_
    rw [Nat.card_eq_fintype_card, hPcard, hr]
  have hP : ∀ σ : Equiv.Perm Ω, (∀ x, orbOf B (σ x) = orbOf B x) → σ ∈ B := by
    intro σ hσ
    obtain ⟨g, hg⟩ := hbij.2 ⟨σ, funext hσ⟩
    have : g.1 = σ := congrArg Subtype.val hg
    rw [← this]
    exact g.2
  let fib : Quotient (orbSetoid B) → Finset Ω := fun O =>
    Finset.univ.filter (fun a => orbOf B a = O)
  have hfib_card : ∀ O, (fib O).card = s' O := fun O => by
    simp only [fib, s']
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hmem_fib : ∀ O a, a ∈ fib O ↔ orbOf B a = O := fun O a => by simp [fib]
  let s : Finset (Finset Ω) :=
    ((Finset.univ : Finset (Quotient (orbSetoid B))).filter (fun O => s' O = 2)).image fib
  have hs_mem : ∀ Δ, Δ ∈ s ↔ ∃ O, s' O = 2 ∧ fib O = Δ := fun Δ => by simp [s]
  have hfib_inj : Function.Injective fib := by
    intro O₁ O₂ h
    obtain ⟨a, ha⟩ := orbOf_surjective B O₁
    have h1 : a ∈ fib O₁ := (hmem_fib O₁ a).mpr ha
    rw [h] at h1
    rw [← ha, ((hmem_fib O₂ a).mp h1)]
  refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Δ hΔ
    obtain ⟨O, hO, rfl⟩ := (hs_mem Δ).mp hΔ
    rw [hfib_card, hO]
  · intro Δ₁ hΔ₁ Δ₂ hΔ₂ hne
    obtain ⟨O₁, -, rfl⟩ := (hs_mem Δ₁).mp hΔ₁
    obtain ⟨O₂, -, rfl⟩ := (hs_mem Δ₂).mp hΔ₂
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro a ha1 ha2
    exact hne (congrArg fib (((hmem_fib O₁ a).mp ha1).symm.trans ((hmem_fib O₂ a).mp ha2)))
  · have hcard : s.card =
        ((Finset.univ : Finset (Quotient (orbSetoid B))).filter (fun O => s' O = 2)).card :=
      Finset.card_image_of_injective _ hfib_inj
    rw [hcard, Finset.card_filter, hru]
    refine Finset.sum_congr rfl fun O _ => ?_
    rcases hs12 O with h1 | h1 <;> simp [h1]
  · apply le_antisymm
    · intro σ hσ
      have := perm_mem_closure_swaps (orbOf B) σ (orbOf_apply B hσ)
      refine Subgroup.closure_mono ?_ this
      rintro τ ⟨a, b, hab, hfab, rfl⟩
      have h2 : s' (orbOf B a) = 2 := by
        have h1 : 2 ≤ s' (orbOf B a) := by
          rw [← hfib_card]
          have hsub : ({a, b} : Finset Ω) ⊆ fib (orbOf B a) := by
            intro z hz
            rw [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact (hmem_fib _ _).mpr rfl
            · exact (hmem_fib _ _).mpr hfab.symm
          have := Finset.card_le_card hsub
          rwa [Finset.card_pair hab] at this
        have := hle2 (orbOf B a)
        omega
      exact ⟨fib (orbOf B a), (hs_mem _).mpr ⟨_, h2, rfl⟩, a, (hmem_fib _ a).mpr rfl, b,
        (hmem_fib _ b).mpr hfab.symm, hab, rfl⟩
    · rw [Subgroup.closure_le]
      rintro τ ⟨Δ, hΔ, a, ha, b, hb, hab, rfl⟩
      obtain ⟨O, -, rfl⟩ := (hs_mem Δ).mp hΔ
      have haO := (hmem_fib O a).mp ha
      have hbO := (hmem_fib O b).mp hb
      exact hP _ (swap_preserves_fibers (orbOf B) (haO.trans hbO.symm))
  · intro σ hσ x hx
    have h1 : s' (orbOf B x) = 1 := by
      rcases hs12 (orbOf B x) with h1 | h1
      · exact h1
      · exfalso
        exact hx (fib (orbOf B x)) ((hs_mem _).mpr ⟨_, h1, rfl⟩) ((hmem_fib _ x).mpr rfl)
    have hsub : Subsingleton {a // orbOf B a = orbOf B x} := (Nat.card_eq_one_iff_unique.mp h1).1
    have := hsub.elim ⟨σ x, orbOf_apply B hσ x⟩ ⟨x, rfl⟩
    exact congrArg Subtype.val this
  · omega

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules
