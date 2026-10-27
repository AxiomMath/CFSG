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

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

section CycleSet

variable {N : Type*}

abbrev CycleSet (π : Perm N) : Type _ := Quotient (SameCycle.setoid π)

theorem sameCycle_map_iff_of_comm {π g : Perm N} (hg : g * π = π * g) {x y : N} :
    SameCycle π (g x) (g y) ↔ SameCycle π x y := by
  have hc : Commute g π := hg
  have key : ∀ (i : ℤ) (z : N), g ((π ^ i) z) = (π ^ i) (g z) := fun i z => by
    have := (hc.zpow_right i).eq
    exact congrArg (fun e : Perm N => e z) this
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, g.injective ?_⟩
    rw [key, hi]
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← key, hi]⟩

@[expose] def cycEquiv (π g : Perm N) (hg : g * π = π * g) : Perm (CycleSet π) :=
  Quotient.congr g (fun _ _ => (sameCycle_map_iff_of_comm hg).symm)

theorem cycEquiv_mk (π g : Perm N) (hg : g * π = π * g) (x : N) :
    cycEquiv π g hg (Quotient.mk _ x) = Quotient.mk _ (g x) := rfl

variable {H : Type*} [Group H] {π : Perm N}

@[expose] def cycHom (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) : H →* Perm (CycleSet π) where
  toFun h := cycEquiv π (ι h) (hι h)
  map_one' := by
    ext q
    induction q using Quotient.inductionOn with
    | _ x => simp [cycEquiv_mk]
  map_mul' h h' := by
    ext q
    induction q using Quotient.inductionOn with
    | _ x => simp [cycEquiv_mk]

theorem cycHom_mk (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H) (x : N) :
    cycHom ι hι h (Quotient.mk _ x) = Quotient.mk _ (ι h x) := rfl

theorem cycHom_eq_one_iff (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H) :
    cycHom ι hι h = 1 ↔ ∀ x, SameCycle π x (ι h x) := by
  constructor
  · intro h1 x
    have h2 : cycHom ι hι h (Quotient.mk _ x) = Quotient.mk _ x := by rw [h1]; rfl
    rw [cycHom_mk] at h2
    exact (Quotient.exact h2).symm
  · intro h2
    ext q
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound (h2 x).symm

theorem apply_comm_of_sameCycle (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) {h h' : H}
    {x : N} (h1 : SameCycle π x (ι h x)) (h2 : SameCycle π x (ι h' x)) :
    ι h (ι h' x) = ι h' (ι h x) := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have key : ∀ (g : H) (k : ℤ) (z : N), ι g ((π ^ k) z) = (π ^ k) (ι g z) := fun g k z => by
    have := (Commute.zpow_right (show Commute (ι g) π from hι g) k).eq
    exact congrArg (fun e : Perm N => e z) this
  have e1 : ι h (ι h' x) = (π ^ (j + i)) x := by
    rw [← hj, key, ← hi, zpow_add, Perm.mul_apply]
  have e2 : ι h' (ι h x) = (π ^ (i + j)) x := by
    rw [← hi, key, ← hj, zpow_add, Perm.mul_apply]
  rw [e1, e2, add_comm]

theorem commute_of_cycHom_eq_one (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) {h h' : H}
    (h1 : cycHom ι hι h = 1) (h2 : cycHom ι hι h' = 1) : ι h * ι h' = ι h' * ι h := by
  rw [cycHom_eq_one_iff] at h1 h2
  ext x
  exact apply_comm_of_sameCycle ι hι (h1 x) (h2 x)

end CycleSet

section TypeSplit

variable {N : Type*} {H : Type*} [Group H] {π : Perm N}

theorem pow_two_apply_ne_iff_of_sameCycle {x y : N} (hxy : SameCycle π x y) :
    (π ^ 2) x ≠ x ↔ (π ^ 2) y ≠ y := by
  obtain ⟨i, rfl⟩ := hxy
  have key : (π ^ 2) ((π ^ i) x) = (π ^ i) ((π ^ 2) x) := by
    have := ((Commute.refl π).zpow_zpow (2 : ℤ) i).eq
    simpa [zpow_natCast] using congrArg (fun e : Perm N => e x) this
  rw [key]
  exact (not_congr (EmbeddingLike.apply_eq_iff_eq (π ^ i))).symm

def CycT (π : Perm N) : Set (CycleSet π) := Quotient.mk _ '' {x | (π ^ 2) x ≠ x}

theorem mk_mem_CycT_iff (x : N) : (Quotient.mk _ x : CycleSet π) ∈ CycT π ↔ (π ^ 2) x ≠ x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (pow_two_apply_ne_iff_of_sameCycle (Quotient.exact hyx)).1 hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem exists_mk_of_mem_CycT {q : CycleSet π} (hq : q ∈ CycT π) :
    ∃ x, Quotient.mk _ x = q ∧ (π ^ 2) x ≠ x := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨x, rfl, hx⟩

theorem pow_two_apply_ne_apply_iff (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H)
    (x : N) : (π ^ 2) (ι h x) ≠ ι h x ↔ (π ^ 2) x ≠ x := by
  have key : (π ^ 2) (ι h x) = ι h ((π ^ 2) x) := by
    have := (Commute.pow_right (show Commute (ι h) π from hι h) 2).eq
    exact (congrArg (fun e : Perm N => e x) this).symm
  rw [key]
  exact not_congr (EmbeddingLike.apply_eq_iff_eq (ι h))

theorem cycHom_mem_CycT_iff (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H)
    (q : CycleSet π) : cycHom ι hι h q ∈ CycT π ↔ q ∈ CycT π := by
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [cycHom_mk, mk_mem_CycT_iff, mk_mem_CycT_iff]
    exact pow_two_apply_ne_apply_iff ι hι h x

@[expose] def actT (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) : H →* Perm (CycT π) where
  toFun h := (cycHom ι hι h).subtypePerm (fun q => cycHom_mem_CycT_iff ι hι h q)
  map_one' := by
    ext q
    simp
  map_mul' h h' := by
    ext q
    simp
    rfl

@[expose] def actF (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) :
    H →* Perm ↥(CycT π)ᶜ where
  toFun h := (cycHom ι hι h).subtypePerm
    (fun q => not_congr (cycHom_mem_CycT_iff ι hι h q))
  map_one' := by
    ext q
    simp
  map_mul' h h' := by
    ext q
    simp
    rfl

@[expose] def resT (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) :
    H →* Perm {x : N // (π ^ 2) x ≠ x} where
  toFun h := (ι h).subtypePerm (fun x => pow_two_apply_ne_apply_iff ι hι h x)
  map_one' := by
    ext x
    simp
  map_mul' h h' := by
    ext x
    simp
    rfl

theorem coe_resT_apply (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H)
    (x : {x : N // (π ^ 2) x ≠ x}) : ((resT ι hι h x : {x : N // (π ^ 2) x ≠ x}) : N) = ι h x :=
  rfl

end TypeSplit

section Kernels

variable {N : Type*} {H : Type*} [Group H] {π : Perm N}

theorem mem_ker_actT_iff (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H) :
    h ∈ (actT ι hι).ker ↔ ∀ x, (π ^ 2) x ≠ x → SameCycle π x (ι h x) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1 x hx
    have h2 := congrArg (fun e : Perm (CycT π) => (e ⟨Quotient.mk _ x, (mk_mem_CycT_iff x).2 hx⟩).1)
      h1
    simp only [Perm.coe_one, id_eq] at h2
    change cycHom ι hι h (Quotient.mk _ x) = Quotient.mk _ x at h2
    rw [cycHom_mk] at h2
    exact (Quotient.exact h2).symm
  · intro h2
    ext ⟨q, hq⟩
    obtain ⟨x, rfl, hx⟩ := exists_mk_of_mem_CycT hq
    exact Quotient.sound (h2 x hx).symm

theorem mem_ker_actF_iff (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) (h : H) :
    h ∈ (actF ι hι).ker ↔ ∀ x, (π ^ 2) x = x → SameCycle π x (ι h x) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1 x hx
    have hq : (Quotient.mk _ x : CycleSet π) ∈ (CycT π)ᶜ := fun hc => (mk_mem_CycT_iff x).1 hc hx
    have h2 := congrArg (fun e : Perm ↥(CycT π)ᶜ => (e ⟨Quotient.mk _ x, hq⟩).1) h1
    simp only [Perm.coe_one, id_eq] at h2
    change cycHom ι hι h (Quotient.mk _ x) = Quotient.mk _ x at h2
    rw [cycHom_mk] at h2
    exact (Quotient.exact h2).symm
  · intro h2
    ext ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      have hx : (π ^ 2) x = x := by
        by_contra hne
        exact hq ((mk_mem_CycT_iff x).2 hne)
      exact Quotient.sound (h2 x hx).symm

theorem apply_comm_of_mem_ker_actT (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) {h h' : H}
    (hh : h ∈ (actT ι hι).ker) (hh' : h' ∈ (actT ι hι).ker) {x : N} (hx : (π ^ 2) x ≠ x) :
    ι h (ι h' x) = ι h' (ι h x) :=
  apply_comm_of_sameCycle ι hι ((mem_ker_actT_iff ι hι h).1 hh x hx)
    ((mem_ker_actT_iff ι hι h').1 hh' x hx)

theorem ker_actT_inf_ker_actF_le (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) :
    (actT ι hι).ker ⊓ (actF ι hι).ker ≤ (cycHom ι hι).ker := by
  rintro h ⟨h1, h2⟩
  rw [MonoidHom.mem_ker, cycHom_eq_one_iff]
  intro x
  by_cases hx : (π ^ 2) x = x
  · exact (mem_ker_actF_iff ι hι h).1 h2 x hx
  · exact (mem_ker_actT_iff ι hι h).1 h1 x hx

theorem commute_resT_of_mem_ker_actT (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) {h h' : H}
    (hh : h ∈ (actT ι hι).ker) (hh' : h' ∈ (actT ι hι).ker) :
    resT ι hι h * resT ι hι h' = resT ι hι h' * resT ι hι h := by
  ext x
  exact apply_comm_of_mem_ker_actT ι hι hh hh' x.2

theorem iota_pow_apply_of_pow_eq (ι : H →* Perm N) (hι : ∀ h, ι h * π = π * ι h) {h : H} {y : N}
    {i : ℤ} (hi : (π ^ i) y = ι h y) (m : ℕ) : ((ι h) ^ m) y = (π ^ (i * m)) y := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key : ι h ((π ^ (i * m)) y) = (π ^ (i * m)) (ι h y) := by
      have := (Commute.zpow_right (show Commute (ι h) π from hι h) (i * m)).eq
      exact congrArg (fun e : Perm N => e y) this
    rw [pow_succ', Perm.mul_apply, ih, key, ← hi, ← Perm.mul_apply, ← zpow_add]
    congr 2
    push_cast
    ring

theorem resT_pow_four_of_mem_ker_actT (hπ : π ^ 4 = 1) (ι : H →* Perm N)
    (hι : ∀ h, ι h * π = π * ι h) {h : H} (hh : h ∈ (actT ι hι).ker) :
    resT ι hι h ^ 4 = 1 := by
  ext ⟨y, hy⟩
  obtain ⟨i, hi⟩ := (mem_ker_actT_iff ι hι h).1 hh y hy
  have h4 : ((ι h) ^ 4) y = y := by
    rw [iota_pow_apply_of_pow_eq ι hι hi 4]
    have : (π ^ (i * ((4 : ℕ) : ℤ))) = 1 := by
      rw [mul_comm, zpow_mul]
      simp [hπ]
    rw [this]
    rfl
  have : ((resT ι hι h ^ 4) ⟨y, hy⟩ : {x : N // (π ^ 2) x ≠ x}) = ⟨y, hy⟩ := by
    apply Subtype.ext
    rw [← map_pow, coe_resT_apply, map_pow]
    exact h4
  simpa using congrArg Subtype.val this

end Kernels

section PowFacts

variable {N : Type*} {π : Perm N}

theorem sameCycle_pow_self (π : Perm N) (x : N) (k : ℕ) : SameCycle π x ((π ^ k) x) :=
  ⟨(k : ℤ), by simp⟩

theorem pow_apply_ne_self (hπ : π ^ 4 = 1) {y : N} (hy : (π ^ 2) y ≠ y) {d : ℕ} (hd1 : 1 ≤ d)
    (hd3 : d ≤ 3) : (π ^ d) y ≠ y := by
  have h1 : π y ≠ y := fun h => hy (by
    rw [pow_two, Perm.mul_apply, h, h])
  interval_cases d
  · simpa using h1
  · exact hy
  · intro h
    apply h1
    have h4 : (π ^ 4) y = y := by rw [hπ]; rfl
    have : π ((π ^ 3) y) = (π ^ 4) y := by
      rw [show (4 : ℕ) = 1 + 3 by norm_num, pow_add, Perm.mul_apply, pow_one]
    rwa [h, h4] at this

theorem pow_apply_injOn_four (hπ : π ^ 4 = 1) {x : N} (hx : (π ^ 2) x ≠ x) {i j : ℕ} (hi : i < 4)
    (hj : j < 4) (h : (π ^ i) x = (π ^ j) x) : i = j := by
  have hsc : ∀ k : ℕ, (π ^ 2) ((π ^ k) x) ≠ (π ^ k) x := fun k =>
    (pow_two_apply_ne_iff_of_sameCycle (sameCycle_pow_self π x k)).1 hx
  have aux : ∀ a b : ℕ, a < b → b < 4 → (π ^ a) x = (π ^ b) x → False := by
    intro a b hab hb h'
    have : (π ^ (b - a)) ((π ^ a) x) = (π ^ a) x := by
      rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hab.le, ← h']
    exact pow_apply_ne_self hπ (hsc a) (by omega) (by omega) this
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact aux i j hlt hj h
  · exact aux j i hlt hi h.symm

end PowFacts

section Counting

variable {N : Type*} [Fintype N] [DecidableEq N] {π : Perm N}

theorem four_mul_card_CycT_le (hπ : π ^ 4 = 1) :
    4 * Nat.card (CycT π) ≤ (π ^ 2).support.card := by
  have rep : ∀ q : ↥(CycT π), (π ^ 2) (Quotient.out q.1) ≠ Quotient.out q.1 := fun q =>
    (mk_mem_CycT_iff (Quotient.out q.1)).1 (by rw [Quotient.out_eq]; exact q.2)
  let f : ↥(CycT π) × Fin 4 → ↥((π ^ 2).support) := fun p =>
    ⟨(π ^ (p.2 : ℕ)) (Quotient.out p.1.1), by
      rw [Perm.mem_support]
      exact (pow_two_apply_ne_iff_of_sameCycle
        (sameCycle_pow_self π (Quotient.out p.1.1) (p.2 : ℕ))).1 (rep p.1)⟩
  have hmk : ∀ (q : CycleSet π) (k : ℕ),
      (Quotient.mk _ ((π ^ k) (Quotient.out q)) : CycleSet π) = q := fun q k => by
    conv_rhs => rw [← Quotient.out_eq q]
    exact Quotient.sound (sameCycle_pow_self π _ k).symm
  have hf : Function.Injective f := by
    rintro ⟨q, i⟩ ⟨q', j⟩ hij
    have h1 : (π ^ (i : ℕ)) (Quotient.out q.1) = (π ^ (j : ℕ)) (Quotient.out q'.1) :=
      congrArg Subtype.val hij
    have hq : q.1 = q'.1 := by
      rw [← hmk q.1 i, ← hmk q'.1 j, h1]
    have hqq : q = q' := Subtype.ext hq
    subst hqq
    have hij' : (i : ℕ) = j := pow_apply_injOn_four hπ (rep q) i.2 j.2 h1
    exact Prod.ext rfl (Fin.ext hij')
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := ↥((π ^ 2).support)), Fintype.card_coe] at this
  omega

theorem card_CycF_le : Nat.card ↥(CycT π)ᶜ ≤ Fintype.card N - (π ^ 2).support.card := by
  have hfix : ∀ q : ↥(CycT π)ᶜ, (π ^ 2) (Quotient.out q.1) = Quotient.out q.1 := fun q => by
    by_contra hne
    exact q.2 (by rw [← Quotient.out_eq q.1]; exact (mk_mem_CycT_iff _).2 hne)
  let f : ↥(CycT π)ᶜ → Function.fixedPoints ⇑(π ^ 2) := fun q => ⟨Quotient.out q.1, hfix q⟩
  have hf : Function.Injective f := by
    intro q q' h
    apply Subtype.ext
    exact Quotient.out_inj.1 (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (Function.fixedPoints ⇑(π ^ 2)) =
      Fintype.card N - (π ^ 2).support.card := by
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  omega

end Counting

end CFSG.OddStandard.Solomon75
