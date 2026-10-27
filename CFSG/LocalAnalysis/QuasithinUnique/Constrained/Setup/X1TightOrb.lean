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
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.X1.Tight

theorem card_modEq_fix_of_pow {α : Type} [Finite α] (f : α → α) (hf : ∀ a, f^[5] a = a) :
    Nat.card α ≡ Nat.card {a | f a = a} [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin := Fintype.ofFinite α
  let g : Function.End α := f
  have hpow : ∀ n a, (g ^ n) a = f^[n] a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ]
      exact (ih (f a)).trans (Function.iterate_succ_apply f n a).symm
  have hg : g ^ 5 ^ 1 = 1 := by
    funext a
    rw [pow_one, hpow]
    exact hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hg
  rw [Nat.card_eq_fintype_card]
  have e : Nat.card {a | f a = a} = Fintype.card g.fixedPoints := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [e]
  exact h

section Orbit

variable {V : Type} [CommGroup V]

@[expose] def fixSub (γ : MulAut V) : Subgroup V where
  carrier := {v | γ v = v}
  one_mem' := map_one γ
  mul_mem' := fun {a b} ha hb => by
    show γ (a * b) = a * b
    rw [map_mul, show γ a = a from ha, show γ b = b from hb]
  inv_mem' := fun {a} ha => by
    show γ a⁻¹ = a⁻¹
    rw [map_inv, show γ a = a from ha]

theorem card_modEq_inv [Finite V] (γ : MulAut V) (h5 : γ ^ 5 = 1) (M : Subgroup V)
    (hM : ∀ m ∈ M, γ m ∈ M) : Nat.card M ≡ Nat.card ↥(M ⊓ fixSub γ) [MOD 5] := by
  let f : M → M := fun m => ⟨γ m, hM m m.2⟩
  have hpow : ∀ n (a : M), ((f^[n] a : M) : V) = (γ ^ n) a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih (f a), pow_succ]
      rfl
  have hf : ∀ a, f^[5] a = a := by
    intro a
    apply Subtype.ext
    rw [hpow, h5]
    rfl
  have h := card_modEq_fix_of_pow f hf
  have e : Nat.card {a : M | f a = a} = Nat.card ↥(M ⊓ fixSub γ) := by
    apply Nat.card_congr
    exact
      { toFun := fun a => ⟨(a.1 : V), a.1.2, by
          have := congrArg Subtype.val a.2
          exact this⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
  rw [e] at h
  exact h

theorem two_pow_card (hcard : Nat.card V = 32) (M : Subgroup V) :
    ∃ m ≤ 5, Nat.card M = 2 ^ m := by
  have hdvd : Nat.card M ∣ 2 ^ 5 := by
    rw [show (2:ℕ) ^ 5 = 32 by norm_num, ← hcard]
    exact Subgroup.card_subgroup_dvd_card M
  obtain ⟨m, hm, h⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨m, hm, h⟩

theorem card_fixSub [Finite V] (hcard : Nat.card V = 32) (γ : MulAut V) (h5 : γ ^ 5 = 1)
    (h1 : γ ≠ 1) : Nat.card (fixSub γ) = 2 := by
  have h := card_modEq_inv γ h5 ⊤ (fun m _ => Subgroup.mem_top _)
  have e1 : Nat.card (⊤ : Subgroup V) = 32 := by rw [Subgroup.card_top, hcard]
  have e2 : (⊤ : Subgroup V) ⊓ fixSub γ = fixSub γ := top_inf_eq _
  rw [e1, e2] at h
  obtain ⟨m, hm, hmm⟩ := two_pow_card hcard (fixSub γ)
  rw [hmm] at h ⊢
  have hm5 : m ≠ 5 := by
    intro h5'
    apply h1
    have : fixSub γ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hmm, h5', hcard]
      norm_num
    ext v
    have hv : v ∈ fixSub γ := by rw [this]; exact Subgroup.mem_top v
    exact hv
  interval_cases m <;> simp_all [Nat.ModEq]

theorem card_inv_cases [Finite V] (hcard : Nat.card V = 32) (γ : MulAut V) (h5 : γ ^ 5 = 1)
    (h1 : γ ≠ 1) (M : Subgroup V) (hM : ∀ m ∈ M, γ m ∈ M) :
    Nat.card M = 1 ∨ Nat.card M = 2 ∨ Nat.card M = 16 ∨ Nat.card M = 32 := by
  have h := card_modEq_inv γ h5 M hM
  have hF := card_fixSub hcard γ h5 h1
  have hdvd : Nat.card ↥(M ⊓ fixSub γ) ∣ 2 := by
    rw [← hF]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hc : Nat.card ↥(M ⊓ fixSub γ) = 1 ∨ Nat.card ↥(M ⊓ fixSub γ) = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 hdvd
  obtain ⟨m, hm, hmm⟩ := two_pow_card hcard M
  rw [hmm] at h ⊢
  rcases hc with hc | hc <;> rw [hc] at h <;> interval_cases m <;> simp_all [Nat.ModEq]

@[expose] def orbSub (γ : MulAut V) (u : V) : Subgroup V :=
  Subgroup.closure (Set.range fun k : Fin 5 => (γ ^ (k : ℕ)) u)

theorem orbSub_inv (γ : MulAut V) (h5 : γ ^ 5 = 1) (u : V) :
    ∀ m ∈ orbSub γ u, γ m ∈ orbSub γ u := by
  intro m hm
  have hmap : (orbSub γ u).map γ.toMonoidHom ≤ orbSub γ u := by
    rw [orbSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    by_cases hk : (k : ℕ) < 4
    · apply Subgroup.subset_closure
      refine ⟨⟨k + 1, by omega⟩, ?_⟩
      show (γ ^ (k + 1 : ℕ)) u = γ ((γ ^ (k : ℕ)) u)
      rw [pow_succ']
      rfl
    · have hk4 : (k : ℕ) = 4 := by omega
      have : γ ((γ ^ (k : ℕ)) u) = u := by
        rw [hk4, ← MulAut.mul_apply, ← pow_succ', h5]
        rfl
      show γ ((γ ^ (k : ℕ)) u) ∈ orbSub γ u
      rw [this]
      apply Subgroup.subset_closure
      exact ⟨0, by simp⟩
  exact hmap ⟨m, hm, rfl⟩

theorem mem_orbSub_self (γ : MulAut V) (u : V) : u ∈ orbSub γ u :=
  Subgroup.subset_closure ⟨0, by simp⟩

theorem mem_orbSub_succ (γ : MulAut V) (u : V) : γ u ∈ orbSub γ u :=
  Subgroup.subset_closure ⟨1, by simp⟩

theorem exists_cyclic_generator [Finite V] (hcard : Nat.card V = 32) (γ : MulAut V)
    (h5 : γ ^ 5 = 1) (h1 : γ ≠ 1) : ∃ u : V, orbSub γ u = ⊤ := by
  by_contra hno
  push Not at hno
  have hF := card_fixSub hcard γ h5 h1
  have hnot32 : ∀ u, Nat.card (orbSub γ u) ≠ 32 := fun u h =>
    hno u (Subgroup.eq_top_of_card_eq _ (h.trans hcard.symm))
  have h16 : ∀ u, γ u ≠ u → Nat.card (orbSub γ u) = 16 := by
    intro u hu
    have hu1 : u ≠ 1 := fun h => hu (by rw [h, map_one])
    have hγu1 : γ u ≠ 1 := fun h => hu1 (γ.injective (by rw [h, map_one]))
    have h3 : 3 ≤ Nat.card (orbSub γ u) := by
      have hsub : ({1, u, γ u} : Set V) ⊆ (orbSub γ u : Set V) := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h | h
        · rw [h]; exact (orbSub γ u).one_mem
        · rw [h]; exact mem_orbSub_self γ u
        · rw [h]; exact mem_orbSub_succ γ u
      have hc : ({1, u, γ u} : Set V).ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨1, u, γ u, hu1.symm, hγu1.symm, hu.symm, rfl⟩
      calc 3 = ({1, u, γ u} : Set V).ncard := hc.symm
        _ ≤ (orbSub γ u : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card (orbSub γ u) := (Nat.card_coe_set_eq _).symm
    rcases card_inv_cases hcard γ h5 h1 (orbSub γ u) (orbSub_inv γ h5 u) with h | h | h | h
    · omega
    · omega
    · exact h
    · exact absurd h (hnot32 u)
  have hidx : ∀ u, γ u ≠ u → (orbSub γ u).index = 2 := by
    intro u hu
    have := Subgroup.card_mul_index (orbSub γ u)
    rw [h16 u hu, hcard] at this
    omega
  have hex : ∃ u : V, γ u ≠ u := by
    by_contra h
    push Not at h
    apply h1
    ext v
    exact h v
  obtain ⟨u, hu⟩ := hex
  have hex2 : ∃ u' : V, u' ∉ orbSub γ u ∧ γ u' ≠ u' := by
    by_contra h
    push Not at h
    have hcov : (Set.univ : Set V) ⊆ (orbSub γ u : Set V) ∪ (fixSub γ : Set V) := by
      intro v _
      by_cases hv : v ∈ orbSub γ u
      · exact Or.inl hv
      · exact Or.inr (h v hv)
    have h1' := Set.ncard_le_ncard hcov (Set.toFinite _)
    have h2' := Set.ncard_union_le (orbSub γ u : Set V) (fixSub γ : Set V)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq (orbSub γ u : Set V), ← Nat.card_coe_set_eq (fixSub γ : Set V)] at *
    have e1 : Nat.card (↥(orbSub γ u : Set V)) = 16 := h16 u hu
    have e2 : Nat.card (↥(fixSub γ : Set V)) = 2 := hF
    omega
  obtain ⟨u', hu'S, hu'⟩ := hex2
  have hinv : ∀ m ∈ orbSub γ u ⊓ orbSub γ u', γ m ∈ orbSub γ u ⊓ orbSub γ u' := fun m hm =>
    ⟨orbSub_inv γ h5 u m hm.1, orbSub_inv γ h5 u' m hm.2⟩
  have hge : 8 ≤ Nat.card ↥(orbSub γ u ⊓ orbSub γ u') := by
    have hm := Subgroup.card_mul_index (orbSub γ u ⊓ orbSub γ u')
    have hi := Subgroup.index_inf_le (H := orbSub γ u) (K := orbSub γ u')
    rw [hidx u hu, hidx u' hu'] at hi
    rw [hcard] at hm
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(orbSub γ u ⊓ orbSub γ u') * (orbSub γ u ⊓ orbSub γ u').index ≤ 7 * 4 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hle16 : Nat.card ↥(orbSub γ u ⊓ orbSub γ u') ≤ 16 := by
    rw [← h16 u hu]
    exact Subgroup.card_le_of_le inf_le_left
  have hc16 : Nat.card ↥(orbSub γ u ⊓ orbSub γ u') = 16 := by
    rcases card_inv_cases hcard γ h5 h1 _ hinv with h | h | h | h <;> omega
  have hSS : orbSub γ u ⊓ orbSub γ u' = orbSub γ u :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16 u hu, hc16])
  have hSS' : orbSub γ u ⊓ orbSub γ u' = orbSub γ u' :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h16 u' hu', hc16])
  apply hu'S
  rw [← hSS, hSS']
  exact mem_orbSub_self γ u'

end Orbit

end CFSG.QuasithinUnique.Setup.X1.Tight
