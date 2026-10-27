module

public import CFSG.Open.LocalVocabulary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem i28_14_symOrbit_mul_le_pow {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : p * j ≤ p ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · calc p * (j + 1) ≤ p * (p * j) := by
            apply Nat.mul_le_mul_left
            nlinarith
        _ ≤ p * p ^ j := Nat.mul_le_mul_left _ ih
        _ = p ^ (j + 1) := (pow_succ' p j).symm

theorem i28_14_symOrbit_mul_succ_le_pow {p : ℕ} (hp : 3 ≤ p) {j : ℕ} (hj : 2 ≤ j) :
    p * (j + 1) ≤ p ^ j := by
  induction j, hj using Nat.le_induction with
  | base => nlinarith
  | succ j hj ih =>
    calc p * (j + 1 + 1) ≤ p * (p * (j + 1)) := by
          apply Nat.mul_le_mul_left
          nlinarith
      _ ≤ p * p ^ j := Nat.mul_le_mul_left _ ih
      _ = p ^ (j + 1) := (pow_succ' p j).symm

variable {X : Type} [Finite X]

theorem i28_14_symOrbit_card_orbit {p : ℕ} (hp : p.Prime) {A : Subgroup (Equiv.Perm X)}
    (hA : IsElemAbelian p A) (x : X) : ∃ j, Nat.card (MulAction.orbit A x) = p ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p A := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hA.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hmul : Nat.card (MulAction.orbit A x) * Nat.card (MulAction.stabilizer A x) =
      Nat.card A := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x)]
  have hdvd : Nat.card (MulAction.orbit A x) ∣ p ^ n := hn ▸ ⟨_, hmul.symm⟩
  exact (Nat.dvd_prime_pow hp).mp hdvd |>.imp fun j hj => hj.2

omit [Finite X] in
theorem i28_14_symOrbit_inj {A : Subgroup (Equiv.Perm X)} (hA : IsMulCommutative A) :
    Function.Injective fun (a : A) (ω : MulAction.orbitRel.Quotient A X) =>
      (⟨a • ω.out, MulAction.mem_orbit _ _⟩ : MulAction.orbit A ω.out) := by
  intro a b hab
  have h : ∀ ω : MulAction.orbitRel.Quotient A X, a • ω.out = b • ω.out := fun ω =>
    congrArg Subtype.val (congrFun hab ω)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨c, hc⟩ : x ∈ MulAction.orbit A (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out := by
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq']
    exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
  rw [← hc]
  have key : ∀ d e : A, d • e • (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out =
      e • d • (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out := fun d e => by
    rw [← mul_smul, ← mul_smul, hA.is_comm.comm d e]
  have := calc (a : Equiv.Perm X) (c • _) = a • c • _ := rfl
    _ = c • a • (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out := key a c
    _ = c • b • (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out := by rw [h]
    _ = b • c • (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out := (key b c).symm
    _ = (b : Equiv.Perm X) (c • (Quotient.mk'' x : MulAction.orbitRel.Quotient A X).out) := rfl
  exact this

theorem i28_14_symOrbit_exists {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (Equiv.Perm X)} (hA : IsElemAbelian p A)
    (hbig : p ^ (Nat.card X / p) ≤ Nat.card A) (hA2 : p ^ 2 ≤ Nat.card A) :
    ∃ x : X, Nat.card (MulAction.orbit A x) = p := by
  classical
  by_contra hne
  push Not at hne
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hfin : Finite (MulAction.orbitRel.Quotient A X) := inferInstance
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient A X)
  choose j hj using fun ω : MulAction.orbitRel.Quotient A X =>
    i28_14_symOrbit_card_orbit hp hA ω.out
  have hj1 : ∀ ω, j ω ≠ 1 := fun ω h => hne ω.out (by rw [hj, h, pow_one])
  have hsum : Nat.card X = ∑ ω, p ^ j ω := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits A X), Nat.card_sigma]
    exact Finset.sum_congr rfl fun ω _ => hj ω
  have hprod : Nat.card A ≤ p ^ ∑ ω, j ω := by
    have h1 := Nat.card_le_card_of_injective _ (i28_14_symOrbit_inj hA.1)
    rw [Nat.card_pi] at h1
    rw [Finset.prod_congr rfl fun ω _ => hj ω, Finset.prod_pow_eq_pow_sum] at h1
    exact h1
  obtain ⟨x, hx⟩ : ∃ x : X, ∃ a : A, a • x ≠ x := by
    by_contra hall
    push Not at hall
    have : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro a ha
      exact Equiv.ext fun x => hall x ⟨a, ha⟩
    rw [this, Subgroup.card_bot] at hA2
    have := Nat.one_lt_pow (n := 2) (by norm_num) (by have := hp.one_lt; omega : 1 < p)
    omega
  obtain ⟨a, ha⟩ := hx
  set ω₀ : MulAction.orbitRel.Quotient A X := Quotient.mk'' x with hω₀
  have hmem : x ∈ MulAction.orbit A ω₀.out := by
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq']
    exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
  have horb : MulAction.orbit A ω₀.out = MulAction.orbit A x :=
    (MulAction.orbit_eq_iff.mpr hmem).symm
  have hnt : 1 < Nat.card (MulAction.orbit A ω₀.out) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨⟨⟨x, hmem⟩, ⟨a • x, by rw [horb]; exact MulAction.mem_orbit _ _⟩, ?_⟩⟩
    intro h
    exact ha (congrArg Subtype.val h).symm
  have hj0 : 2 ≤ j ω₀ := by
    have h1 := hj1 ω₀
    have h0 : j ω₀ ≠ 0 := fun h => by
      have := hj ω₀
      rw [h, pow_zero] at this
      omega
    omega
  have hle : ∑ ω, (p * j ω + if ω = ω₀ then p else 0) ≤ ∑ ω, p ^ j ω := by
    apply Finset.sum_le_sum
    intro ω _
    by_cases h : ω = ω₀
    · subst h
      simp only [↓reduceIte]
      have := i28_14_symOrbit_mul_succ_le_pow hp3 hj0
      linarith
    · simp only [h, ↓reduceIte, add_zero]
      exact i28_14_symOrbit_mul_le_pow hp.two_le _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ ω₀,
    ← hsum] at hle
  simp only [Finset.mem_univ, ↓reduceIte] at hle
  have h2 : (∑ ω, j ω) + 1 ≤ Nat.card X / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    linarith
  have h3 : p ^ ((∑ ω, j ω) + 1) ≤ p ^ (Nat.card X / p) :=
    Nat.pow_le_pow_right hp.pos h2
  have h4 : p ^ (∑ ω, j ω) < p ^ ((∑ ω, j ω) + 1) :=
    Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self _)
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
