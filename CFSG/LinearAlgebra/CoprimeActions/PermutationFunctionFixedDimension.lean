module

public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LinearAlgebra.CoprimeActions.PermutationFunctionFixedDimension

open Module

variable (F : Type*) [Field F] {X : Type*}

@[expose] def fixedSpace (σ : Equiv.Perm X) : Submodule F (X → F) where
  carrier := {f | ∀ x, f (σ x) = f x}
  add_mem' := by intro f g hf hg x; simp [hf x, hg x]
  zero_mem' := by intro x; simp
  smul_mem' := by intro c f hf x; simp [hf x]

abbrev OrbitQuot (σ : Equiv.Perm X) : Type _ :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers σ) X)

variable {F}

theorem mem_fixedSpace_zpow {σ : Equiv.Perm X} {f : X → F} (hf : f ∈ fixedSpace F σ) (k : ℤ)
    (x : X) : f ((σ ^ k) x) = f x := by
  induction k using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hf]
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    have := hf (σ⁻¹ x)
    simp at this
    exact this.symm

theorem orbitRel_iff (σ : Equiv.Perm X) (x y : X) :
    MulAction.orbitRel (Subgroup.zpowers σ) X x y ↔ ∃ k : ℤ, (σ ^ k) y = x := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, k, rfl⟩, h⟩
    exact ⟨k, h⟩
  · rintro ⟨k, h⟩
    exact ⟨⟨σ ^ k, k, rfl⟩, h⟩

@[expose] noncomputable def fixedEquiv (σ : Equiv.Perm X) :
    fixedSpace F σ ≃ₗ[F] (OrbitQuot σ → F) where
  toFun f := fun q => (f : X → F) q.out
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  invFun g := ⟨fun x => g (Quotient.mk _ x), fun x => by
    have : (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) (σ x)) =
        Quotient.mk _ x := by
      exact Quotient.sound ((orbitRel_iff σ _ _).2 ⟨1, by simp⟩)
    show g (Quotient.mk _ (σ x)) = g (Quotient.mk _ x)
    rw [this]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    obtain ⟨k, hk⟩ := (orbitRel_iff σ _ _).1 (Quotient.mk_out (s := MulAction.orbitRel
      (Subgroup.zpowers σ) X) x)
    show (f : X → F) (Quotient.out (Quotient.mk _ x)) = (f : X → F) x
    rw [← hk, mem_fixedSpace_zpow f.2]
  right_inv g := by
    funext q
    show g (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) q.out) = g q
    rw [Quotient.out_eq]

theorem finrank_eq_orbits [Finite X] (σ : Equiv.Perm X) :
    finrank F (fixedSpace F σ) = Nat.card (OrbitQuot σ) := by
  haveI : Finite (OrbitQuot σ) := Quotient.finite _
  haveI := Fintype.ofFinite (OrbitQuot σ)
  rw [(fixedEquiv σ).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

open Classical in
theorem fiber_card [Finite X] (σ : Equiv.Perm X) (r : ℕ) (hr : r.Prime) (hσ : σ ^ r = 1)
    (x0 : X) (hfix : ∀ x, σ x = x ↔ x = x0) (x : X) :
    Nat.card {y : X // (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) y : OrbitQuot σ) =
      Quotient.mk _ x} = if x = x0 then 1 else r := by
  have hfib : Nat.card {y : X // (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) y :
      OrbitQuot σ) = Quotient.mk _ x} = Nat.card (MulAction.orbit (Subgroup.zpowers σ) x) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun y => ?_
    rw [Quotient.eq]
    show MulAction.orbitRel (Subgroup.zpowers σ) X y x ↔ _
    rw [MulAction.orbitRel_apply]
  rw [hfib]
  have hdvd : Nat.card (MulAction.orbit (Subgroup.zpowers σ) x) ∣ r := by
    have h1 : Nat.card (MulAction.orbit (Subgroup.zpowers σ) x) *
        Nat.card (MulAction.stabilizer (Subgroup.zpowers σ) x) = Nat.card (Subgroup.zpowers σ) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers σ) x)
    have h2 : Nat.card (Subgroup.zpowers σ) ∣ r := by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ
    exact Dvd.dvd.trans ⟨_, h1.symm⟩ h2
  split_ifs with hx
  · subst hx
    have : MulAction.orbit (Subgroup.zpowers σ) x = {x} := by
      ext y
      rw [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, k, rfl⟩, h⟩
        rw [← h]
        exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ((hfix x).2 rfl) k
      · rintro rfl
        exact ⟨1, by simp⟩
    rw [this]; simp
  · rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exfalso
      apply hx
      rw [← hfix]
      have hmem : σ x ∈ MulAction.orbit (Subgroup.zpowers σ) x :=
        ⟨⟨σ, Subgroup.mem_zpowers σ⟩, rfl⟩
      have hmem' : x ∈ MulAction.orbit (Subgroup.zpowers σ) x := MulAction.mem_orbit_self x
      have := Nat.card_eq_one_iff_unique.1 h
      have h3 := this.1.elim ⟨σ x, hmem⟩ ⟨x, hmem'⟩
      exact congrArg Subtype.val h3
    · exact h

theorem prime_semiregular_formula [Finite X] (σ : Equiv.Perm X) (r : ℕ) (hr : r.Prime)
    (hσ : σ ^ r = 1) (x0 : X) (hfix : ∀ x, σ x = x ↔ x = x0) :
    r * finrank F (fixedSpace F σ) = Nat.card X + r - 1 := by
  classical
  rw [finrank_eq_orbits]
  haveI : Finite (OrbitQuot σ) := Quotient.finite _
  haveI := Fintype.ofFinite (OrbitQuot σ)
  haveI := Fintype.ofFinite X
  set mk : X → OrbitQuot σ := Quotient.mk _ with hmk
  have hsum : Nat.card X = ∑ q : OrbitQuot σ, Nat.card {y : X // mk y = q} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_congr (Equiv.sigmaFiberEquiv mk).symm,
      Fintype.card_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Nat.card_eq_fintype_card]
  have hq0 : ∀ q : OrbitQuot σ, q ≠ mk x0 → Nat.card {y : X // mk y = q} = r := by
    intro q hq
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    have hx : x ≠ x0 := fun h => hq (by rw [h])
    rw [fiber_card σ r hr hσ x0 hfix x, if_neg hx]
  have h0 : Nat.card {y : X // mk y = mk x0} = 1 := by
    rw [fiber_card σ r hr hσ x0 hfix x0, if_pos rfl]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (mk x0)), h0,
    Finset.sum_congr rfl (fun q hq => hq0 q (Finset.ne_of_mem_erase hq)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  have : 1 ≤ Fintype.card (OrbitQuot σ) := Fintype.card_pos_iff.2 ⟨mk x0⟩
  have h1 := hr.one_lt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le this
  rw [hk]
  simp only [Nat.add_sub_cancel_left]
  rw [Nat.mul_add, Nat.mul_comm k r]
  omega

end CFSG.LinearAlgebra.CoprimeActions.PermutationFunctionFixedDimension
