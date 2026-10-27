module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GroupActions

open MulAction

variable {Ω : Type*}

@[expose] def orbitFixedSet (D E : Subgroup (Equiv.Perm Ω)) (a : Ω) : Set Ω :=
  {b | b ∈ orbit D a ∧ ∀ e ∈ E, e b = b}

theorem permutation_centralizer_orbit_fixed_bound [Finite Ω] (D : Subgroup (Equiv.Perm Ω))
    {r : ℕ} (a : Fin r → Ω) (hcover : ∀ x : Ω, ∃ i, x ∈ orbit D (a i))
    (hdist : Function.Injective fun i => Nat.card (orbit D (a i)))
    (E : Fin r → Subgroup (Equiv.Perm Ω)) (hED : ∀ i, E i ≤ D)
    (hEa : ∀ i, ∀ e ∈ E i, e (a i) = a i) :
    (∀ c ∈ Subgroup.centralizer (D : Set (Equiv.Perm Ω)), ∀ i,
      c (a i) ∈ orbitFixedSet D (E i) (a i)) ∧
    Set.InjOn (fun c : Equiv.Perm Ω => fun i => c (a i))
      (Subgroup.centralizer (D : Set (Equiv.Perm Ω))) ∧
    Nat.card (Subgroup.centralizer (D : Set (Equiv.Perm Ω))) ≤
      ∏ i, Nat.card (orbitFixedSet D (E i) (a i)) := by
  classical
  set C := Subgroup.centralizer (D : Set (Equiv.Perm Ω)) with hC
  have hcomm : ∀ c ∈ C, ∀ d ∈ D, ∀ x : Ω, c (d x) = d (c x) := by
    intro c hc d hd x
    have h := Subgroup.mem_centralizer_iff.1 hc d hd
    exact (congrFun (congrArg DFunLike.coe h) x).symm
  have horbit : ∀ c ∈ C, ∀ x : Ω,
      Nat.card (orbit D (c x)) = Nat.card (orbit D x) := by
    intro c hc x
    refine (Nat.card_congr ?_).symm
    refine
      { toFun := fun y => ⟨c y, ?_⟩
        invFun := fun y => ⟨c⁻¹ y, ?_⟩
        left_inv := fun y => Subtype.ext (c.symm_apply_apply y)
        right_inv := fun y => Subtype.ext (c.apply_symm_apply y) }
    · obtain ⟨d, hd⟩ := y.2
      refine ⟨d, ?_⟩
      change (d : Equiv.Perm Ω) (c x) = c y
      rw [← hcomm c hc d d.2, ← hd]
      rfl
    · obtain ⟨d, hd⟩ := y.2
      refine ⟨d, ?_⟩
      change (d : Equiv.Perm Ω) x = c⁻¹ y
      rw [Equiv.Perm.eq_inv_iff_eq, hcomm c hc d d.2]
      exact hd
  have hmem : ∀ c ∈ C, ∀ i, c (a i) ∈ orbitFixedSet D (E i) (a i) := by
    intro c hc i
    refine ⟨?_, fun e he => ?_⟩
    · obtain ⟨j, hj⟩ := hcover (c (a i))
      have hij : orbit D (c (a i)) = orbit D (a j) := orbit_eq_iff.2 hj
      have hsize : Nat.card (orbit D (a j)) = Nat.card (orbit D (a i)) := by
        rw [← hij, horbit c hc]
      rw [hdist hsize] at hj
      exact hj
    · rw [← hcomm c hc e (hED i he), hEa i e he]
  have hinj : Set.InjOn (fun c : Equiv.Perm Ω => fun i => c (a i)) C := by
    intro c hc c' hc' h
    refine Equiv.ext fun x => ?_
    obtain ⟨i, d, hd⟩ := hcover x
    have hdx : (d : Equiv.Perm Ω) (a i) = x := hd
    rw [← hdx, hcomm c hc d d.2, hcomm c' hc' d d.2]
    exact congrArg (d : Equiv.Perm Ω) (congrFun h i)
  refine ⟨hmem, hinj, ?_⟩
  have : Finite (∀ i, orbitFixedSet D (E i) (a i)) := Pi.finite
  rw [← Nat.card_pi]
  exact Nat.card_le_card_of_injective (fun c : C => fun i => ⟨(c : Equiv.Perm Ω) (a i),
    hmem c c.2 i⟩) fun c c' h => Subtype.ext (hinj c.2 c'.2 (funext fun i =>
      congrArg Subtype.val (congrFun h i)))

end CFSG.GroupActions
