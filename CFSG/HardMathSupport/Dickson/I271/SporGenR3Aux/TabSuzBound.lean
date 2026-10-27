module

public import Certificates.Data.TabSuzA

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Certificates.ChainArrays
open CFSG.HardMathSupport.Dickson.I271.TabSuzA (levList levCount)

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem card_inf_levelSubgroup_le_fix (N : Subgroup (Equiv.Perm (Fin n))) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) (hN : ∀ g ∈ N, ∀ q, X q = q → X (g q) = g q)
    {i : ℕ} (hi : i < Q.baseCount) (hfix : X (Q.base.get ⟨i, hi⟩) = Q.base.get ⟨i, hi⟩) :
    Nat.card (N ⊓ Q.levelSubgroup i : Subgroup (Equiv.Perm (Fin n))) ≤
      fixLevCount n (rawLevels n S base) x i *
        Nat.card (N ⊓ Q.levelSubgroup (i + 1) : Subgroup (Equiv.Perm (Fin n))) := by
  set b := Q.base.get ⟨i, hi⟩ with hb
  set K := (N ⊓ Q.levelSubgroup i : Subgroup (Equiv.Perm (Fin n)))
  have hL : ∀ g ∈ K, g • b ∈ fixLevList n (rawLevels n S base) x i := by
    intro g hg
    obtain ⟨hgN, hgi⟩ := hg
    rw [fixLevList, List.mem_filter]
    refine ⟨List.mem_finRange _, ?_⟩
    rw [Equiv.Perm.smul_def, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    have horb : g b ∈ Q.orbitPoints ⟨i, hi⟩ := by
      rw [Q.orbitPoints_eq_orbit]
      exact ⟨⟨g, hgi⟩, rfl⟩
    refine ⟨?_, (hA.orbitPoints_spec hF hi horb).1⟩
    rw [hx (g b)]
    exact congrArg Fin.val (hN g hgN b hfix)
  have h := card_le_of_orbit_subset K b _ hL
  have hstab : (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) b : Subgroup _) =
      N ⊓ Q.levelSubgroup (i + 1) := by
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩, inf_assoc]
  rw [hstab] at h
  exact h

theorem card_inf_levelSubgroup_le_orb (N : Subgroup (Equiv.Perm (Fin n))) {i : ℕ}
    (hi : i < Q.baseCount) :
    Nat.card (N ⊓ Q.levelSubgroup i : Subgroup (Equiv.Perm (Fin n))) ≤
      levCount n (rawLevels n S base) i *
        Nat.card (N ⊓ Q.levelSubgroup (i + 1) : Subgroup (Equiv.Perm (Fin n))) := by
  set b := Q.base.get ⟨i, hi⟩ with hb
  set K := (N ⊓ Q.levelSubgroup i : Subgroup (Equiv.Perm (Fin n)))
  have hL : ∀ g ∈ K, g • b ∈ levList n (rawLevels n S base) i := by
    intro g hg
    obtain ⟨hgN, hgi⟩ := hg
    rw [levList, List.mem_filter]
    refine ⟨List.mem_finRange _, ?_⟩
    rw [Equiv.Perm.smul_def, decide_eq_true_eq]
    have horb : g b ∈ Q.orbitPoints ⟨i, hi⟩ := by
      rw [Q.orbitPoints_eq_orbit]
      exact ⟨⟨g, hgi⟩, rfl⟩
    exact (hA.orbitPoints_spec hF hi horb).1
  have h := card_le_of_orbit_subset K b _ hL
  have hstab : (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) b : Subgroup _) =
      N ⊓ Q.levelSubgroup (i + 1) := by
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩, inf_assoc]
  rw [hstab] at h
  exact h

end Facts

end CFSG.HardMathSupport.Dickson.I271
