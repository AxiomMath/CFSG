module

public import CFSG.GH74.GLS.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG CFSG.GH74.GLS

theorem aor_pCore_isPGroup {G : Type*} [Group G] (p : ℕ) : IsPGroup p (CFSG.pCore p G) := by
  apply Sylow.sSup_of_normal
  · intro N hN
    exact hN.2
  · intro N hN
    exact hN.1

theorem aor_isSolvable_pPrimePCore_two (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable ↥(pPrimePCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup X := pPrimePCore 2 X
  let N : Subgroup X := pPrimeCore 2 X
  let g : ↥P →* ↥(pCore 2 (X ⧸ N)) :=
    ((QuotientGroup.mk' N).comp P.subtype).codRestrict (pCore 2 (X ⧸ N)) fun x => x.2
  have hNP : N ≤ P := by
    intro n hn
    show QuotientGroup.mk' N n ∈ pCore 2 (X ⧸ N)
    have h : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [h]
    exact one_mem _
  have hNsol : Group.IsSolvable ↥(N.subgroupOf P) := by
    have hcard : Nat.card ↥(N.subgroupOf P) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by
      rw [hcard]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hQsol : Group.IsSolvable ↥(pCore 2 (X ⧸ N)) := by
    have := (aor_pCore_isPGroup (G := X ⧸ N) 2).isNilpotent
    infer_instance
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf P).subtype g ?_
  intro x hx
  have h1 : QuotientGroup.mk' N (x : X) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
  exact ⟨⟨x, (QuotientGroup.eq_one_iff (x : X)).mp h1⟩, rfl⟩

theorem aor_commutator_pPrimePCore_eq_bot {H : Type} [Group H] [Finite H] {I : Subgroup H}
    (hI : IsComponent I) : ⁅pPrimePCore 2 H, I⁆ = ⊥ := by
  have hsol := aor_isSolvable_pPrimePCore_two H
  have h := (CFSG.LocalCores.component_solvable_centralizer hsol
    (Subgroup.Normal.isSubnormal inferInstance)).1 I hI
  rw [Subgroup.commutator_comm]
  exact h

end CFSG.OddStandard.SmallF3.Omega
