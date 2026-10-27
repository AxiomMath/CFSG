module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectSubgroupLeTwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Conj
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X]

theorem mem_twoResidualOf_top_of_isSimpleGroup [Finite X] [IsSimpleGroup X]
    (hnab : ∃ u v : X, u * v ≠ v * u) (u : X) :
    u ∈ GorensteinWalter.twoResidualOf (⊤ : Subgroup X) := by
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup X) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨v, w, hvw⟩ := hnab
      apply hvw
      have h1 : ⁅v, w⁆ ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
        Subgroup.commutator_mem_commutator (mem_top v) (mem_top w)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  have hperf : Group.IsPerfect ↥(⊤ : Subgroup X) := Subgroup.isPerfect_iff.mpr hcomm
  exact GorensteinWalter.perfect_subgroup_le_twoResidualOf ⊤ ⊤ le_rfl hperf (mem_top u)

theorem conjugate_centralizer_singleton (u g : X) :
    conjugate (centralizer ({u} : Set X)) g = centralizer ({g⁻¹ * u * g} : Set X) := by
  have h1 := LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g⁻¹ u
  rwa [inv_inv] at h1

theorem gsUnbalancingTriple_conjugate {a x : X} {J : Subgroup X}
    (hU : GSUnbalancingTriple a x J) (g : X) :
    GSUnbalancingTriple (g⁻¹ * a * g) (g⁻¹ * x * g) (conjugate J g) := by
  obtain ⟨ha, hx, hax, hJa, hJ, hJx, hJF⟩ := gsUnbalancingTriple_iff.mp hU
  set f := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfy : ∀ y : X, f y = g⁻¹ * y * g := fun y => by
    rw [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hCaf : (centralizer ({a} : Set X)).map f = centralizer ({g⁻¹ * a * g} : Set X) :=
    conjugate_centralizer_singleton a g
  have hOf : ((pPrimeCore 2 (centralizer ({x} : Set X))).map
      (centralizer ({x} : Set X)).subtype).map f =
      (pPrimeCore 2 (centralizer ({g⁻¹ * x * g} : Set X))).map
        (centralizer ({g⁻¹ * x * g} : Set X)).subtype := by
    rw [← hfy x]
    exact map_pPrimeCore_centralizer_of_mulAut (MulAut.conj g⁻¹) x
  obtain ⟨hJg, hJgp⟩ := GSThmB.Six.isPComponent_conjugate hJa hJ g
  have hCg : conjugate (centralizer ({a} : Set X)) g = centralizer ({g⁻¹ * a * g} : Set X) :=
    hCaf
  rw [hCg] at hJg hJgp
  refine gsUnbalancingTriple_iff.mpr ⟨?_, ?_, ?_, hJg, hJgp, ?_, ?_⟩
  · rw [← hfy a, hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, ha]
  · rw [← hfy x, hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hx]
  · rw [← hfy a, ← hfy x, ← map_mul, ← map_mul, hax]
  · have h1 := congrArg (Subgroup.map f) hJx
    rw [map_commutator, MonoidHom.map_zpowers, hfy x] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map f) hJF
    rw [map_commutator, Subgroup.map_inf _ _ _ hfinj, hOf, hCaf] at h1
    exact h1

variable [Finite X]

theorem isSylowIn_conjugate {S Y : Subgroup X} (hS : Seven.IsSylowIn S Y) (g : X) :
    Seven.IsSylowIn (conjugate S g) (conjugate Y g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSY, R, hR⟩ := hS
  have hle : conjugate S g ≤ conjugate Y g := map_mono hSY
  have h1 : Nat.card ↥((conjugate S g).subgroupOf (conjugate Y g)) = Nat.card ↥(conjugate S g) :=
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have h2 : Nat.card ↥(conjugate S g) = Nat.card ↥S :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have h3 : Nat.card ↥(conjugate Y g) = Nat.card ↥Y :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have h4 : Nat.card ↥(S.subgroupOf Y) = Nat.card ↥S :=
    Nat.card_congr (subgroupOfEquivOfLe hSY).toEquiv
  have h5 : Nat.card ↥(R : Subgroup ↥Y) = 2 ^ (Nat.card ↥Y).factorization 2 :=
    R.card_eq_multiplicity
  rw [hR, h4] at h5
  refine ⟨hle, Sylow.ofCard ((conjugate S g).subgroupOf (conjugate Y g)) ?_, rfl⟩
  rw [h1, h2, h3, h5]

end Eight2

end CFSG.ComponentClassification.GSThmB
