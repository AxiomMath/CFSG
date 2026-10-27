module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4PerfApply
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.Generic.S45.LSporWit

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem j3_inner_centralizer_data :
    ∀ t ∈ j3P, orderOf t = 2 →
      ⁅centralizerIn j3P t, centralizerIn j3P t⁆ = centralizerIn j3P t ∧
        Nat.card ↥(centralizerIn j3P t) = 1920 := by
  obtain ⟨-, -, -, hrows, hcover, -, hshape, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  intro t htP ht2
  have htR : t ∈ j3R := Subgroup.mem_sup_left htP
  obtain ⟨r, hr, g, hg, htg⟩ := hcover t htR ht2
  obtain ⟨-, -, hrouter, hCr, hcard, -⟩ := hrows r hr
  have hrP : tp 6156 r.rep ∈ j3P := by
    have : tp 6156 r.rep = g⁻¹ * t * g := by rw [htg]; group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) htP) hg
  have hrout : r.outer = false := by
    by_contra hne
    exact (hrouter.1 (by simpa using hne)) hrP
  have hr0 : r.centOrder = 1920 := by
    have hm : (r.outer, r.classSize, r.centOrder) ∈
        j3Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map_of_mem hr
    rw [hshape] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · rw [hrout] at h
      exact absurd h (by decide)
  have hcls : t ∈ CFSG.Sporadic.Schreier.conjClass j3P (tp 6156 r.rep) := ⟨g, hg, htg⟩
  refine ⟨?_, ?_⟩
  ·
    have hperf : ⁅j3C r, j3C r⁆ = j3C r := by
      have hw := perfWit_of_all perfWit_j3_2A r hr hr0
      exact (perfWitOK_spec (by norm_num) hw).1
    have hCeq : centralizerIn j3P (tp 6156 r.rep) = j3C r := hCr.symm
    have h1 : ⁅centralizerIn j3P (tp 6156 r.rep), centralizerIn j3P (tp 6156 r.rep)⁆ =
        centralizerIn j3P (tp 6156 r.rep) := by rw [hCeq]; exact hperf
    have h2 := GHInv.commutator_centralizerIn_conj hg h1
    rw [← htg] at h2
    exact h2
  · rw [GHInv.card_centralizerIn_eq_of_mem_conjClass j3P hcls]
    exact hcard.trans hr0

theorem ivk73_j3 :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  refine ivk73_empty_of_perfect_centralizers (P := fun X _ => NativeSporadic.IsSporadic X .J3) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥j3P := e.trans j3PermEquiv
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact j3_outer_card_le
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥j3P := e.trans j3PermEquiv
    have hord : orderOf ((e' y : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨hperf, hcard⟩ := j3_inner_centralizer_data _ (e' y).2 hord
    refine ⟨GHInv.isPerfect_centralizer_of_equiv j3P e' y hperf, Or.inl ?_⟩
    rw [GHInv.card_centralizer_eq_centralizerIn j3P e' y]
    exact hcard

end CFSG.GH74.GLS.IVK
