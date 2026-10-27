module

public import CFSG.Open.OrderForm

public section

open CFSG.Open

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

abbrev Involution (G : Type*) [Group G] := {t : G // orderOf t = 2}

@[expose] def conjugateInvolution (g : G) (t : Involution G) : Involution G :=
  ⟨MulAut.conj g t, (MulAut.conj g).orderOf_eq t |>.trans t.property⟩

@[simp]
theorem conjugateInvolution_one (t : Involution G) : conjugateInvolution 1 t = t := by
  apply Subtype.ext
  simp [conjugateInvolution]

@[simp]
theorem conjugateInvolution_mul (g h : G) (t : Involution G) :
    conjugateInvolution (g * h) t = conjugateInvolution g (conjugateInvolution h t) := by
  apply Subtype.ext
  simp [conjugateInvolution, MulAut.conj_apply, mul_assoc]

@[simp]
theorem conjugateInvolution_self (t : Involution G) : conjugateInvolution (t : G) t = t := by
  apply Subtype.ext
  simp [conjugateInvolution, MulAut.conj_apply, mul_assoc]

theorem conjugateInvolution_injective (g : G) : Function.Injective (conjugateInvolution g) := by
  intro t u heq
  apply Subtype.ext
  exact (MulAut.conj g).injective (congrArg Subtype.val heq)

theorem involutionGraph_adj_iff (t u : Involution G) :
    (disconnectedInvolutionCommutingGraph G).Adj t u ↔
      t ≠ u ∧ (t : G) * u = u * t := by
  simp only [disconnectedInvolutionCommutingGraph, SimpleGraph.fromRel_adj, eq_comm,
    or_self]

@[expose] def conjugationGraphHom (g : G) :
    disconnectedInvolutionCommutingGraph G →g disconnectedInvolutionCommutingGraph G where
  toFun := conjugateInvolution g
  map_rel' := by
    intro t u hadj
    obtain ⟨hne, hcomm⟩ := (involutionGraph_adj_iff t u).mp hadj
    apply (involutionGraph_adj_iff _ _).mpr
    constructor
    · exact fun heq => hne (conjugateInvolution_injective g heq)
    · change (MulAut.conj g) (t : G) * (MulAut.conj g) (u : G) =
        (MulAut.conj g) (u : G) * (MulAut.conj g) (t : G)
      simpa only [map_mul] using congrArg (MulAut.conj g) hcomm

theorem reachable_conjugate {t u : Involution G}
    (hpath : (disconnectedInvolutionCommutingGraph G).Reachable t u) (g : G) :
    (disconnectedInvolutionCommutingGraph G).Reachable
      (conjugateInvolution g t) (conjugateInvolution g u) :=
  hpath.map (conjugationGraphHom g)

theorem reachable_of_commute (t u : Involution G) (hcomm : (t : G) * u = u * t) :
    (disconnectedInvolutionCommutingGraph G).Reachable t u := by
  by_cases heq : t = u
  · subst u
    exact SimpleGraph.Reachable.rfl
  · exact ((involutionGraph_adj_iff t u).mpr ⟨heq, hcomm⟩).reachable

@[expose] def componentStabilizer (t : Involution G) : Subgroup G where
  carrier := {g | (disconnectedInvolutionCommutingGraph G).Reachable t
    (conjugateInvolution g t)}
  one_mem' := by
    change (disconnectedInvolutionCommutingGraph G).Reachable t
      (conjugateInvolution 1 t)
    rw [conjugateInvolution_one]
  mul_mem' := by
    intro g h hg hh
    change (disconnectedInvolutionCommutingGraph G).Reachable t
      (conjugateInvolution (g * h) t)
    rw [conjugateInvolution_mul]
    exact hg.trans (reachable_conjugate hh g)
  inv_mem' := by
    intro g hg
    change (disconnectedInvolutionCommutingGraph G).Reachable t
      (conjugateInvolution g⁻¹ t)
    have hpath := reachable_conjugate hg g⁻¹
    simpa only [← conjugateInvolution_mul, inv_mul_cancel, conjugateInvolution_one]
      using hpath.symm

theorem mem_componentStabilizer_iff (t : Involution G) (g : G) :
    g ∈ componentStabilizer t ↔
      (disconnectedInvolutionCommutingGraph G).Reachable t (conjugateInvolution g t) :=
  Iff.rfl

theorem involution_mem_componentStabilizer {t u : Involution G}
    (hpath : (disconnectedInvolutionCommutingGraph G).Reachable t u) :
    (u : G) ∈ componentStabilizer t := by
  have hconj := reachable_conjugate hpath (u : G)
  rw [conjugateInvolution_self] at hconj
  exact hpath.trans hconj.symm

theorem componentStabilizer_base_mem (t : Involution G) : (t : G) ∈ componentStabilizer t :=
  involution_mem_componentStabilizer SimpleGraph.Reachable.rfl

end CFSG.DisconnectedInvolutionGraph.Helpers
