module

public import CFSG.Fischer.Uniq.Graph

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer SimpleGraph
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

@[expose] def Pair.compPerm (hP : Pair X E) : X →* Equiv.Perm (commGraph E).ConnectedComponent where
  toFun g := (Pair.conjAut hP g).connectedComponentEquiv
  map_one' := Equiv.ext fun C => C.ind fun a =>
    congrArg (commGraph E).connectedComponentMk (Subtype.ext (by simp))
  map_mul' g h := Equiv.ext fun C => C.ind fun a =>
    congrArg (commGraph E).connectedComponentMk (Subtype.ext (by simp [mul_assoc]))

@[simp]
theorem Pair.compPerm_mk (hP : Pair X E) (g : X) (a : E) :
    Pair.compPerm hP g ((commGraph E).connectedComponentMk a) =
      (commGraph E).connectedComponentMk (Pair.conjPerm hP g a) :=
  rfl

theorem Pair.reachable_conjPerm_iff (hP : Pair X E) (g : X) {a b : E} :
    (commGraph E).Reachable (Pair.conjPerm hP g a) (Pair.conjPerm hP g b) ↔
      (commGraph E).Reachable a b :=
  (Pair.conjAut hP g).reachable_iff

theorem Pair.reachable_conjPerm_self (hP : Pair X E) {e a : E} (h : (commGraph E).Reachable e a) :
    (commGraph E).Reachable e (Pair.conjPerm hP e a) := by
  have h' := (Pair.reachable_conjPerm_iff hP e).2 h
  rwa [conjPerm_eq_tau, Pair.tauE_self] at h'

theorem Pair.compPerm_eq_of_adj (hP : Pair X E) {e e' : E} (h : (commGraph E).Adj e e') :
    Pair.compPerm hP e = Pair.compPerm hP e' := by
  refine Equiv.ext fun C => C.ind fun y => ?_
  rw [Pair.compPerm_mk, Pair.compPerm_mk, ConnectedComponent.eq]
  by_cases hy : (commGraph E).Reachable e y
  · exact (Pair.reachable_conjPerm_self hP hy).symm.trans
      (h.reachable.trans (Pair.reachable_conjPerm_self hP (h.reachable.symm.trans hy)))
  · have hye : (y : X) * e ≠ e * y := mul_ne_mul_of_not_reachable fun h' => hy h'.symm
    have hye' : (y : X) * e' ≠ e' * y :=
      mul_ne_mul_of_not_reachable fun h' => hy (h.reachable.trans h'.symm)
    rw [conjPerm_eq_tau, conjPerm_eq_tau]
    exact (Pair.tau_adj_tau hP h hye hye').reachable

theorem Pair.not_reachable_tauE (hP : Pair X E) {e y : E} (hy : ¬(commGraph E).Reachable e y) :
    ¬(commGraph E).Reachable e (tauE hP e y) := by
  intro h
  apply hy
  have h' := (Pair.reachable_conjPerm_iff hP e).2 h
  rwa [conjPerm_eq_tau, conjPerm_eq_tau, Pair.tauE_self, Pair.tauE_tauE] at h'

theorem Pair.compPerm_mul_ne (hP : Pair X E) {e y : E} (hy : ¬(commGraph E).Reachable e y) :
    Pair.compPerm hP e * Pair.compPerm hP y ≠ Pair.compPerm hP y * Pair.compPerm hP e := by
  intro h
  have hC := congrArg (fun σ => σ ((commGraph E).connectedComponentMk y)) h
  simp only [Equiv.Perm.mul_apply, Pair.compPerm_mk, conjPerm_eq_tau, Pair.tauE_self,
    ConnectedComponent.eq] at hC
  have hey : (e : X) * y ≠ y * e := mul_ne_mul_of_not_reachable hy
  have h3 : tauE hP y (tauE hP e y) = e :=
    Subtype.ext (Pair.mul_mul_conj_eq hP e.2 y.2 hey)
  rw [h3] at hC
  exact Pair.not_reachable_tauE hP hy hC.symm

theorem Pair.connected_of_simple (hP : Pair X E) (hs : IsSimpleGroup (commutator X))
    (h : ∃ e f, e ∈ E ∧ f ∈ E ∧ e ≠ f ∧ e * f = f * e) : (commGraph E).Connected := by
  obtain ⟨e, f, he, hf, hne, hef⟩ := h
  have hadj : (commGraph E).Adj ⟨e, he⟩ ⟨f, hf⟩ := commGraph_adj_iff.2 ⟨hne, hef⟩
  refine (connected_iff_exists_forall_reachable _).2 ⟨⟨e, he⟩, fun y => ?_⟩
  by_contra hy
  set ψ := (Pair.compPerm hP).comp (commutator X).subtype
  rcases hs.eq_bot_or_eq_top_of_normal ψ.ker with hbot | htop
  · obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj hP he hf)
    have hmem : f * e⁻¹ ∈ commutator X := by
      rw [← hc, commutator_def, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top e)
    have hker : (⟨f * e⁻¹, hmem⟩ : commutator X) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      change Pair.compPerm hP (f * e⁻¹) = 1
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 (Pair.compPerm_eq_of_adj hP hadj).symm
    rw [hbot, Subgroup.mem_bot, Subtype.ext_iff] at hker
    exact hne (mul_inv_eq_one.1 hker).symm
  · have hmem : ⁅e, (y : X)⁆ ∈ commutator X := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top e) (Subgroup.mem_top _)
    have hker : (⟨_, hmem⟩ : commutator X) ∈ ψ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hker
    change Pair.compPerm hP ⁅e, (y : X)⁆ = 1 at hker
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hker
    exact Pair.compPerm_mul_ne hP hy hker

end CFSG.Fischer
