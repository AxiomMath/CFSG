module

public import CFSG.Fischer.Uniq.Graph

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer SimpleGraph

variable {X : Type} [Group X] {E : Set X}

theorem Pair.tauE_tauE_involutive (hP : Pair X E) {x f : E} (hxf : (x : X) * f = f * x) :
    Function.Involutive fun y => tauE hP x (tauE hP f y) := by
  intro y
  have h1 : (x : X) * f * (x * f) = 1 := by
    calc (x : X) * f * (x * f) = x * (f * x) * f := by group
      _ = x * x * (f * f) := by rw [← hxf]; group
      _ = 1 := by rw [Pair.mul_self hP x.2, Pair.mul_self hP f.2, one_mul]
  simp only [Pair.tauE_tauE_eq_conjPerm]
  rw [← Equiv.Perm.mul_apply, ← map_mul, h1, map_one, Equiv.Perm.one_apply]

theorem Pair.tauE_tauE_tauE (hP : Pair X E) (x f a b : E) :
    tauE hP x (tauE hP f (tauE hP a b)) =
      tauE hP (tauE hP x (tauE hP f a)) (tauE hP x (tauE hP f b)) := by
  rw [Pair.tauE_tauE_eq_conjPerm hP x f, Pair.conjPerm_tauE, ← Pair.tauE_tauE_eq_conjPerm,
    ← Pair.tauE_tauE_eq_conjPerm]

theorem Pair.tau_tau_adj_iff (hP : Pair X E) (x f : E) {a b : E} :
    (commGraph E).Adj (tauE hP x (tauE hP f a)) (tauE hP x (tauE hP f b)) ↔
      (commGraph E).Adj a b := by
  rw [Pair.tau_adj_iff, Pair.tau_adj_iff]

theorem Pair.exists_fixedPointFree_of_not_connected (hP : Pair X E)
    (hc : ¬(commGraph E).Connected) (h : ∃ e f, e ∈ E ∧ f ∈ E ∧ e ≠ f ∧ e * f = f * e) :
    ∃ (C₁ C₂ : (commGraph E).ConnectedComponent) (x f : E), C₁ ≠ C₂ ∧ x ∈ C₁.supp ∧
      f ∈ C₁.supp ∧ (commGraph E).Adj x f ∧
      Set.BijOn (fun y => tauE hP x (tauE hP f y)) C₂.supp C₂.supp ∧
      Function.Involutive (fun y => tauE hP x (tauE hP f y)) ∧
      (∀ y ∈ C₂.supp, (commGraph E).Adj (tauE hP x (tauE hP f y)) y) ∧
      ∀ y ∈ C₂.supp, tauE hP x (tauE hP f y) ≠ y := by
  obtain ⟨e, f, he, hf, hne, hef⟩ := h
  have hadj : (commGraph E).Adj ⟨e, he⟩ ⟨f, hf⟩ := commGraph_adj_iff.2 ⟨hne, hef⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y : E, ¬(commGraph E).Reachable ⟨e, he⟩ y := by
    by_contra! hall
    exact hc ((connected_iff_exists_forall_reachable _).2 ⟨_, hall⟩)
  set C₂ := (commGraph E).connectedComponentMk y₀
  have hfar : ∀ y ∈ C₂.supp, (y : X) * e ≠ e * y ∧ (y : X) * f ≠ f * y := by
    intro y hy
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hy
    exact ⟨mul_ne_mul_of_not_reachable fun h => hy₀ (h.symm.trans hy),
      mul_ne_mul_of_not_reachable fun h => hy₀ (hadj.reachable.trans (h.symm.trans hy))⟩
  have hg : ∀ y ∈ C₂.supp, (commGraph E).Adj (tauE hP ⟨e, he⟩ (tauE hP ⟨f, hf⟩ y)) y :=
    fun y hy => Pair.tau_tau_adj hP hadj (hfar y hy).1 (hfar y hy).2
  have hmaps : Set.MapsTo (fun y => tauE hP ⟨e, he⟩ (tauE hP ⟨f, hf⟩ y)) C₂.supp C₂.supp :=
    fun y hy => (C₂.mem_supp_congr_adj (hg y hy)).2 hy
  have hinv := Pair.tauE_tauE_involutive hP (x := ⟨e, he⟩) (f := ⟨f, hf⟩) hef
  refine ⟨(commGraph E).connectedComponentMk ⟨e, he⟩, C₂, ⟨e, he⟩, ⟨f, hf⟩, fun h => ?_,
    (ConnectedComponent.mem_supp_iff _ _).2 rfl, ?_, hadj,
    ⟨hmaps, hinv.injective.injOn, fun y hy => ⟨_, hmaps hy, hinv y⟩⟩, hinv, hg,
    fun y hy => (hg y hy).ne⟩
  · exact hy₀ (ConnectedComponent.eq.1 h)
  · rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact hadj.reachable.symm

end CFSG.Fischer
