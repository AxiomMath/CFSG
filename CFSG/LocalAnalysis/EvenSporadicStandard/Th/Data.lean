module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

structure ThData (F : Type) [Group F] [Finite F] : Prop where
  simple : IsSimpleGroup F
  nonabelian : ∃ a b : F, a * b ≠ b * a
  allInner : ∀ α : MulAut F, ∃ f : F, α = MulAut.conj f
  invConj : ∀ u v : F, orderOf u = 2 → orderOf v = 2 → IsConj u v
  exists_invol : ∃ u : F, orderOf u = 2
  perfectCentralizer : ∀ u : F, orderOf u = 2 →
    ⁅centralizer ({u} : Set F), centralizer ({u} : Set F)⁆ = centralizer ({u} : Set F)
  sylowCenter : ∃ S : Subgroup F, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧
    ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x ^ 2 = 1

variable {F F' : Type*} [Group F] [Group F']

theorem map_centralizer_singleton (e : F ≃* F') (u : F) :
    (centralizer ({u} : Set F)).map e.toMonoidHom = centralizer ({e u} : Set F') := by
  ext x
  simp only [mem_map, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := congrArg e hy
    simpa using this
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    apply e.injective
    simpa using hx

theorem map_commutator_self (e : F ≃* F') (H : Subgroup F) :
    ⁅H.map e.toMonoidHom, H.map e.toMonoidHom⁆ = (⁅H, H⁆).map e.toMonoidHom :=
  (Subgroup.map_commutator H H e.toMonoidHom).symm

theorem ThData.of_mulEquiv {F F' : Type} [Group F] [Finite F] [Group F'] [Finite F']
    (e : F ≃* F') (h : ThData F') : ThData F := by
  have hsimple : IsSimpleGroup F := haveI := h.simple; e.isSimpleGroup
  refine ⟨hsimple, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  · intro α
    let α' : MulAut F' := e.symm.trans (α.trans e)
    obtain ⟨f', hf'⟩ := h.allInner α'
    refine ⟨e.symm f', MulEquiv.ext fun x => ?_⟩
    have := congrArg (fun β : MulAut F' => β (e x)) hf'
    simp only [α', MulEquiv.trans_apply, MulAut.conj_apply] at this
    apply e.injective
    simpa using this
  · intro u v hu hv
    have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (e v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    obtain ⟨c, hc⟩ := isConj_iff.1 (h.invConj _ _ hu' hv')
    refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
    simpa using hc
  · obtain ⟨u, hu⟩ := h.exists_invol
    exact ⟨e.symm u, by rw [MulEquiv.orderOf_eq]; exact hu⟩
  · intro u hu
    have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have h1 := h.perfectCentralizer _ hu'
    rw [← map_centralizer_singleton e u, map_commutator_self] at h1
    exact (map_injective e.injective) h1
  · obtain ⟨S, hS, hidx, hZ⟩ := h.sylowCenter
    refine ⟨S.map (e.symm : F' →* F), hS.map _, ?_, ?_⟩
    · rw [Subgroup.index_map_equiv]
      exact hidx
    · rintro x ⟨y, hy, rfl⟩ hcomm
      have h2 := hZ y hy (fun z hz => by
        have := hcomm (e.symm z) ⟨z, hz, rfl⟩
        simpa using congrArg e this)
      simpa using congrArg e.symm h2

end CFSG.EvenSporadicStandard.ThStd
