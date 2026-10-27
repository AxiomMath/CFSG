module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Levi
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Block

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Closure

theorem closure_commute_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ u ∈ Subgroup.closure S, ∀ v ∈ Subgroup.closure T, u * v = v * u := by
  have h1 : ∀ s ∈ S, Subgroup.closure T ≤ Subgroup.centralizer {s} := fun s hs => by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (h s hs t ht).symm
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    have := h1 s hs hv
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  intro u hu v hv
  have := h2 hu
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this v hv).symm

end Closure

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_smul_mem_rootGroup_right {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (c : K) : eichler Q u (c • w) ∈ rootGroup Q w := by
  have hcu : Q (c • u) = 0 := by rw [map_smul_eq_sq, hu, mul_zero]
  have hcuw : polar Q (c • u) w = 0 := by rw [polar_smul_left_eq, huw, mul_zero]
  rw [← eichler_smul_left, CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.eichler_swap hcu hw hcuw]
  exact eichler_mem_rootGroup (by rw [polar_neg_right, polar_comm, hcuw, neg_zero])

theorem eichler_smul_mem_rootGroup_left {u w : V} (huw : polar Q u w = 0) (c : K) :
    eichler Q u (c • w) ∈ rootGroup Q u :=
  eichler_mem_rootGroup (by rw [polar_smul_right_eq, huw, mul_zero])

end Eichler

section Levi

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def swapPair (P : HypPair Q) : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩

theorem orth_swapPair_right {A B : HypPair Q} (h : A.Orth B) : A.Orth (swapPair B) where
  ee := h.ef
  ef := h.ee
  fe := h.ff
  ff := h.fe

theorem leviV_comm_swap {A B : HypPair Q} (h : A.Orth B) :
    ∀ u ∈ leviV Q A.e B.e A.f B.f, ∀ v ∈ leviV Q A.e B.f A.f B.e, u * v = v * u := by
  refine closure_commute_closure ?_
  have hAe := A.Q_e
  have hAf := A.Q_f
  have hBe := B.Q_e
  have hBf := B.Q_f
  have hff : polar Q B.f A.f = 0 := by rw [polar_comm, h.ff]
  have hfe : polar Q B.e A.f = 0 := by rw [polar_comm, h.fe]
  rintro s (⟨c, rfl⟩ | ⟨c, rfl⟩) t (⟨c', rfl⟩ | ⟨c', rfl⟩)
  ·
    exact rootGroup_commute (eichler_smul_mem_rootGroup_left h.ef c)
      (eichler_smul_mem_rootGroup_left h.ee c')
  ·
    exact rootGroup_commute (eichler_smul_mem_rootGroup_right hAe hBf h.ef c)
      (eichler_smul_mem_rootGroup_left hff c')
  ·
    exact rootGroup_commute (eichler_smul_mem_rootGroup_left (polar_comm Q B.e A.f ▸ h.fe) c)
      (eichler_smul_mem_rootGroup_right hAe hBe h.ee c')
  ·
    exact rootGroup_commute (eichler_smul_mem_rootGroup_right hBe hAf hfe c)
      (eichler_smul_mem_rootGroup_right hBf hAf hff c')

end Levi

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
