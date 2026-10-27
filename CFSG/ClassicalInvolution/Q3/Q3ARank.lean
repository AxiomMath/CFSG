module

public import CFSG.ClassicalInvolution.Q3.Q3ABoot

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure IsA2Pair3 (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  cls₁ : IsClassicalMember3 K₁ z₁
  cls₂ : IsClassicalMember3 K₂ z₂
  ne : z₁ ≠ z₂
  comm_involutions : z₁ * z₂ = z₂ * z₁
  not_comm : ¬ Commutes K₁ K₂

namespace IsA2Pair3

variable {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem symm (h : IsA2Pair3 Ω K₁ K₂ z₁ z₂) : IsA2Pair3 Ω K₂ K₁ z₂ z₁ where
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  cls₁ := h.cls₂
  cls₂ := h.cls₁
  ne := h.ne.symm
  comm_involutions := h.comm_involutions.symm
  not_comm hc := h.not_comm hc.symm

end IsA2Pair3

theorem exists_a2Pair3_of_a2Configuration {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (h : A2Configuration z K) :
    ∃ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsA2Pair3 (conjClass3 K) K₁ K₂ z₁ z₂ := by
  obtain ⟨g, h', hne, hne', hcomm, hnc⟩ := h
  refine ⟨conjSub g⁻¹ K, conjSub h'⁻¹ K, g⁻¹ * z * g⁻¹⁻¹, h'⁻¹ * z * h'⁻¹⁻¹, ⟨?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · exact ⟨g⁻¹, rfl⟩
  · exact ⟨h'⁻¹, rfl⟩
  · exact hz.conj g⁻¹
  · exact hz.conj h'⁻¹
  · simpa using hne'
  · simpa using hcomm
  · simpa [conjSub] using hnc

section CommonNeighbour

variable {Ω : Set (Subgroup G)} {K₁ K₂ M : Subgroup G} {z₁ z₂ w : G}

theorem le_centralizer_of_commutes (hz : IsClassicalMember3 K₁ z₁) (h : Commutes M K₁) :
    M ≤ Subgroup.centralizer ({z₁} : Set G) := fun m hm =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h m hm z₁ hz.mem)

variable [Finite G]

theorem bootData3_of_commonNbr (h : IsA2Pair3 Ω K₁ K₂ z₁ z₂) (hM : M ∈ Ω)
    (hw : IsClassicalMember3 M w) (h₁ : Commutes M K₁) (h₂ : Commutes M K₂)
    (hnot : w ∉ Subgroup.closure ({z₁, z₂} : Set G)) : BootData3 Ω :=
  bootData3_of_pair hM hw h.cls₁.isCentralInvolution.sq h.cls₂.isCentralInvolution.sq
    h.cls₁.ne_one h.cls₂.ne_one h.ne h.comm_involutions
    (le_centralizer_of_commutes h.cls₁ h₁) (le_centralizer_of_commutes h.cls₂ h₂) hnot

theorem commonNbr_involution_mem (hB : ¬ BootData3 Ω) (h : IsA2Pair3 Ω K₁ K₂ z₁ z₂)
    (hM : M ∈ Ω) (hw : IsClassicalMember3 M w) (h₁ : Commutes M K₁) (h₂ : Commutes M K₂) :
    w = z₁ ∨ w = z₂ ∨ w = z₁ * z₂ :=
  eq_or_eq_or_eq_mul_of_not_bootData3 hB hM hw h.cls₁.isCentralInvolution.sq
    h.cls₂.isCentralInvolution.sq h.cls₁.ne_one h.cls₂.ne_one h.ne h.comm_involutions
    (le_centralizer_of_commutes h.cls₁ h₁) (le_centralizer_of_commutes h.cls₂ h₂)

theorem le_centralizer_of_commonNbr (hB : ¬ BootData3 Ω) (h : IsA2Pair3 Ω K₁ K₂ z₁ z₂)
    (hM : M ∈ Ω) (hw : IsClassicalMember3 M w) (h₁ : Commutes M K₁) (h₂ : Commutes M K₂) :
    K₂ ≤ Subgroup.centralizer ({z₁} : Set G) ∨ K₁ ≤ Subgroup.centralizer ({z₂} : Set G) := by
  rcases commonNbr_involution_mem hB h hM hw h₁ h₂ with rfl | rfl | rfl
  ·
    left
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h₂ _ hw.mem k hk).symm
  · right
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h₁ _ hw.mem k hk).symm
  · right
    intro k hk
    have e : z₁ * z₂ * k = k * (z₁ * z₂) := h₁ _ hw.mem k hk
    have e1 : z₁ * k = k * z₁ := h.cls₁.isCentralInvolution.central k hk
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have : z₁ * (z₂ * k) = z₁ * (k * z₂) := by
      calc z₁ * (z₂ * k) = z₁ * z₂ * k := by rw [mul_assoc]
        _ = k * (z₁ * z₂) := e
        _ = (k * z₁) * z₂ := by rw [mul_assoc]
        _ = (z₁ * k) * z₂ := by rw [e1]
        _ = z₁ * (k * z₂) := by rw [mul_assoc]
    exact (mul_left_cancel this).symm

end CommonNeighbour

end CFSG.ClassicalInvolution.Q3
