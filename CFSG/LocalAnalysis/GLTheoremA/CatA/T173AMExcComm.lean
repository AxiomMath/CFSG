module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open scoped commutatorElement

theorem uexc_comm_eq_bot {Ω : Type*} [Group Ω] {P Q : Subgroup Ω} (hP : ⁅P, P⁆ = P)
    (hPQ : ⁅P, Q⁆ ≤ Subgroup.centralizer (P : Set Ω)) : ⁅P, Q⁆ = ⊥ := by
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  refine CFSG.ComponentClassification.Quasisimple.perfect_double_commutator P Q ?_
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro g hg h hh
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.1 (hPQ hg) h hh).symm

theorem uexc_centralizer_of_map {Ω Ω' : Type*} [Group Ω] [Group Ω'] (π : Ω →* Ω')
    {P : Subgroup Ω} (hP : ⁅P, P⁆ = P) (hker : π.ker ≤ Subgroup.centralizer (P : Set Ω)) {b : Ω}
    (hb : π b ∈ Subgroup.centralizer ((P.map π : Subgroup Ω') : Set Ω')) :
    b ∈ Subgroup.centralizer (P : Set Ω) := by
  have hle : ⁅P, Subgroup.zpowers b⁆ ≤ Subgroup.centralizer (P : Set Ω) := by
    refine le_trans ?_ hker
    rw [Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [MonoidHom.mem_ker, map_commutatorElement, map_zpow,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.zpow_mem _ hb n)) (π g)
      (Subgroup.mem_map_of_mem π hg)
  have h0 := uexc_comm_eq_bot hP hle
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 : ⁅g, b⁆ ∈ (⁅P, Subgroup.zpowers b⁆ : Subgroup Ω) :=
    Subgroup.commutator_mem_commutator hg (Subgroup.mem_zpowers b)
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem uexc_cent_field {Ω Ω' : Type*} [Group Ω] [Group Ω'] (π : Ω →* Ω') {S B : Subgroup Ω}
    {x : Ω} (hS : ⁅S, S⁆ = S) (hker : π.ker ≤ Subgroup.centralizer (S : Set Ω)) (hx : x ∈ B)
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x) :
    ∀ b ∈ B.map π, b ∈ Subgroup.centralizer ((S.map π : Subgroup Ω') : Set Ω') ↔
      b ∈ Subgroup.zpowers (π x) := by
  rintro _ ⟨b, hb, rfl⟩
  constructor
  · intro h
    have h1 := (hcent b hb).1 (uexc_centralizer_of_map π hS hker h)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [map_zpow]⟩
  · intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    have hxC : x ∈ Subgroup.centralizer (S : Set Ω) := (hcent x hx).2 (Subgroup.mem_zpowers x)
    have hπx : π x ∈ Subgroup.centralizer ((S.map π : Subgroup Ω') : Set Ω') := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hxC s hs)]
    rw [← hn]
    exact Subgroup.zpow_mem _ hπx n

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
