module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22OddC

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T7.OddC
open scoped commutatorElement

section Frame

variable {G : Type} [Group G]

theorem oddCore_centralizer_eq_bot_of_twins [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    (hconj : ConjInvariant Ω) (hex : ExactMembers Ω) {K K' : Subgroup G} {z c a b : G}
    (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hzK : IsUniqueInvolution K z)
    (hzK' : IsUniqueInvolution K' z) (hne : K ≠ K')
    (hV : ∀ M ∈ Ω, IsUniqueInvolution M z → M = K ∨ M = K')
    (ha : a ∈ K) (hb : b ∈ K') (haa : a * a = z) (hbb : b * b = z) (hc : c = a * b)
    (hc1 : c ≠ 1) (hcomm : Commutes K K') (hMK : IsClassicalMember3 K z)
    (hMK' : IsClassicalMember3 K' z) (hα : alphaOf (Subgroup.closure ({c, z} : Set G)) = ⊥)
    (hGen : K ⊔ K' ⊔ Subgroup.centralizer ({c} : Set G) = ⊤) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) = ⊥ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({c} : Set G) with hC
  set P : Subgroup G := K ⊔ K' with hP
  have hcz : ∀ x ∈ oddCoreOf C, x * z = z * x := by
    intro x hx
    have hcA : c ∈ Subgroup.closure ({c, z} : Set G) := Subgroup.subset_closure (by simp)
    have hzA : z ∈ Subgroup.closure ({c, z} : Set G) := Subgroup.subset_closure (by simp)
    exact T7Y.commute_of_alphaOf_eq_bot hcA hc1 hα hx hzA
  have hxC : ∀ x ∈ oddCoreOf C, x ∈ C := fun x hx => oddCoreOf_le_self C hx
  have hxc : ∀ x ∈ oddCoreOf C, x * c * x⁻¹ = c := by
    intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hxC x hx)
    rw [h]; group
  have hfix : ∀ x ∈ oddCoreOf C, conjSub x K = K ∧ conjSub x K' = K' := by
    intro x hx
    have hodd := odd_orderOf_of_mem_oddCoreOf hx
    have hmem : ∀ M ∈ Ω, IsUniqueInvolution M z → conjSub x M = K ∨ conjSub x M = K' := by
      intro M hM hMz
      have h1 := hMz.conj x
      rw [show x * z * x⁻¹ = z by rw [hcz x hx]; group] at h1
      exact hV _ (hconj x M hM) h1
    have a1 := hmem K hKΩ hzK
    have a2 := hmem K' hK'Ω hzK'
    exact ⟨conjSub_eq_self_of_odd hodd hne a1 a2,
      conjSub_eq_self_of_odd hodd hne.symm a2.symm a1.symm⟩
  have hcomm' : Commutes K' K := fun a ha d hd => (hcomm d hd a ha).symm
  have hc' : c = b * a := by rw [hc]; exact hcomm a ha b hb
  have hPc : ∀ x ∈ oddCoreOf C, P ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx
    obtain ⟨f1, f2⟩ := hfix x hx
    have hodd := odd_orderOf_of_mem_oddCoreOf hx
    have c1 : K ≤ Subgroup.centralizer ({x} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_outer hMK (hex K hKΩ) hcomm ha haa hb hc f1 f2 (hxc x hx) hodd hm).symm
    have c2 : K' ≤ Subgroup.centralizer ({x} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_outer hMK' (hex K' hK'Ω) hcomm' hb hbb ha hc' f2 f1 (hxc x hx) hodd hm).symm
    exact sup_le c1 c2
  set S : Set G := {y | ∃ g ∈ C, ∃ p ∈ P, y = g * p * g⁻¹} with hS
  set N : Subgroup G := Subgroup.closure S with hN
  have hPN : P ≤ N := fun p hp => Subgroup.subset_closure ⟨1, C.one_mem, p, hp, by group⟩
  have hSconj : ∀ g' ∈ C, ∀ y ∈ S, g' * y * g'⁻¹ ∈ S := by
    rintro g' hg' y ⟨g, hg, p, hp, rfl⟩
    exact ⟨g' * g, C.mul_mem hg' hg, p, hp, by group⟩
  have hNconj : ∀ g' ∈ C, conjSub g' N ≤ N := by
    intro g' hg'
    show N.map (MulAut.conj g').toMonoidHom ≤ N
    rw [hN, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using hSconj g' hg' y hy
  have hCnorm : C ≤ Subgroup.normalizer (N : Set G) := by
    intro g' hg'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hNconj g' hg' (conj_mem_conjSub hh)
    · intro hh
      have h1 := hNconj g'⁻¹ (C.inv_mem hg') (conj_mem_conjSub hh)
      simpa [mul_assoc] using h1
  have hNtop : Subgroup.normalizer (N : Set G) = ⊤ := by
    rw [eq_top_iff, ← hGen]
    exact sup_le (hPN.trans Subgroup.le_normalizer) hCnorm
  have hNnormal : N.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exact absurd (by rw [h]; exact le_top) hMK.not_le_center
  have hNtop' : N = ⊤ := by
    have := hNnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exfalso
      have hKP : K ≤ P := le_sup_left
      have hzN : z ∈ N := hPN (hKP hzK.mem)
      rw [h, Subgroup.mem_bot] at hzN
      exact hzK.ne_one hzN
    · exact h
  have hZ : oddCoreOf C = ⊥ := by
    refine eq_bot_iff.mpr (fun x hx => ?_)
    rw [Subgroup.mem_bot]
    have hSle : S ⊆ (Subgroup.centralizer ({x} : Set G) : Set G) := by
      rintro _ ⟨g, hg, p, hp, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hx' : g⁻¹ * x * g ∈ oddCoreOf C := by
        have := conj_mem_oddCoreOf (C.inv_mem hg) hx
        simpa using this
      have hp' : p ∈ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := hPc _ hx' hp
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hp'
      calc g * p * g⁻¹ * x = g * (p * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * p) * g⁻¹ := by rw [h1]
        _ = x * (g * p * g⁻¹) := by group
    have hNle : N ≤ Subgroup.centralizer ({x} : Set G) := (Subgroup.closure_le _).mpr hSle
    rw [hNtop'] at hNle
    have hxcenter : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hNle (Subgroup.mem_top g))
    rw [hcenter] at hxcenter
    exact Subgroup.mem_bot.mp hxcenter
  have hinj : Function.Injective C.subtype := C.subtype_injective
  have hZ' : (classicalInvolutionOddCore ↥C).map C.subtype = ⊥ := hZ
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hZ'

end Frame

end CFSG.ClassicalInvolution.Q3.Q3OCL
