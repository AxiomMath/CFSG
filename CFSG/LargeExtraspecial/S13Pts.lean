module

public import CFSG.LargeExtraspecial.S3bEleven
public import CFSG.LargeExtraspecial.S13Fbar
public import CFSG.LargeExtraspecial.S13Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem cl_mem_clSub_symm (H : Hyp4 S g) {h₁ h₂ : S.M}
    (h : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g))) :
    S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₂ : G) * g)) := by
  have hcQ := conj_mem_QG' S h₁.2 H.conj_mem
  have hdQ := conj_mem_QG' S h₂.2 H.conj_mem
  have hcz := conj_ne_z' S h₁.2 H.conj_ne
  have hdz := conj_ne_z' S h₂.2 H.conj_ne
  have hd : (h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹ ∈ S.Qa ((h₁ : G) * g) :=
    (mem_Qa_iff_cl_mem hcQ hcz hdQ).mpr h
  refine (mem_Qa_iff_cl_mem hdQ hdz hcQ).mp ?_
  by_cases hcd : (h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹ = (h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹
  · rw [hcd]
    exact S.conj_z_mem_Qa _
  · exact S.mem_Qa_symm (Ne.symm hcd) hd

theorem fix_of_mem_Lbar_inf {g₁ g₂ : G}
    (hne : S.cl (g₁ * S.z * g₁⁻¹) ≠ S.cl (g₂ * S.z * g₂⁻¹)) {s : S.O} (hs₁ : s ∈ S.Lbar g₁)
    (hs₂ : s ∈ S.Lbar g₂) {v : S.Qt} (hv₁ : v ∈ S.clSub (S.QG ⊓ S.Qa g₁))
    (hv₂ : v ∈ S.clSub (S.QG ⊓ S.Qa g₂)) : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have h1 := S.sub_mem_span_of_mem_clSub hs₁ hv₁
  have h2 := S.sub_mem_span_of_mem_clSub hs₂ hv₂
  rcases mem_span_cl_iff.mp h1 with e1 | e1
  · exact sub_eq_zero.mp e1
  · rcases mem_span_cl_iff.mp h2 with e2 | e2
    · exact sub_eq_zero.mp e2
    · exact absurd (e1.symm.trans e2) hne

theorem cl_mem_Fbar_of_le {g' : G} (H' : Hyp4 S g') (hle : Ebar S g K ≤ S.Lbar g') :
    S.cl (g' * S.z * g'⁻¹) ∈ Fbar S g K :=
  fun _ hx => Lbar_apply_cl H' (hle hx)

end CFSG.LargeExtraspecial.S13
