module

public import CFSG.LargeExtraspecial.S10SixC
public import CFSG.LargeExtraspecial.S13Gen
public import CFSG.LargeExtraspecial.S13TwoH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

theorem eq_of_add_eq_zero_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {v w : V}
    (h : v + w = 0) : v = w := by
  have h2 : w + w = 0 := by
    rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  calc v = v + w + w := by rw [add_assoc, h2, add_zero]
    _ = w := by rw [h, zero_add]

theorem exists_pt_add (H : Hyp4 S g) {h₁ h₂ : S.M}
    (h12 : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g)))
    (hne : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ≠
      S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹)) :
    ∃ h₃ : S.M, S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) =
      S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) +
        S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) := by
  have h₁Q := conj_mem_QG' S h₁.2 H.conj_mem
  have h₁z := conj_ne_z' S h₁.2 H.conj_ne
  have h₂Q := conj_mem_QG' S h₂.2 H.conj_mem
  have hc : (h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹ ∈ S.QG ⊓ S.Qa ((h₁ : G) * g) :=
    Subgroup.mem_inf.mpr ⟨h₂Q, (mem_Qa_iff_cl_mem h₁Q h₁z h₂Q).mpr h12⟩
  have hcb : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ∉
      (ZMod 2) ∙ S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) := by
    intro h
    rcases mem_span_cl_iff.mp h with h | h
    · exact cl_conj_z_ne_zero S h₂Q (conj_ne_z' S h₂.2 H.conj_ne) h
    · exact hne h
  obtain ⟨l, hl, hle⟩ := exists_Lbar_apply_eq_add h₁Q h₁z hc hcb
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ hl)
  refine ⟨m * h₂, ?_⟩
  rw [add_comm, ← hle, ρ_cl_conj_z S m h₂Q, Subgroup.coe_mul]
  congr 1
  group

namespace Hyp13

theorem eq_of_mem_Ebar_inf (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {h : S.M}
    (hg : g₁ = (h : G) * g) (hne : Fbar S g₁ K ≠ Fbar S g K) {ρ₁ ρ₂ : S.O}
    (h₁ : ρ₁ ∈ Ebar S g K ⊓ Ebar S g₁ K) (h₂ : ρ₂ ∈ Ebar S g K ⊓ Ebar S g₁ K)
    (h₁1 : ρ₁ ≠ 1) (h₂1 : ρ₂ ≠ 1) : ρ₁ = ρ₂ := by
  obtain ⟨X₁, hV₁⟩ := hyp10_and_Vt_eq_of_mem_inf Y hg hne h₁ h₁1
  obtain ⟨X₂, hV₂⟩ := hyp10_and_Vt_eq_of_mem_inf Y hg hne h₂ h₂1
  by_contra h12
  have hN : ρ₂ ∈ Nbar S g ρ₁ := by
    refine ⟨Lbar_le_Rbar X₁.ht (Ebar_le_Lbar (Subgroup.mem_inf.mp h₂).1), fun v hv => ?_⟩
    rw [hV₁] at hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, (mem_Fbar.mp hu) _ (Subgroup.mem_inf.mp h₂).1,
      (mem_Fbar.mp hw) _ (Subgroup.mem_inf.mp h₂).2]
  have hle := finrank_Vt_inf_Vt_le hCE X₁ X₂ hN (Ne.symm h12)
  rw [hV₁, hV₂, inf_idem, finrank_Dbar Y (Y.mul hg) hne] at hle
  omega

end Hyp13

end CFSG.LargeExtraspecial.S13
