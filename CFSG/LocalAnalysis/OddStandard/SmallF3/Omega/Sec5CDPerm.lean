module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDTwist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem perm_of_mem (g : ↥L)
    (hg : (g : G) ∈ normalizer ((zpowers r ⊔ B : Subgroup G) : Set G)) :
    ∃ σ ∈ alternatingGroup (Fin 6), ∀ v, (g : G) * sec5c_phi L B r i fr φc v * (g : G)⁻¹ =
      sec5c_phi L B r i fr φc (permVec σ v) := by
  have hn : ∀ b ∈ ffB0 fr, (φc g : OGroup Q)⁻¹ * b * (φc g : OGroup Q) ∈ ffB0 fr := by
    intro b hb
    obtain ⟨c, hcB, hcφ⟩ := h.B_onto b hb
    have hcA : (c : G) ∈ (zpowers r ⊔ B : Subgroup G) := Subgroup.mem_sup_right hcB
    have hconjA : (g : G)⁻¹ * (c : G) * (g : G) ∈ (zpowers r ⊔ B : Subgroup G) :=
      (Subgroup.mem_set_normalizer_iff''.mp hg (c : G)).mp hcA
    have hu_eq : ((g⁻¹ * c * g : ↥L) : G) = (g : G)⁻¹ * (c : G) * (g : G) := by simp
    have huA : ((g⁻¹ * c * g : ↥L) : G) ∈ (zpowers r ⊔ B : Subgroup G) := by
      rw [hu_eq]; exact hconjA
    have huB : ((g⁻¹ * c * g : ↥L) : G) ∈ B := h.A_inf_L huA (g⁻¹ * c * g).2
    have hbu := h.B_map (g⁻¹ * c * g : ↥L) huB
    have hmap : (φc (g⁻¹ * c * g : ↥L) : OGroup Q) =
        (φc g : OGroup Q)⁻¹ * b * (φc g : OGroup Q) := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hcφ]
    rwa [hmap] at hbu
  obtain ⟨σ, K, hσ, _hK, hg_eq⟩ := sec5c_mono_of_norm hQ fr (φc g).2 hn
  have hrA : r ∈ (zpowers r ⊔ B : Subgroup G) := Subgroup.mem_sup_left (Subgroup.mem_zpowers r)
  have hA : (g : G) * r * (g : G)⁻¹ ∈ (zpowers r ⊔ B : Subgroup G) :=
    (Subgroup.mem_set_normalizer_iff.mp hg r).mp hrA
  exact ⟨σ, hσ, fun v => h.conj_phi hg_eq hA v⟩

theorem exists_of_perm {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ g : ↥L, (g : G) ∈ normalizer ((zpowers r ⊔ B : Subgroup G) : Set G) ∧
      ∀ v, (g : G) * sec5c_phi L B r i fr φc v * (g : G)⁻¹ =
        sec5c_phi L B r i fr φc (permVec σ v) := by
  obtain ⟨g, hφ, hA⟩ := h.exists_twist hσ
  have hg_eq : (φc g : OGroup Q) = fr.permOrth σ * fr.signChange (∅ : Finset (Fin 6)) := by
    rw [hφ, fr.signChange_empty, mul_one]
  have hform : ∀ v, (g : G) * sec5c_phi L B r i fr φc v * (g : G)⁻¹ =
      sec5c_phi L B r i fr φc (permVec σ v) := fun v => h.conj_phi hg_eq hA v
  refine ⟨g, ?_, hform⟩
  refine Subgroup.mem_set_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
  · intro hy
    obtain ⟨v, rfl⟩ := (h.mem_A_iff).mp hy
    rw [hform v]
    exact h.phi_mem_A (permVec σ v)
  · intro hy
    obtain ⟨w, hw⟩ := (h.mem_A_iff).mp hy
    have hperm : permVec σ (permVec σ.symm w) = w := by
      funext j
      simp [permVec, Equiv.symm_symm, Equiv.apply_symm_apply]
    have h2 : (g : G) * sec5c_phi L B r i fr φc (permVec σ.symm w) * (g : G)⁻¹ =
        (g : G) * y * (g : G)⁻¹ := by
      rw [hform (permVec σ.symm w), hperm, hw]
    have h3 : sec5c_phi L B r i fr φc (permVec σ.symm w) = y := by
      have h2' : (g : G) * (sec5c_phi L B r i fr φc (permVec σ.symm w) * (g : G)⁻¹) =
          (g : G) * (y * (g : G)⁻¹) := by
        simpa only [mul_assoc] using h2
      exact mul_right_cancel (mul_left_cancel h2')
    exact (h.mem_A_iff).mpr ⟨permVec σ.symm w, h3⟩

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega
