module

public import CFSG.LargeExtraspecial.S8KN
public import CFSG.LargeExtraspecial.S8KO
public import CFSG.LargeExtraspecial.S9GenG
public import CFSG.LargeExtraspecial.S8KM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem commSpace_mul_eq_sup {x y : S.O}
    (hinf : commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hx : ∀ v ∈ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    commSpace ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hle : commSpace ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    have h1 := hx _ (sub_mem_commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
    rw [map_sub] at h1
    have e : ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by
      rw [coe_mul_apply]
      calc (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) - u =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
            (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
        _ = _ := by rw [h1]; abel
    rw [e]
    exact Submodule.add_mem_sup (sub_mem_commSpace _ u) (sub_mem_commSpace _ u)
  have h1 := S9.finrank_commSpace_mul_eq hinf hx
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have h3 := Submodule.finrank_eq_zero.mpr hinf
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem mul_mem_N1bar {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    σ * τ ∈ N1bar S g t τ := by
  have R := B.red
  have := R.nqHyp
  have hσK := mem_CMt_of_mem_conjCentM hσ
  have hτK := mem_CMt_of_mem_conjCentM B.mem
  have hφ := B.nqComm_eq hσ hσN
  have hlin : ∀ v : NQ S g t, S9.nqLinC ⟨σ, hσK⟩ v = S9.nqLinC ⟨τ, hτK⟩ v := fun v =>
    add_right_cancel ((nqComm_apply _ v).symm.trans ((LinearMap.congr_fun hφ v).trans
      (nqComm_apply _ v)))
  have hττ : (⟨τ, hτK⟩ : CMt S t) * ⟨τ, hτK⟩ = 1 :=
    Subtype.ext (mul_self_of_mem_conjCentM H ht B.mem)
  have hc : ∀ y ∈ Nbar S g t, (σ * τ) * y * (σ * τ)⁻¹ * y⁻¹ ∈ zpowers t := by
    intro y hy
    have h1 : S9.nqLinC (⟨σ, hσK⟩ * ⟨τ, hτK⟩) (nqMk ⟨y, hy⟩) = nqMk ⟨y, hy⟩ :=
      (S9.nqLinC_comp _ _ _).symm.trans ((hlin _).trans ((S9.nqLinC_comp _ _ _).trans
        ((congrArg (fun s => S9.nqLinC s (nqMk ⟨y, hy⟩)) hττ).trans (S9.nqLinC_one _))))
    have h2 := (nqMk_eq_iff _ _).mp ((S9.nqLinC_mk _ _).symm.trans h1)
    have h3 : y * ((σ * τ * y * (σ * τ)⁻¹)⁻¹ * y)⁻¹ * y⁻¹ ∈ zpowers t :=
      (conj_mem_zpowers_iff (commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar hy))).mpr (inv_mem h2)
    have e2 : y * ((σ * τ * y * (σ * τ)⁻¹)⁻¹ * y)⁻¹ * y⁻¹ = σ * τ * y * (σ * τ)⁻¹ * y⁻¹ := by
      group
    rwa [e2] at h3
  have hστM : σ * τ ∈ S.Mbar := mul_mem hσ.1 B.mem.1
  have hστN := mem_Nbar_of_comm_mem_zpowers R.hCE R.hNo R.hΩ D R.six_le R.hA7 hστM hc
  refine B.mem_N1bar_of_fix hστN fun w hw => ?_
  have hwσ : w ∈ S2.perp S.q (Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    rw [B.sup_eq hσ hσN]
    exact hw
  rw [perp_sup_commSpace] at hw hwσ
  rw [coe_mul_apply, mem_fixSpace.mp hw.2, mem_fixSpace.mp hwσ.2]

end Bad4

end CFSG.LargeExtraspecial.S8
