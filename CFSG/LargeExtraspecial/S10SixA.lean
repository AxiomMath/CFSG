module

public import CFSG.LargeExtraspecial.S10Conj
public import CFSG.LargeExtraspecial.S10FlagB
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem mem_Nbar_of_noFix (X : Hyp10 S g t)
    (hno : ∀ x ∈ S.Lbar g, x ∉ Nbar S g t → x ∉ fixWstar X) {m : S.M}
    (hm : S.ρ m * t * (S.ρ m)⁻¹ ∈ S.Lbar g) : S.ρ m * t * (S.ρ m)⁻¹ ∈ Nbar S g t := by
  by_contra h
  refine hno _ hm h (mem_fixWstar_of_finrank_le X hm h ?_)
  have e : ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, finrank_commSpace_conj, finrank_commSpace_t X]

theorem mem_Wt_conj' {τ : S.O} {k : S.M} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) {v : S.Qt} :
    v ∈ Wt S g τ ↔ (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt S g t := by
  rw [mem_Wt, mem_Wt]
  constructor
  · intro h u hu
    have h1 := h (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
      ((mem_Vt_conj' haQ hτ).mpr (by rw [inv_apply_apply_O]; exact hu))
    rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ((S.ρ k)⁻¹).2,
      inv_apply_apply_O] at h1
  · intro h u hu
    have h1 := h _ ((mem_Vt_conj' haQ hτ).mp hu)
    rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ k).2,
      apply_inv_apply_O, apply_inv_apply_O] at h1

theorem mem_fixWstar_conj' {τ : S.O} (X : Hyp10 S g t) {k : S.M}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (Y : Hyp10 S g τ) {x : S.O} :
    x ∈ fixWstar Y ↔ (S.ρ k)⁻¹ * x * S.ρ k ∈ fixWstar X := by
  have hR : Rbar S g τ = (Rbar S g t).map (cK S k) := by subst hτ; exact Rbar_conj k t
  rw [mem_fixWstar, mem_fixWstar, hR, mem_map_cK_iff]
  refine and_congr_right fun _ => ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · have hw' : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g τ :=
      (mem_Wt_conj' X.haQ hτ).mpr (by rw [inv_apply_apply_O]; exact hw)
    have h1 := (mem_Vt_conj' X.haQ hτ).mp (h _ hw')
    rw [map_sub, inv_apply_apply_O] at h1
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using h1
  · have h1 := h _ ((mem_Wt_conj' X.haQ hτ).mp hw)
    refine (mem_Vt_conj' X.haQ hτ).mpr ?_
    rw [map_sub]
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply_O] using h1

theorem orthogonal_Wt (t : S.O) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (Wt S g t) = Vt S g t :=
  LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl _

theorem clSub_inf_fixSub_Abar (X : Hyp10 S g t) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) =
      S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
    fun v hv => ⟨hv.1, fun x hx => (mem_Nbar.mp hx.2).2 v hv.2⟩
  have hcard := card_mul_two_pow_finrank_fix X.H X.C (inf_le_left : S.Lbar g ⊓ Nbar S g t ≤ _)
  rw [X.card_Abar] at hcard
  have h5 := X.five_le_width
  have hdim : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t)) =
      3 := by
    have h1 : 2 ^ S.width = 2 ^ (S.width - 3) * 2 ^ 3 := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1] at hcard
    exact Nat.pow_right_injective le_rfl
      (Nat.eq_of_mul_eq_mul_left (by positivity) hcard)
  have h2 := finrank_clSub_inf_Vt X.H X.C X.ht X.ht1 X.hVQ
  rw [X.h4] at h2
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

end CFSG.LargeExtraspecial.S10
