module

public import CFSG.LargeExtraspecial.S13EightE
public import CFSG.LargeExtraspecial.S13FiveF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

theorem timmesfeld_13_8
    (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K)
    (hii : ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ Ebar S g K → Rbar S g τ = S.Lbar g ∨ LinCase S g hτ) :
    False := by
  obtain ⟨σ, hσ, hσE, hL, h3⟩ := timmesfeld_13_5 hCE Y hii
  have h3' := finrank_Vt_le_three hCE Y hσ hσE hL
  have hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M,
      v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧ σ ∈ S.Lbar ((m : G) * g) ∧
      Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) :=
    fun v hv hv0 => linCase_pt Y.H hσ hL hv hv0
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  obtain ⟨c, hcU⟩ := exists_pt_not_mem Y.H Y.irr
    (Y.sup_ne_top (Vt_le_clSub_of_V_le hL.le_Qa) hk hk1)
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  have hdim := finrank_inf_perp_ge (Vt S g σ) (Fbar S ((c : G) * g) K)
  rw [Yc.finrank_Fbar] at hdim
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h0 => by
    rw [h0, finrank_bot] at hdim; omega :
      Vt S g σ ⊓ perp S (Fbar S ((c : G) * g) K) ≠ ⊥)
  obtain ⟨hdV, hdP⟩ := Submodule.mem_inf.mp hd
  obtain ⟨md, rfl, hσd, hVd⟩ := hpts _ hdV hd0
  have Y' : Hyp13 S ((md : G) * g) K := Y.mul rfl
  have hVt' : Vt S ((md : G) * g) σ = Vt S g σ := Vt_mul md σ
  have hσE' : σ ∉ Ebar S ((md : G) * g) K := fun h =>
    hσE (mem_Ebar.mpr ⟨hσ, (mem_Ebar.mp h).2⟩)
  have hpts' : ∀ v ∈ Vt S ((md : G) * g) σ, v ≠ 0 → ∃ m : S.M,
      v = S.cl ((m : G) * ((md : G) * g) * S.z * ((m : G) * ((md : G) * g))⁻¹) ∧
      σ ∈ S.Lbar ((m : G) * ((md : G) * g)) ∧
      Vt S ((md : G) * g) σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * ((md : G) * g))) := by
    intro v hv hv0
    rw [hVt'] at hv ⊢
    obtain ⟨m, rfl, h1, h2⟩ := hpts v hv hv0
    exact ⟨m * md⁻¹, by rw [coe_mul_inv_mul], by rwa [coe_mul_inv_mul],
      by rwa [coe_mul_inv_mul]⟩
  obtain ⟨pE, pU, pX, pF, hEA, hXA, hXE, hXU, hFA, hFE, hFU, hXF, hli⟩ :=
    Y'.exists_config hCE hσd hσE' hpts' (hVt' ▸ hVd) (by rw [hVt']; omega) hk hk1
      (c := c * md⁻¹) (by rw [coe_mul_inv_mul, hVt']; exact hcU)
      (by rw [coe_mul_inv_mul]; exact hdP)
  exact Y.false_of_config' hCE hii ⟨md, rfl⟩ ⟨pE * md, (coe_mul_mul pE md g).symm⟩
    ⟨pU * md, (coe_mul_mul pU md g).symm⟩ ⟨pX * md, (coe_mul_mul pX md g).symm⟩
    ⟨pF * md, (coe_mul_mul pF md g).symm⟩ hEA hXA hXE hXU hFA hFE hFU hXF hli

end Hyp13

end CFSG.LargeExtraspecial.S13
