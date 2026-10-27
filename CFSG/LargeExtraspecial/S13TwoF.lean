module

public import CFSG.LargeExtraspecial.S13TwoD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

theorem Hyp13.Fbar_le_clSub (Y : Hyp13 S g K) : Fbar S g K ≤ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  obtain ⟨m, rfl⟩ := Y.exists_ρ_eq hk
  rw [← Y.timmesfeld_13_1 hk hk1]
  exact S.clSub_mono (inf_le_left.trans le_rfl)

theorem Hyp13.polar_Fbar (Y : Hyp13 S g K) {u v : S.Qt} (hu : u ∈ Fbar S g K)
    (hv : v ∈ Fbar S g K) : polar S.q u v = 0 :=
  polar_eq_zero_of_mem_clSub Y.hne (Y.Fbar_le_clSub hu) (Y.Fbar_le_clSub hv)

theorem Dbar_le_perp (Y : Hyp13 S g K) (Y₁ : Hyp13 S g₁ K)
    (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0) :
    (Fbar S g K ⊔ Fbar S g₁ K : Submodule (ZMod 2) S.Qt) ≤
      perp S (Fbar S g K ⊔ Fbar S g₁ K) := by
  intro v hv
  rw [mem_perp]
  intro w hw
  obtain ⟨f, hf, f₁, hf₁, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨f', hf', f₁', hf₁', rfl⟩ := Submodule.mem_sup.mp hw
  rw [polar_add_left, polar_add_right, polar_add_right, Y.polar_Fbar hf' hf, hperp f' hf' f₁ hf₁,
    QuadraticMap.polar_comm, hperp f hf f₁' hf₁', Y₁.polar_Fbar hf₁' hf₁]
  simp

theorem ptStab_map_conj {D : Submodule (ZMod 2) S.Qt} {y : S.O}
    (hy : ∀ d ∈ D, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D)
    (hy' : ∀ d ∈ D, ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D) :
    (ptStab S D).map (MulAut.conj y).toMonoidHom = ptStab S D := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_ptStab, mem_ptStab]
  constructor
  · intro hx d hd
    have h1 := hx _ (hy' d hd)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
    have h2 := congrArg (y : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    simpa [apply_inv_apply_O] using h2
  · intro hx d hd
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hx _ (hy d hd), inv_apply_apply_O]

end CFSG.LargeExtraspecial.S13
