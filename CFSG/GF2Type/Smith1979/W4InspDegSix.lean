module

public import CFSG.GF2Type.Smith1979.W4InspDefs
public import CFSG.GF2Type.Smith1979.W4InspSixRep
public import CFSG.LargeExtraspecial.AS35YFSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

omit [IsSimpleGroup G] in
theorem Mbar_le_Xbar12_of_sym6 (hS : S.S12Standing g t) (φ : S.Xbar12 g ≃* Equiv.Perm (Fin 6))
    (hφ : ∀ x : S.Xbar12 g, x ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ↔
      (φ x).IsSwap) :
    S.Mbar ≤ S.Xbar12 g := by
  intro m hm
  have hn : m ∈ normalizer (S.Xbar12 g : Set S.O) := Setting.Mbar_le_normalizer_Xbar12 hm
  let α : MulAut (S.Xbar12 g) :=
    { toFun := fun x => ⟨m * x * m⁻¹, (mem_normalizer_iff.mp hn x).mp x.2⟩
      invFun := fun x => ⟨m⁻¹ * x * m, (mem_normalizer_iff''.mp hn x).mp x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hα : ∀ y : S.Xbar12 g, ((α y : S.Xbar12 g) : S.O) = m * y * m⁻¹ := fun y => rfl
  obtain ⟨x, hx⟩ := AS35YF.mem_inner_of_perm_six φ hφ α fun e he => by
    rw [Set.mem_preimage, hα]
    exact Setting.conj_mem_Ebar12 hm he
  have hxy : ∀ y : S.Xbar12 g, (x : S.O) * y * (x : S.O)⁻¹ = m * y * m⁻¹ := fun y => by
    rw [← hα, ← hx]
    rfl
  have hc : m⁻¹ * (x : S.O) ∈ S.CXbar12 g := by
    refine ⟨S.Mbar.mul_mem (S.Mbar.inv_mem hm) (Setting.Xbar12_le_Mbar x.2),
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h := hxy ⟨y, hy⟩
    change (x : S.O) * y * (x : S.O)⁻¹ = m * y * m⁻¹ at h
    calc y * (m⁻¹ * (x : S.O)) = m⁻¹ * (m * y * m⁻¹) * x := by group
      _ = m⁻¹ * ((x : S.O) * y * (x : S.O)⁻¹) * x := by rw [h]
      _ = m⁻¹ * (x : S.O) * y := by group
  rw [hS.cent, mem_bot, inv_mul_eq_one] at hc
  rw [hc]
  exact x.2

omit [IsSimpleGroup G] in
theorem false_of_sym6 (hc : Ctx S g t)
    (φ : S.Xbar12 g ≃* Equiv.Perm (Fin 6))
    (hφ : ∀ x : S.Xbar12 g, x ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ↔
      (φ x).IsSwap) : False := by
  have htE : t ∈ S.Ebar12 g := Setting.mem_Ebar12_of_mem_Lbar hc.ht hc.htA
  have htX : t ∈ S.Xbar12 g := Setting.subset_Xbar12 htE
  have hMX := Mbar_le_Xbar12_of_sym6 hc.hS φ hφ
  have hfin : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set ρ : Equiv.Perm (Fin 6) →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    (S.actX12 g).comp φ.symm.toMonoidHom with hρ
  have hρx : ∀ x : S.Xbar12 g, ρ (φ x) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun x => by
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨a, b, hab, hτ⟩ := (hφ ⟨t, htX⟩).mp htE
  have ht2 : φ ⟨t, htX⟩ * φ ⟨t, htX⟩ = 1 := by
    rw [hτ, Equiv.swap_mul_self]
  have hts : Equiv.Perm.sign (φ ⟨t, htX⟩) = -1 := by
    rw [hτ, Equiv.Perm.sign_swap hab]
  have hirr : ∀ U : Submodule (ZMod 2) S.Qt,
      (∀ σ : Equiv.Perm (Fin 6), ∀ v ∈ U, ρ σ v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_contra hne
    push Not at hne
    refine hc.hred ⟨U, hne.1, hne.2, fun m v hv => ?_⟩
    have hmX : S.ρ m ∈ S.Xbar12 g := hMX ⟨m, rfl⟩
    have := hU (φ ⟨S.ρ m, hmX⟩) v hv
    rwa [hρx] at this
  refine false_of_alt_six_module (V := S.Qt)
    (by rw [S.finrank_Qt_eq_two_mul_width, hc.hw]) ρ ht2 hts hirr
    (T := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) hc.htA.2.2.2.1 fun v => ?_
  rw [hρx]
  exact sub_mem_commSpace _ v

end CFSG.GF2Type.Smith1979.W4Insp
