module

public import CFSG.LargeExtraspecial.S11ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Dset_eq_of_conj_eq {g' : G} (hc : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) (t : S.O) :
    Dset S g t = Dset S g' t := by
  ext X
  constructor
  · rintro ⟨h, rfl, ht⟩
    exact ⟨h, S.Lbar_eq_of_conj_eq (mul_conj_eq_of_conj_eq hc h), ht⟩
  · rintro ⟨h, rfl, ht⟩
    exact ⟨h, (S.Lbar_eq_of_conj_eq (mul_conj_eq_of_conj_eq hc h)).symm, ht⟩

theorem Vt_eq_of_conj_eq {g' : G} (hc : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) (t : S.O) :
    Vt S g t = Vt S g' t := by
  unfold Vt
  congr 1
  ext v
  constructor
  · rintro ⟨h, ht, rfl⟩
    refine ⟨h, ?_, by rw [mul_conj_eq_of_conj_eq hc h]⟩
    rwa [← S.Lbar_eq_of_conj_eq (mul_conj_eq_of_conj_eq hc h)]
  · rintro ⟨h, ht, rfl⟩
    refine ⟨h, ?_, by rw [mul_conj_eq_of_conj_eq hc h]⟩
    rwa [S.Lbar_eq_of_conj_eq (mul_conj_eq_of_conj_eq hc h)]

variable (hy : Hyp S g) {k : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG) (hkz : k * S.z * k⁻¹ ≠ S.z)
include hy hkQ hkz

theorem Hyp.Dset_eq (t : S.O) : Dset S k t = Dset S g t := by
  obtain ⟨m, hm, hmk⟩ := hy.fusion k hkQ hkz
  rw [← Dset_eq_of_conj_eq (g := (m : G) * g) (by rw [mul_conj_z S]; exact hmk),
    Dset_mul (⟨m, hm⟩ : S.M)]

theorem Hyp.Rbar_eq (t : S.O) : Rbar S k t = Rbar S g t := by
  rw [Rbar, Rbar, hy.Dset_eq hkQ hkz]

theorem Hyp.Vt_eq (t : S.O) : Vt S k t = Vt S g t := by
  obtain ⟨m, hm, hmk⟩ := hy.fusion k hkQ hkz
  rw [← Vt_eq_of_conj_eq (g := (m : G) * g) (by rw [mul_conj_z S]; exact hmk),
    Vt_mul (⟨m, hm⟩ : S.M)]

theorem Hyp.Nbar_eq (t : S.O) : Nbar S k t = Nbar S g t := by
  ext x
  rw [mem_Nbar, mem_Nbar, hy.Rbar_eq hkQ hkz, hy.Vt_eq hkQ hkz]

theorem Hyp.card_inf_centralizer {y : G} (hyL : y ∈ S.L0 k) (hyQ : y ∉ S.QG) :
    Nat.card (S.QG ⊓ S.Qa k ⊓ centralizer ({y} : Set G) : Subgroup G) = 2 ^ S.width := by
  have C := hy.cons_of hkQ hkz
  set P := S.clSub (S.QG ⊓ S.Qa k) with hP
  set s := S.ρ ⟨y, S.L0_le_M k hyL⟩ with hs
  have hsL : s ∈ S.Lbar k := S.ρ_mem_Lbar hyL
  have hs1 : s ≠ 1 := fun h => hyQ ((S.ρ_eq_one_iff _).mp h)
  set X := S.QG ⊓ S.Qa k ⊓ centralizer ({y} : Set G) with hX
  have hXQ : X ≤ S.QG := fun x hx => hx.1.1
  have hzX : S.z ∈ X := ⟨⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl hkQ hkz⟩,
    mem_centralizer_singleton_iff.mpr (S.z_comm (S.L0_le_M k hyL)).symm⟩
  have hXcl : S.clSub X = P ⊓ fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
      refine ⟨S.cl_mem_clSub hx.1 hxQ, mem_fixSpace.mpr ?_⟩
      rw [hs, S.ρ_cl _ hxQ]
      have hxy : y * x = x * y := (mem_centralizer_singleton_iff.mp hx.2).symm
      change S.cl (y * x * y⁻¹) = S.cl x
      rw [hxy, mul_inv_cancel_right]
    · rintro v ⟨hvP, hvf⟩
      obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hvP
      refine S.cl_mem_clSub ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩ hxQ
      have h1 : S.cl (y * x * y⁻¹) = S.cl x := by
        have := mem_fixSpace.mp hvf
        rwa [hs, S.ρ_cl _ hxQ] at this
      rcases (S.cl_eq_cl_iff hxQ (S.conj_mem_QG (S.L0_le_M k hyL) hxQ)).mp h1.symm with e | e
      · calc x * y = y * x * y⁻¹ * y := by rw [e]
          _ = y * x := by group
      · exfalso
        have h2 := (S.conjBy k).commutator_eq_one_or_z hyL.1 hx.2
        have e2 : y * x * y⁻¹ * x⁻¹ = S.z := by
          rw [e, S.z_comm_QG hxQ, mul_inv_cancel_right]
        rw [e2] at h2
        rcases h2 with h2 | h2
        · exact S.z_ne_one h2
        · exact hkz h2.symm
  have hdim : finrank (ZMod 2) P + 1 = S.width + 1 :=
    S.finrank_clSub_QG_inf_Qa hkQ hkz C.card_QG_inf_Qa
  have h1 := S2.finrank_map_sub_one_add (s : S.Qt ≃ₗ[ZMod 2] S.Qt) P
  have hmap : P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤
      (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Lbar_apply_sub_mem_span' hkQ hv hsL
  have h2 := Submodule.finrank_mono hmap
  have h3 := finrank_span_singleton_le_one (S.cl (k * S.z * k⁻¹))
  have hne : P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≠ ⊥ := by
    intro h0
    apply hs1
    refine C.faithful s hsL fun v hv => ?_
    have : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
        P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have h4 : finrank (ZMod 2) (P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) ≠ 0 :=
    fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hX' := S.clPre_clSub hXQ hzX
  rw [← hX', S.card_clPre, hXcl, S.card_submodule]
  have : finrank (ZMod 2) ↥(P ⊓ fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt)) + 1 = S.width := by omega
  rw [← this, pow_succ]
  ring

end CFSG.LargeExtraspecial.S11
