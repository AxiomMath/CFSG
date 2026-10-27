module

public import CFSG.LargeExtraspecial.DWCaseIIBBound
public import CFSG.LargeExtraspecial.DWCaseIIBConfig
public import CFSG.ClassicalGroups.Alternating.Generation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.LocalAnalysis.ComponentInitial

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
  (hM : S.M ≤ normalizer (A : Set G))
  (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
  (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
include hA hM hII hbad

theorem spConfig_of_hyp (h1 : 1 ≤ S.width) {g : G} (hxA : g * S.z * g⁻¹ ∈ A)
    (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hsp : finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S g) + 1) :
    SpConfig S A hM := by
  have := finiteDimensional_Qt (S := S)
  have hWs := q_spanD hII
  have hD := hA.spanD_eq_clSub hM hII hxA hxz h1 hbad
  have hfam := hA.isHypFamily_axisV hM hII hbad hxA hxz hsp
  rw [hD] at hfam
  have hB := hfam.form_isAlt
  have hBn := hfam.form_nondegenerate
  refine ⟨hfam.form, hBn, hB, fun f => ⟨?_, fun hf => ?_⟩⟩
  ·
    rintro ⟨⟨_, m, rfl⟩, rfl⟩ u v
    rw [hfam.form_apply, hfam.form_apply, coe_resAt_apply, coe_resAt_apply]
    exact hypFun_ρ hWs m (by rw [hD]; exact u.2) (by rw [hD]; exact v.2)
  ·
    have hgen : bilinIsometryGroup hfam.form ≤ (resAt S A hM).range.comap
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (S.clSub A)).toMonoidHom := by
      rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hB hBn,
        closure_le]
      rintro _ ⟨a, c, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      by_cases hc : c = 0 ∨ a = 0
      · have h1 : CFSG.ClassicalGroups.Alternating.symplecticTransvection hfam.form hB a c = 1 :=
          Units.ext (LinearMap.ext fun x => by
            rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply]
            rcases hc with rfl | rfl
            · rw [zero_mul, zero_smul, add_zero]
              rfl
            · rw [smul_zero, add_zero]
              rfl)
        rw [h1, map_one]
        exact one_mem _
      push Not at hc
      obtain ⟨hc0, ha0⟩ := hc
      have hc1 : c = 1 := by
        rcases zmod2_dichotomy c with h | h
        · exact absurd h hc0
        · exact h
      subst hc1
      have ha0' : (a : S.Qt) ≠ 0 := fun e => ha0 (Subtype.ext e)
      obtain ⟨hk1, hk2, hk3⟩ := repD_spec hWs (by rw [hD]; exact a.2) ha0'
      set k := repD S (a : S.Qt)
      have hkA := hII k hk1
      have hax : axisV S (a : S.Qt) = axisA S A k := by
        rw [← hk3, axisV_cl hWs hk1 hk2, hA.axisD_eq hII hkA hk2, hD]
        exact inf_eq_left.mpr (S.clSub_mono inf_le_left)
      obtain ⟨t, ht, htw⟩ := hA.exists_Abar_eq hM hII hkA hk2 (hfam.form.flip a) fun w hw => by
        change hfam.form w a = 0
        rw [hfam.form_eq_zero_iff w ha0', hax]
        exact hw
      refine ⟨⟨t, Abar_le_Mbar A k ht⟩, LinearEquiv.ext fun w => Subtype.ext ?_⟩
      rw [coe_resAt_apply, htw w, hk3]
      change _ = ((CFSG.ClassicalGroups.Alternating.symplecticTransvection hfam.form hB a 1 :
        S.clSub A →ₗ[ZMod 2] S.clSub A) w : S.Qt)
      rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
      rfl
    have hmem : (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (S.clSub A)).symm f ∈
        bilinIsometryGroup hfam.form := by
      rw [mem_bilinIsometryGroup]
      intro x y
      have e : ∀ v, (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
          (S.clSub A)).symm f : LinearMap.GeneralLinearGroup (ZMod 2) (S.clSub A)) :
            S.clSub A →ₗ[ZMod 2] S.clSub A) v = f v := fun v => by
        rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
          MulEquiv.apply_symm_apply]
        rfl
      rw [e, e]
      exact hf x y
    have := hgen hmem
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this

end MaxEA

end CFSG.LargeExtraspecial.DW
