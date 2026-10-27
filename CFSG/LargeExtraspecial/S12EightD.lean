module

public import CFSG.LargeExtraspecial.S12EightC
public import CFSG.LargeExtraspecial.S12Eight
public import CFSG.LargeExtraspecial.S12EightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

theorem s12_finrank_range_le_map {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (f : V →ₗ[ZMod 2] V) (H : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (LinearMap.range f) ≤
      finrank (ZMod 2) (H.map f) + (finrank (ZMod 2) V - finrank (ZMod 2) H) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl H
  have hsup : H ⊔ C = ⊤ := hC.sup_eq_top
  have hdim : finrank (ZMod 2) H + finrank (ZMod 2) C = finrank (ZMod 2) V := by
    have := Submodule.finrank_sup_add_finrank_inf_eq H C
    rw [hsup, hC.inf_eq_bot, finrank_bot, add_zero, finrank_top] at this
    exact this.symm
  rw [LinearMap.range_eq_map, ← hsup, Submodule.map_sup]
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
  have := Submodule.finrank_map_le f C
  omega

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem s12_finrank_commSpace_eq_width {x z : S.O} (hz : fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hxx : x * x = 1) (hxz : x * z * x⁻¹ = z ^ 2) :
    finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) = S.width := by
  have hrel : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) * z = (z : S.Qt ≃ₗ[ZMod 2] S.Qt) * z * x := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * z * x := by rw [hxz, pow_two]
  have h1 := s12_two_mul_finrank_fixSpace_le hz hrel
  have h2 := finrank_commSpace_add_finrank_fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hxx' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) * x = 1 := by rw [← Subgroup.coe_mul, hxx]; rfl
  have h3 := Submodule.finrank_mono (commSpace_le_fixSpace hxx')
  rw [S.finrank_Qt_eq_two_mul_width] at h1 h2
  omega

theorem s12_eight_caseA {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {z : S.O} (hz : z ∈ S.CXbar12 g)
    (hz0 : fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) (hzρ : S.M)
    (hzρe : S.ρ hzρ = z) {x : S.O} (hx : x ∈ S.Lbar g) (hxz : x * z * x⁻¹ = z ^ 2)
    (hbQa : ((hzρ : G) * g) * S.z * ((hzρ : G) * g)⁻¹ ∈ S.Qa g) : False := by
  set a := g * S.z * g⁻¹ with ha
  set b := ((hzρ : G) * g) * S.z * ((hzρ : G) * g)⁻¹ with hb
  obtain ⟨hbQ, hbne⟩ := S.s12_conj_mem haQ hne hzρ
  set ã := S.cl a
  set tb := S.cl b
  have hbcl : tb = (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ã := by
    rw [← hzρe, S.ρ_cl hzρ haQ]
    show S.cl b = _
    rw [hb, S.s12_mul_conj_z]
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hab : tb ≠ ã := by
    rw [hbcl]
    intro e
    have : ã ∈ fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) := mem_fixSpace.mpr e
    rw [hz0] at this
    exact ha0 ((Submodule.mem_bot _).mp this)
  have hxx : x * x = 1 := by
    have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx
    rwa [pow_two] at this
  have hdimx := S.s12_finrank_commSpace_eq_width hz0 hxx hxz
  have hxb : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) tb ≠ tb := by
    have hxa := S.s12_Lbar_apply_cl_a haQ hx
    have hrel : x * z = z ^ 2 * x := by
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z ^ 2 * x := by rw [hxz]
    rw [hbcl, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hrel, Subgroup.coe_mul,
      LinearEquiv.mul_apply, hxa]
    intro e
    have e' : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ((z : S.Qt ≃ₗ[ZMod 2] S.Qt) ã) =
        (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ã := by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← pow_two, e]
    have := (z : S.Qt ≃ₗ[ZMod 2] S.Qt).injective e'
    apply hab
    rw [hbcl, this]
  set Wa := S.clSub (S.QG ⊓ S.Qa g) with hWa
  set H := LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ ã) with hH
  set Mx := H.map ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hMx
  have hMxWa : Mx ≤ Wa := by
    rintro _ ⟨v, hv, rfl⟩
    exact S.s12_Lbar_apply_sub_mem haQ hx
      (OrthoF2.mem_orthogonal_span_singleton_iff.mp hv)
  have hbWa : tb ∈ Wa := S.cl_mem_clSub ⟨hbQ, hbQa⟩ hbQ
  have hbMx : tb ∉ Mx := by
    intro hbm
    have hbc : tb ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      obtain ⟨v, -, hv⟩ := hbm
      rw [← hv]
      exact sub_mem_commSpace _ v
    have hxx' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) * x = 1 := by rw [← Subgroup.coe_mul, hxx]; rfl
    exact hxb (mem_fixSpace.mp (commSpace_le_fixSpace hxx' hbc))
  have hdimH : finrank (ZMod 2) H = 2 * S.width - 1 := by
    rw [hH, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
      finrank_span_singleton ha0, S.finrank_Qt_eq_two_mul_width]
  have hdimMx : S.width ≤ finrank (ZMod 2) Mx + 1 := by
    have h : finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
        finrank (ZMod 2) Mx + (finrank (ZMod 2) S.Qt - finrank (ZMod 2) H) :=
      s12_finrank_range_le_map ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1) H
    rw [hdimx, hdimH, S.finrank_Qt_eq_two_mul_width] at h
    omega
  have hdimWa : finrank (ZMod 2) Wa = S.width := by
    refine le_antisymm (S.s12_finrank_clSub_le haQ hne) ?_
    have hsup : Mx ⊔ (ZMod 2) ∙ tb ≤ Wa :=
      sup_le hMxWa ((Submodule.span_singleton_le_iff_mem _ _).mpr hbWa)
    have hinf : Mx ⊓ (ZMod 2) ∙ tb = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hv1, hv2⟩
      rcases OrthoF2.mem_span_singleton_iff.mp hv2 with h | h
      · rw [h]; exact Submodule.zero_mem _
      · exact absurd (h ▸ hv1) hbMx
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Mx ((ZMod 2) ∙ tb)
    rw [hinf, finrank_bot, add_zero] at h1
    have h0 : tb ≠ 0 := S.s12_cl_ne_zero_of_conj hbQ hbne
    rw [finrank_span_singleton h0] at h1
    have h2 := Submodule.finrank_mono hsup
    omega
  have haW : ã ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := (S.timmesfeld_12_6 haQ hne ht htA).1
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hbW : tb ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hbcl]
    exact CXbar12_apply_mem htX hz haW
  have hWspan : Submodule.span (ZMod 2) {ã, tb} = commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    s12_span_pair_eq htA.2.2.2.1 haW hbW ha0 (S.s12_cl_ne_zero_of_conj hbQ hbne) hab.symm
  have htfix : ∀ w ∈ Wa, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro w hw
    have hfs := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate t.2
    have : w ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [hfs, ← hWspan]
      exact OrthoF2.mem_orthogonal_span_pair_iff.mpr
        ⟨S.s12_polar_clSub_QG_inf_Qa hne (S.s12_cl_a_mem_clSub haQ) hw,
          S.s12_polar_clSub_QG_inf_Qa hne hbWa hw⟩
    exact mem_fixSpace.mp this
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp ht
  have hyc : ∀ w ∈ S.QG ⊓ S.Qa g, y * w = w * y := by
    intro w hw
    have h1 := htfix _ (S.cl_mem_clSub hw hw.1)
    rw [S.ρ_cl _ hw.1] at h1
    change S.cl (y * w * y⁻¹) = S.cl w at h1
    have hconj : y * w * y⁻¹ = w := by
      rcases S.s12_conj_L0_eq_or hy hw.2 with h2 | h2
      · exact h2
      · exfalso
        rcases (S.cl_eq_cl_iff hw.1 (S.conj_mem_QG (S.L0_le_M g hy) hw.1)).mp h1.symm with
          h3 | h3
        · apply S.s12_conj_z_ne_one g
          calc a = a * w * w⁻¹ := by group
            _ = w * w⁻¹ := by rw [← h2, h3]
            _ = 1 := by group
        · apply hne
          calc a = a * w * w⁻¹ := by group
            _ = w * S.z * w⁻¹ := by rw [← h2, h3]
            _ = S.z := by rw [S.z_comm_QG hw.1]; group
    calc y * w = y * w * y⁻¹ * y := by group
      _ = w * y := by rw [hconj]
  have hyQ := S.s12_mem_of_centralizes haQ hne hdimWa hy.1 hyc
  exact htA.2.1 (by rw [(S.ρ_eq_one_iff _).mpr hyQ.1]; rfl)

end Setting

end CFSG.LargeExtraspecial
