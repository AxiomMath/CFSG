module

public import CFSG.CGT.PushingUpLit.SolK.GenFourA8
public import CFSG.GF2Type.Smith1979.W4C1Par
public import CFSG.LargeExtraspecial.DWTransGL
public import CFSG.LargeExtraspecial.S111CNorm
public import CFSG.LargeExtraspecial.S12Basic
public import CFSG.LargeExtraspecial.S4Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commute_of_mem_K (H : Hyp4 S g) (C : Cons311 S g) {k : S.O} (hkM : k ∈ S.Mbar)
    (hkD : ∀ d ∈ S.clSub (S.QG ⊓ S.Qa g), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d)
    {l : S.O} (hl : l ∈ S.Lbar g) : k * l = l * k := by
  have haQ := H.conj_mem
  have hka : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    hkD _ (S6.cl_mem_clSub_self haQ)
  obtain ⟨κ, rfl⟩ := MonoidHom.mem_range.mp hkM
  have hnorm : S.ρ κ ∈ normalizer (S.Lbar g : Set S.O) :=
    (S.timmesfeld_12_4_1 haQ H.conj_ne (by have := H.two_lt_width; omega) κ).mpr hka
  have hc : S.ρ κ * l * (S.ρ κ)⁻¹ * l⁻¹ ∈ S.Lbar g :=
    mul_mem ((mem_normalizer_iff.mp hnorm l).mp hl) (inv_mem hl)
  have hlinv : ∀ d ∈ S.clSub (S.QG ⊓ S.Qa g),
      ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    intro d hd
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (S6.Lbar_apply_sub_mem_span' haQ hd
      (inv_mem hl))
    have h2 : ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d - d ∈ S.clSub (S.QG ⊓ S.Qa g) := by
      rw [← hc]
      exact Submodule.smul_mem _ c (S6.cl_mem_clSub_self haQ)
    simpa using add_mem h2 hd
  have hfix : ∀ d ∈ S.clSub (S.QG ⊓ S.Qa g),
      ((S.ρ κ * l * (S.ρ κ)⁻¹ * l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d := by
    intro d hd
    have hd' := hlinv d hd
    have hk' : (((S.ρ κ)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d) = ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d := by
      conv_lhs => rw [← hkD _ hd']
      exact inv_apply_apply_O (S.ρ κ) _
    simp only [coe_mul_apply, hk', apply_inv_apply_O, hkD _ hd]
  have h1 : S.ρ κ * l * (S.ρ κ)⁻¹ * l⁻¹ = 1 := C.faithful _ hc hfix
  calc S.ρ κ * l = (S.ρ κ * l * (S.ρ κ)⁻¹ * l⁻¹) * l * S.ρ κ := by group
    _ = l * S.ρ κ := by rw [h1, one_mul]

theorem sectionalTwoRankLE_Mbar_of_K_trivial (hw : S.width = 4) (H : Hyp4 S g)
    (C : Cons311 S g)
    (hK : ∀ k ∈ S.Mbar,
      (∀ d ∈ S.clSub (S.QG ⊓ S.Qa g), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d) → k = 1) :
    CFSG.GH74.SectionalTwoRankLE S.Mbar 4 := by
  have haQ := H.conj_mem
  have hne := H.conj_ne
  obtain ⟨T, -, hTN⟩ := S11.exists_sylow_le_normalizer haQ C
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  let ρ : (T : Subgroup S.Mbar) →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    S.O.subtype.comp (S.Mbar.subtype.comp (T : Subgroup S.Mbar).subtype)
  have hDinv : ∀ x : (T : Subgroup S.Mbar), ∀ d ∈ S.clSub (S.QG ⊓ S.Qa g),
      ρ x d ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    intro x d hd
    have hxN : ((x : S.Mbar) : S.O) ∈ normalizer (S.Lbar g : Set S.O) :=
      hTN ⟨(x : S.Mbar), x.2, rfl⟩
    exact S6.apply_mem_clSub_of_fix haQ hne (x : S.Mbar).2 (fix_of_mem_normalizer H hxN) hd
  have hdim : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = 4 := by
    rw [finrank_clSub_QG_inf_Qa haQ hne C.card_QG_inf_Qa, hw]
  obtain ⟨e⟩ := DW.nonempty_linearEquiv_mulEquiv_GL hdim
  have hinj : Function.Injective (W4C1.Par.resD ρ hDinv) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have hfix := (W4C1.Par.resD_eq_one_iff ρ hDinv x).mp hx
    exact Subtype.ext (Subtype.ext (hK (x : S.Mbar) (x : S.Mbar).2 hfix))
  exact CFSG.CGT.PushingUpLit.SolK.SectionalTwoRankLE.of_sylow T
    (CFSG.GH74.SectionalTwoRankLE.of_injective _ hinj
      (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv e.symm
        CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_GL_four_two))

end CFSG.GF2Type.Smith1979.W4As
