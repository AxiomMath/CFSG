module

public import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.S5Odd
public import CFSG.LargeExtraspecial.S12Basic
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup CFSG.LargeExtraspecial CFSG.GF2Type.Aschbacher1976Full

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_dvd_three {g : G} (H : S4.Hyp4 S g) (Cn : S4.Cons311 S g) (hw : S.width = 4)
    {X : Subgroup S.O} (hXM : X ≤ S.Mbar) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (hX81 : Nat.card X ∣ 3 ^ 4)
    (hfix : ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)) :
    Nat.card X ∣ 3 := by
  have hXN : X ≤ normalizer (S.Lbar g : Set S.O) := by
    intro x hx
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp (hXM hx)
    have hfix' : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      rw [hh]
      exact hfix x hx
    have hnorm := (S.timmesfeld_12_4_1 H.conj_mem H.conj_ne (by omega) h).mpr hfix'
    rw [hh] at hnorm
    exact hnorm
  have hL8 : Nat.card (S.Lbar g) = 8 := by
    rw [Cn.card_Lbar, hw]
    norm_num
  have hcomm : ∀ a b : S.Lbar g, a * b = b * a := fun a b =>
    Subtype.ext (S4.Lbar_comm S H.conj_mem a.2 b.2)
  have hsq : ∀ a : S.Lbar g, a * a = 1 := fun a =>
    Subtype.ext (S4.mul_self_of_mem_Lbar S H.conj_mem a.2)
  let ψ : X →* MulAut (S.Lbar g) :=
    (S.Lbar g).normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    have hconj : ∀ s ∈ S.Lbar g, s * (x : S.O) = (x : S.O) * s := by
      intro s hs
      have h1 := congrArg (fun φ : MulAut (S.Lbar g) => ((φ ⟨s, hs⟩ : S.Lbar g) : S.O)) hx1
      have h2 : (x : S.O) * s * (x : S.O)⁻¹ = s := h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    exact Subtype.ext
      (S5.eq_one_of_pow_eq_one_of_commute H (m := 3) ⟨1, by norm_num⟩ (hX3 (x : S.O) x.2) hconj)
  have h168 : Nat.card X ∣ 168 := by
    have h := Subgroup.card_dvd_of_injective ψ hψ
    rwa [HS.card_mulAut_eq_168 hL8 hcomm hsq] at h
  have h81 : Nat.card X ∣ 81 := by
    norm_num at hX81
    exact hX81
  have h3 := Nat.dvd_gcd h168 h81
  norm_num at h3
  exact h3

end CFSG.GF2Type.Smith1979.W4As
