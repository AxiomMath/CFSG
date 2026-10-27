module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCTICommutingCenterWidth
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

namespace SteinbergBQ.HigherCenter

variable {P : Type*} [Group P]

theorem card_le_of_commute_extraspecial {K : Type*} [Group K] [Finite K]
    (hK : IsExtraspecialPGroup 2 K) {w : ℕ} (hw : Nat.card K = 2 ^ (1 + 2 * w)) {A : Subgroup K}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A ≤ 2 ^ (w + 1) := by
  classical
  let _ : Module (ZMod 2) (Additive (Abelianization K)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hK
  have : Module.Finite (ZMod 2) (Additive (Abelianization K)) := Module.Finite.of_finite
  set A' := A ⊔ center K with hA'def
  have hZA' : center K ≤ A' := le_sup_right
  have hA'c : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hx
    obtain ⟨b, hb, d, hd, rfl⟩ := mem_sup_of_normal_right.mp hy
    have h1 := mem_center_iff.mp hc
    have h2 := mem_center_iff.mp hd
    have hab : Commute a b := hA a ha b hb
    have hcb : Commute c b := (show Commute b c from h1 b).symm
    have hcd : Commute c d := (show Commute d c from h1 d).symm
    exact (hab.mul_right (h2 a)).mul_left (hcb.mul_right hcd)
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  have hS := ofMul_mem_img_iff hK hZA'
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  have hiso : img A' ≤ LinearMap.BilinForm.orthogonal (extraspecialQuadForm hK).polarBilin
      (img A') := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    obtain ⟨a, rfl⟩ := exists_ofMul_of u
    obtain ⟨a', rfl⟩ := exists_ofMul_of v
    show QuadraticMap.polar (extraspecialQuadForm hK) (Additive.ofMul (Abelianization.of a'))
      (Additive.ofMul (Abelianization.of a)) = 0
    rw [polar_extraspecialQuadForm_eq_zero_iff]
    exact hA'c _ ((hS a').mp hv) _ ((hS a).mp hu)
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := (extraspecialQuadForm hK).polarBilin) (img A')
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  rw [LinearMap.BilinForm.Nondegenerate.ker_eq_bot (extraspecialQuadForm_nondegenerate hK),
    inf_bot_eq, finrank_bot, add_zero, finrank_eq hK hw] at hdim
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  have hle := Submodule.finrank_mono hiso
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  have hcard := card_preim hK (img A')
  open CFSG.RankThree.Literature.FSmith TICommutingCenters InvolutionTrichotomy in
  rw [preim_img hK hZA'] at hcard
  calc Nat.card A ≤ Nat.card A' := card_le_of_le le_sup_left
    _ = _ := hcard
    _ ≤ 2 ^ w * 2 := Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 2 ^ (w + 1) := (pow_succ 2 w).symm

end SteinbergBQ.HigherCenter

end CFSG.LocalAnalysis.GorensteinLyons
