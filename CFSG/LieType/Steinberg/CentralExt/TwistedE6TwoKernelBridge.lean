module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCoverDescent
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.GroupTheory.OrderThreeActionTwoGroup
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Schreier.J4SThree

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

public section

open CFSG.RankThree.PerfectCover CFSG.LieType.Chevalley.C2E6Std CFSG.StandardType
open CFSG.EvenSmallLie.TwoE6

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

theorem hopfLift_equivariant {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]
    (ψ : H →* ↥stdGroup) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker ≤ Subgroup.center H)
    (σ : MulAut H) (δ : MulAut ↥stdGroup)
    (hσ : ∀ x, ψ (σ x) = δ (ψ x)) :
    σ.toMonoidHom.comp (hopfLift ψ hψ hψker) =
      (hopfLift ψ hψ hψker).comp (hopfCoverAut δ).toMonoidHom := by
  classical
  let π : HopfCover ↥stdGroup →* H := hopfLift ψ hψ hψker
  have hcomp : ψ.comp π = hopfCoverMap ↥stdGroup := by
    simpa [π] using comp_hopfLift ψ hψ hψker
  apply hopfCover_hom_ext_of_comp_eq ψ hψker (σ.toMonoidHom.comp π)
    (π.comp (hopfCoverAut δ).toMonoidHom)
  apply MonoidHom.ext
  intro u
  change ψ (σ (π u)) = ψ (π ((hopfCoverAut δ) u))
  rw [hσ (π u), ← MonoidHom.comp_apply, hcomp]
  rw [← MonoidHom.comp_apply, hcomp]
  exact (DFunLike.congr_fun (hopfCoverMap_hopfCoverAut δ) u).symm

theorem fixed_two_element_of_hopf_lift_cube
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]
    (ψ : H →* ↥stdGroup) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker ≤ Subgroup.center H)
    (σ : MulAut H) (δ : MulAut ↥stdGroup) (hδ3 : δ ^ 3 = 1)
    (hσ : ∀ x, ψ (σ x) = δ (ψ x))
    (hfree : ∀ z ∈ hopfMultiplier ↥stdGroup,
      (∃ k : ℕ, z ^ (2 ^ k) = 1) → hopfCoverAut δ z = z → z = 1)
    {z : H} (hzker : z ∈ ψ.ker) (hz2 : ∃ k : ℕ, z ^ (2 ^ k) = 1) (hzfix : σ z = z) :
    z = 1 := by
  classical
  let π : HopfCover ↥stdGroup →* H := hopfLift ψ hψ hψker
  let α : MulAut (HopfCover ↥stdGroup) := hopfCoverAut δ
  have hπ : Function.Surjective π := hopfLift_surjective ψ hψ hψker
  have hcomp : ψ.comp π = hopfCoverMap ↥stdGroup := comp_hopfLift ψ hψ hψker
  have heq := hopfLift_equivariant ψ hψ hψker σ δ hσ
  have hσπ : ∀ x, σ (π x) = π (α x) := fun x => DFunLike.congr_fun heq x
  obtain ⟨w, hw⟩ := hπ z
  have hwM : w ∈ hopfMultiplier ↥stdGroup := by
    rw [MonoidHom.mem_ker]
    rw [← DFunLike.congr_fun hcomp w, MonoidHom.comp_apply, hw]
    exact MonoidHom.mem_ker.mp hzker
  have hw6 : w ^ 6 = 1 := hopfMultiplier_bound.1 w hwM
  let u : HopfCover ↥stdGroup := w ^ 3
  have huM : u ∈ hopfMultiplier ↥stdGroup := (hopfMultiplier ↥stdGroup).pow_mem hwM 3
  have hu2 : u ^ 2 = 1 := by
    change (w ^ 3) ^ 2 = 1
    rw [← pow_mul]
    exact hw6
  have hπu : π u = z ^ 3 := by
    change π (w ^ 3) = z ^ 3
    rw [map_pow, hw]
  have hαuM : α u ∈ hopfMultiplier ↥stdGroup := hopfCoverAut_mem_hopfMultiplier δ huM
  have hααuM : α (α u) ∈ hopfMultiplier ↥stdGroup :=
    hopfCoverAut_mem_hopfMultiplier δ hαuM
  have hα3u : α (α (α u)) = u := by
    have h := DFunLike.congr_fun (hopfCoverAut_pow_three δ hδ3) u
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
  let v : HopfCover ↥stdGroup := u * α u * α (α u)
  have hvM : v ∈ hopfMultiplier ↥stdGroup :=
    (hopfMultiplier ↥stdGroup).mul_mem
      ((hopfMultiplier ↥stdGroup).mul_mem huM hαuM) hααuM
  have hcomm : ∀ x ∈ hopfMultiplier ↥stdGroup, ∀ y : HopfCover ↥stdGroup,
      Commute x y := fun x hx y =>
    (Subgroup.mem_center_iff.mp (hopfMultiplier_le_center hx) y).symm
  have hv2 : v ^ 2 = 1 := by
    change (u * α u * α (α u)) ^ 2 = 1
    rw [(hcomm _ ((hopfMultiplier ↥stdGroup).mul_mem huM hαuM) _).mul_pow,
      (hcomm u huM _).mul_pow, ← map_pow, ← map_pow, ← map_pow, hu2]
    simp only [map_one, one_mul]
  have hvfix : α v = v := by
    change α (u * α u * α (α u)) = u * α u * α (α u)
    rw [map_mul, map_mul, hα3u]
    calc
      α u * α (α u) * u = u * (α u * α (α u)) := (hcomm u huM _).eq.symm
      _ = u * α u * α (α u) := by group
  have hπv : π v = z ^ 9 := by
    change π (u * α u * α (α u)) = z ^ 9
    simp only [map_mul, ← hσπ, hπu, map_pow, hzfix]
    group
  have hv1 : v = 1 := hfree v hvM ⟨1, by simpa using hv2⟩ hvfix
  have hz9 : z ^ 9 = 1 := by rw [← hπv, hv1, map_one]
  obtain ⟨k, hk⟩ := hz2
  have hcop : Nat.Coprime 9 (2 ^ k) :=
    (by norm_num : Nat.Coprime 9 2).pow_right k
  have hdvd : orderOf z ∣ Nat.gcd 9 (2 ^ k) :=
    Nat.dvd_gcd ((orderOf_dvd_iff_pow_eq_one).mpr hz9)
      ((orderOf_dvd_iff_pow_eq_one).mpr hk)
  rw [hcop.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
