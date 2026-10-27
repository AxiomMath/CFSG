module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem NFrame.permOrth_conj_signChange {c : ZMod 3} (fr : NFrame Q ι c) (σ : Equiv.Perm ι)
    (J : Finset ι) :
    fr.permOrth σ * fr.signChange J * (fr.permOrth σ)⁻¹ =
      fr.signChange (J.map σ.toEmbedding) := by
  rw [fr.permOrth_mul_signChange σ J, mul_assoc, mul_inv_cancel, mul_one]

theorem NFrame.permOrth_comm_signChange {c : ZMod 3} (fr : NFrame Q ι c) {σ : Equiv.Perm ι}
    {J : Finset ι} (h : J.map σ.toEmbedding = J) :
    fr.permOrth σ * fr.signChange J = fr.signChange J * fr.permOrth σ := by
  rw [fr.permOrth_mul_signChange σ J, h]

theorem NFrame.signChange_univ {c : ZMod 3} (fr : NFrame Q ι c) :
    fr.signChange Finset.univ = piOrth Q := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [fr.signChange_basis Finset.univ i, if_pos (Finset.mem_univ i)]
  exact (coe_piOrth_apply (Q := Q) (fr.b i)).symm

theorem NFrame.signChange_mem_twoRes {c : ZMod 3} (fr : NFrame Q ι c)
    {H : Subgroup (OGroup Q)} {σ : Equiv.Perm ι} (hσ3 : σ ^ 3 = 1) {J : Finset ι}
    (hp : fr.permOrth σ ∈ H) (ht : fr.signChange J ∈ H)
    (hJ : symmDiff J (J.map σ.toEmbedding) = (J.map σ.toEmbedding).map σ.toEmbedding) :
    fr.signChange J ∈ twoRes H := by
  have hp3 : (fr.permOrth σ) ^ 3 = 1 := by
    rw [pow_three, ← fr.permOrth_mul, ← fr.permOrth_mul, ← pow_three, hσ3, fr.permOrth_one]
  have hodd : Odd (orderOf (fr.permOrth σ)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hp3)
  have h1 : fr.permOrth σ * fr.signChange J * (fr.permOrth σ)⁻¹ =
      fr.signChange (J.map σ.toEmbedding) := fr.permOrth_conj_signChange σ J
  have h2 : fr.permOrth σ * fr.permOrth σ * fr.signChange J * (fr.permOrth σ)⁻¹ *
      (fr.permOrth σ)⁻¹ =
      fr.signChange ((J.map σ.toEmbedding).map σ.toEmbedding) := by
    calc fr.permOrth σ * fr.permOrth σ * fr.signChange J * (fr.permOrth σ)⁻¹ *
          (fr.permOrth σ)⁻¹
        = fr.permOrth σ * (fr.permOrth σ * fr.signChange J * (fr.permOrth σ)⁻¹) *
          (fr.permOrth σ)⁻¹ := by group
      _ = _ := by rw [h1, fr.permOrth_conj_signChange]
  have h3 : fr.signChange J * (fr.permOrth σ * fr.signChange J * (fr.permOrth σ)⁻¹) =
      fr.signChange (symmDiff J (J.map σ.toEmbedding)) := by
    rw [h1, fr.signChange_mul]
  exact t5c_mem_twoRes_of_three_cycle ht hp hodd (fr.signChange_mul_self J)
    (by rw [h3, h2, hJ])

end CFSG.OddStandard.SmallF3.Omega
