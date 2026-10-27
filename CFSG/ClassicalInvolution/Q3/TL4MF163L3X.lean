module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

namespace MF163

section Action

variable {X : Type} [Group X] {N : Subgroup X} [N.Normal] {P : Type} [Group P]

theorem congr_conjNormal_of_mem (e : ↥N ≃* P) {n : X} (hn : n ∈ N) :
    MulAut.congr e (MulAut.conjNormal n) = MulAut.conj (e ⟨n, hn⟩) := by
  ext w
  obtain ⟨m, rfl⟩ := e.surjective w
  rw [show MulAut.congr e (MulAut.conjNormal n) (e m) = e (MulAut.conjNormal n m) by
    simp [MulAut.congr_apply], MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem mem_of_congr_mem_inner (hC : Subgroup.centralizer (N : Set X) = ⊥) (e : ↥N ≃* P) {y : X}
    (h : MulAut.congr e (MulAut.conjNormal y) ∈
      ComponentClassification.OuterAutomorphisms.inner P) : y ∈ N := by
  obtain ⟨m, hm⟩ := h
  have key : ∀ x : ↥N, (e.symm m : ↥N) * x * (e.symm m)⁻¹ = MulAut.conjNormal y x := by
    intro x
    apply e.injective
    have h1 := DFunLike.congr_fun hm (e x)
    rw [show MulAut.congr e (MulAut.conjNormal y) (e x) = e (MulAut.conjNormal y x) by
      simp [MulAut.congr_apply]] at h1
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
  have hcen : ((e.symm m : ↥N) : X)⁻¹ * y ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg Subtype.val (key ⟨x, hx⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
    calc x * (((e.symm m : ↥N) : X)⁻¹ * y) =
        ((e.symm m : ↥N) : X)⁻¹ * (((e.symm m : ↥N) : X) * x * ((e.symm m : ↥N) : X)⁻¹) * y := by
          group
      _ = ((e.symm m : ↥N) : X)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
      _ = ((e.symm m : ↥N) : X)⁻¹ * y * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
  rw [← hcen]
  exact (e.symm m).2

theorem congr_conjNormal_injective (hC : Subgroup.centralizer (N : Set X) = ⊥) (e : ↥N ≃* P) :
    Function.Injective ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← hC, Subgroup.mem_centralizer_iff]
  intro n hn
  have hx' : MulAut.congr e (MulAut.conjNormal x) = 1 := hx
  have h1 := DFunLike.congr_fun hx' (e ⟨n, hn⟩)
  rw [show MulAut.congr e (MulAut.conjNormal x) (e ⟨n, hn⟩) = e (MulAut.conjNormal x ⟨n, hn⟩) by
    simp [MulAut.congr_apply], MulAut.one_apply] at h1
  have h3 := congrArg Subtype.val (e.injective h1)
  rw [MulAut.conjNormal_apply] at h3
  calc n * x = (x * n * x⁻¹) * x := by rw [h3]
    _ = x * n := by group

theorem apply_eq_of_comm_conj (hZ : Subgroup.center P = ⊥) {b : MulAut P} {x : P}
    (h : b * MulAut.conj x = MulAut.conj x * b) : b x = x := by
  have h1 : ∀ w, b x * w * (b x)⁻¹ = x * w * x⁻¹ := by
    intro w
    have := DFunLike.congr_fun h (b.symm w)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this
    exact this
  have h2 : x⁻¹ * b x ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro w
    calc w * (x⁻¹ * b x) = x⁻¹ * (x * w * x⁻¹) * b x := by group
      _ = x⁻¹ * (b x * w * (b x)⁻¹) * b x := by rw [h1 w]
      _ = x⁻¹ * b x * w := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2.symm

omit [N.Normal] in
theorem center_eq_bot_of_equiv [IsSimpleGroup N] (hnab : ∃ a b : N, a * b ≠ b * a)
    (e : ↥N ≃* P) : Subgroup.center P = ⊥ := by
  have hZN : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ Subgroup.center N := Subgroup.mem_center_iff.mpr fun g => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (e g)
  rw [hZN, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply x, hx', map_one]

end Action

namespace L3

variable {K : Type} [Field K]

theorem exists_noncomm : ∃ a b : projectiveSL 3 K, a * b ≠ b * a := by
  let B₁ : GL (Fin 2) K :=
    GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp [Matrix.det_fin_two_of])
  let B₂ : GL (Fin 2) K :=
    GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by simp [Matrix.det_fin_two_of])
  refine ⟨proj 3 K (blkP 1 B₁), proj 3 K (blkP 1 B₂), fun h => ?_⟩
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, proj_eq_proj_iff, ← map_inv, ← map_mul] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  have hblk : Lemma41aL3.blk ((B₁ * B₂)⁻¹ * (B₂ * B₁)) = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, ← hc]
    show _ = ((1 * Lemma41aL3.blk _ * 1⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [one_mul, inv_one, mul_one]
  obtain ⟨-, hA⟩ := Q5GL2.blk_eq_scalar hblk
  have e := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
    (show B₂ * B₁ = B₁ * B₂ * GeneralLinearGroup.scalar (Fin 2) c by rw [← hA, mul_inv_cancel_left])
  have e01 := congrFun (congrFun e 0) 1
  have e11 := congrFun (congrFun e 1) 1
  simp [B₁, B₂, Matrix.mul_apply, Fin.sum_univ_two, GeneralLinearGroup.coe_scalar] at e01 e11
  have : (1 : K) = 0 := by linear_combination e11 - e01
  exact one_ne_zero this

end L3

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
