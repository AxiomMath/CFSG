module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open scoped MatrixGroups

@[expose] def borelGL3 (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular}
  one_mem' := by
    intro i j hij
    rw [GeneralLinearGroup.coe_one, Matrix.one_apply]
    exact if_neg (ne_of_gt hij)
  mul_mem' := by
    intro A B hA hB
    show (((A * B : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular
    have hA' : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := hA
    have hB' : (B : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := hB
    rw [show (((A * B : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) from
      GeneralLinearGroup.coe_mul A B]
    exact Matrix.BlockTriangular.mul hA' hB'
  inv_mem' := by
    intro A hA
    show (((A⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular
    rw [GeneralLinearGroup.coe_inv]
    haveI := A.invertible
    have hA' : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := hA
    exact Matrix.blockTriangular_inv_of_blockTriangular hA'

variable {K : Type} [Field K]

theorem mem_borelGL3 {g : GL (Fin 3) K} :
    g ∈ borelGL3 K ↔ (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
  Iff.rfl

theorem diag_ne_zero_of_mem_borelGL3 {A : GL (Fin 3) K} (hA : A ∈ borelGL3 K) (i : Fin 3) :
    ((A : Matrix (Fin 3) (Fin 3) K)) i i ≠ 0 := by
  rw [mem_borelGL3] at hA
  intro hi
  have hdet : ((A : Matrix (Fin 3) (Fin 3) K)).det = 0 := by
    rw [Matrix.det_of_isUpperTriangular hA]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  exact GeneralLinearGroup.det_ne_zero A hdet

@[expose] def borelGL3.diag : borelGL3 K →* (Fin 3 → Kˣ) where
  toFun A := fun i =>
    Units.mk0 ((((A : borelGL3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i)
      (diag_ne_zero_of_mem_borelGL3 A.2 i)
  map_one' := by
    funext i
    apply Units.ext
    simp
  map_mul' A B := by
    funext i
    apply Units.ext
    have hA' : (((A : borelGL3 K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := A.2
    have hB' : (((B : borelGL3 K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := B.2
    have hmul := mul_apply_self_of_isUpperTriangular hA' hB' i
    simpa only [Units.val_mk0, Pi.mul_apply, Units.val_mul,
      show ((((A * B : borelGL3 K) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        (((A : borelGL3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((B : borelGL3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) from
        GeneralLinearGroup.coe_mul _ _] using hmul

theorem borelGL3.ker_diag :
    (borelGL3.diag (K := K)).ker =
      (unitriangularGL 3 K).subgroupOf (borelGL3 K) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    rw [mem_unitriangularGL]
    refine ⟨A.2, fun i => ?_⟩
    have hi := congrFun h i
    have hval := congrArg Units.val hi
    simpa [borelGL3.diag, Units.val_mk0] using hval
  · intro h
    funext i
    apply Units.ext
    simp only [Units.val_mk0, Pi.one_apply]
    exact (mem_unitriangularGL.mp h).2 i

theorem normal_unitriangularGL_subgroupOf :
    ((unitriangularGL 3 K).subgroupOf (borelGL3 K)).Normal := by
  rw [← borelGL3.ker_diag]
  exact MonoidHom.normal_ker _

@[expose] def utGL3 (a b c : K) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, a, c; 0, 1, b; 0, 0, 1] (by
    simp [Matrix.det_fin_three])

theorem coe_utGL3 (a b c : K) :
    ((utGL3 a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, a, c; 0, 1, b; 0, 0, 1] :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem utGL3_mem_unitriangularGL (a b c : K) :
    utGL3 a b c ∈ unitriangularGL 3 K := by
  rw [mem_unitriangularGL, coe_utGL3]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> simp

theorem eq_utGL3_of_mem_unitriangularGL {A : GL (Fin 3) K}
    (hA : A ∈ unitriangularGL 3 K) :
    A = utGL3 (((A : Matrix (Fin 3) (Fin 3) K)) 0 1)
      (((A : Matrix (Fin 3) (Fin 3) K)) 1 2)
      (((A : Matrix (Fin 3) (Fin 3) K)) 0 2) := by
  rw [mem_unitriangularGL] at hA
  obtain ⟨hup, hdiag⟩ := hA
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [coe_utGL3]
  fin_cases i <;> fin_cases j <;> simp [coe_utGL3]
  all_goals first | exact hup (by decide) | exact hdiag _ | rfl

@[expose] def unitriangularGL3Equiv : unitriangularGL 3 K ≃ (K × K × K) where
  toFun A := (((A : unitriangularGL 3 K) : GL (Fin 3) K) 0 1,
    ((A : unitriangularGL 3 K) : GL (Fin 3) K) 1 2,
    ((A : unitriangularGL 3 K) : GL (Fin 3) K) 0 2)
  invFun v := ⟨utGL3 v.1 v.2.1 v.2.2, utGL3_mem_unitriangularGL _ _ _⟩
  left_inv A := by
    refine Subtype.ext ?_
    exact (eq_utGL3_of_mem_unitriangularGL A.2).symm
  right_inv v := by
    obtain ⟨a, b, c⟩ := v
    simp [coe_utGL3]

theorem isPGroup_unitriangularGL_three [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] :
    IsPGroup p (unitriangularGL 3 K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hk
  have hcard : Nat.card (unitriangularGL 3 K) = p ^ ((k : ℕ) * 3) := by
    rw [Nat.card_congr (unitriangularGL3Equiv (K := K))]
    rw [Nat.card_prod, Nat.card_prod, hk, ← pow_add, ← pow_add]
    congr 1
    ring
  exact IsPGroup.of_card hcard

theorem dvd_card_sub_one_of_isPGroup_le_borel_of_ne_bot [Finite K] {d p : ℕ}
    [Fact p.Prime] [CharP K p] (hd : d.Prime) (hdp : d ≠ p)
    {D : Subgroup (GL (Fin 3) K)} (hD : IsPGroup d D) (hDB : D ≤ borelGL3 K)
    (hDne : D ≠ ⊥) : d ∣ Nat.card K - 1 := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  have hU : IsPGroup p (unitriangularGL 3 K) := isPGroup_unitriangularGL_three
  have hinf : D ⊓ unitriangularGL 3 K = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne d p hdp D (unitriangularGL 3 K) hD hU)
  have hnorm : ((unitriangularGL 3 K).subgroupOf (borelGL3 K)).Normal :=
    normal_unitriangularGL_subgroupOf
  letI : ((unitriangularGL 3 K).subgroupOf (borelGL3 K)).Normal := hnorm
  let f : D →* (borelGL3 K ⧸ (unitriangularGL 3 K).subgroupOf (borelGL3 K)) :=
    (QuotientGroup.mk' ((unitriangularGL 3 K).subgroupOf (borelGL3 K))).comp
      (Subgroup.inclusion hDB)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (Subgroup.inclusion hDB x : ↥(borelGL3 K)) ∈
        (unitriangularGL 3 K).subgroupOf (borelGL3 K) :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_subgroupOf] at hx'
    have hm : x.1 ∈ D ⊓ unitriangularGL 3 K := ⟨x.2, hx'⟩
    rw [hinf] at hm
    exact Subtype.ext (Subgroup.mem_bot.mp hm)
  have hdvd_quot : Nat.card D ∣
      Nat.card (borelGL3 K ⧸ (unitriangularGL 3 K).subgroupOf (borelGL3 K)) :=
    Subgroup.card_dvd_of_injective f hf
  have hiso : (borelGL3 K ⧸ (unitriangularGL 3 K).subgroupOf (borelGL3 K)) ≃*
      (borelGL3.diag (K := K)).range :=
    (QuotientGroup.quotientMulEquivOfEq (borelGL3.ker_diag (K := K)).symm).trans
      (QuotientGroup.quotientKerEquivRange (borelGL3.diag (K := K)))
  have hcard : Nat.card (borelGL3 K ⧸ (unitriangularGL 3 K).subgroupOf (borelGL3 K)) =
      Nat.card (borelGL3.diag (K := K)).range :=
    Nat.card_congr hiso.toEquiv
  have hrange_dvd : Nat.card (borelGL3.diag (K := K)).range ∣ (Nat.card K - 1) ^ 3 := by
    have h := Subgroup.card_subgroup_dvd_card (borelGL3.diag (K := K)).range
    rw [Nat.card_fun, Nat.card_units, Nat.card_fin] at h
    exact h
  have hquot_dvd : Nat.card
      (borelGL3 K ⧸ (unitriangularGL 3 K).subgroupOf (borelGL3 K)) ∣
      (Nat.card K - 1) ^ 3 := by
    rw [hcard]
    exact hrange_dvd
  have hdvdD : d ∣ Nat.card D := by
    rcases hD.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hDne
    · exact h
  exact hd.dvd_of_dvd_pow (hdvdD.trans (hdvd_quot.trans hquot_dvd))

end CFSG.LocalAnalysis.AGL81I.Section3

end
