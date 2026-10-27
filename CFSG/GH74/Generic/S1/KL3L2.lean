module

public import CFSG.GH74.Generic.S1.KL3Cfg
public import CFSG.GH74.Generic.S1.KL3Heis
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.Assembly.GL83LieDefs

public section

open Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace CFSG.GH74.Generic.S1

namespace KL3L2

section Mat

variable {K : Type} [Field K]

@[expose] def mat (u : ↥(StatedSL 2 K)) : Matrix (Fin 2) (Fin 2) K := ((u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

theorem mat_mul (u v : ↥(StatedSL 2 K)) : mat (u * v) = mat u * mat v := rfl

theorem mat_one : mat (1 : ↥(StatedSL 2 K)) = 1 := rfl

theorem mat_inv_mul (u : ↥(StatedSL 2 K)) : mat u⁻¹ * mat u = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mem_statedSL_iff' (A : GL (Fin 2) K) :
    A ∈ StatedSL 2 K ↔ (A : Matrix (Fin 2) (Fin 2) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem det_mat (u : ↥(StatedSL 2 K)) : (mat u).det = 1 := (mem_statedSL_iff' _).1 u.2




theorem scalar_matrix_of_mem {A : GL (Fin 2) K} (h : A ∈ StatedScalars (Fin 2) K) :
    ∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨u, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem mem_scalars_of_matrix {A : GL (Fin 2) K} {c : K}
    (h : (A : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    A ∈ StatedScalars (Fin 2) K := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 : (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h, zero_smul, zero_mul] at h1
    have := congrFun (congrFun h1 0) 0
    simp at this
  refine ⟨Units.mk0 c hc, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem exists_scalar_of_commute (u v : ↥(StatedSL 2 K))
    (h : (QuotientGroup.mk u : StatedProj (StatedSL 2 K)) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk u) :
    ∃ c : K, mat v * mat u = c • (mat u * mat v) := by
  have h1 : (QuotientGroup.mk (u * v) : StatedProj (StatedSL 2 K)) = QuotientGroup.mk (v * u) := h
  have h2 := QuotientGroup.eq.1 h1
  rw [Subgroup.mem_subgroupOf] at h2
  obtain ⟨c, hc⟩ := scalar_matrix_of_mem h2
  refine ⟨c, ?_⟩
  have h3 : mat ((u * v)⁻¹ * (v * u)) = c • (1 : Matrix (Fin 2) (Fin 2) K) := hc
  calc mat v * mat u = mat (v * u) := (mat_mul v u).symm
    _ = mat (u * v) * mat ((u * v)⁻¹ * (v * u)) := by
        rw [← mat_mul, mul_inv_cancel_left]
    _ = c • (mat u * mat v) := by
        rw [h3, Matrix.mul_smul, Matrix.mul_one, mat_mul]




theorem commute_of_commute_nonscalar {K : Type} [Field K] {A B G : Matrix (Fin 2) (Fin 2) K}
    (hG : ∀ c : K, G ≠ c • 1) (hA : A * G = G * A) (hB : B * G = G * B) : A * B = B * A := by
  have hne : G 0 1 ≠ 0 ∨ G 1 0 ≠ 0 ∨ G 0 0 - G 1 1 ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply hG (G 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2]
    exact (sub_eq_zero.1 h3).symm
  have a1 := congrFun (congrFun hA 0) 0
  have a2 := congrFun (congrFun hA 0) 1
  have a3 := congrFun (congrFun hA 1) 0
  have b1 := congrFun (congrFun hB 0) 0
  have b2 := congrFun (congrFun hB 0) 1
  have b3 := congrFun (congrFun hB 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3 b1 b2 b3
  have key : A 0 1 * B 1 0 - B 0 1 * A 1 0 = 0 ∧
      B 0 1 * (A 0 0 - A 1 1) - A 0 1 * (B 0 0 - B 1 1) = 0 ∧
      A 1 0 * (B 0 0 - B 1 1) - B 1 0 * (A 0 0 - A 1 1) = 0 := by
    rcases hne with hu | hv | hw
    · have T2 : B 0 1 * (A 0 0 - A 1 1) - A 0 1 * (B 0 0 - B 1 1) = 0 := by
        apply mul_left_cancel₀ hu
        linear_combination (B 0 1) * a2 - (A 0 1) * b2
      have T1 : A 0 1 * B 1 0 - B 0 1 * A 1 0 = 0 := by
        apply mul_left_cancel₀ hu
        linear_combination (B 0 1) * a1 - (A 0 1) * b1
      refine ⟨T1, T2, ?_⟩
      apply mul_left_cancel₀ hu
      linear_combination (-(G 1 0)) * T2 - (B 0 0 - B 1 1) * a1 + (A 0 0 - A 1 1) * b1
    · have T1 : A 0 1 * B 1 0 - B 0 1 * A 1 0 = 0 := by
        apply mul_left_cancel₀ hv
        linear_combination (B 1 0) * a1 - (A 1 0) * b1
      have T2 : B 0 1 * (A 0 0 - A 1 1) - A 0 1 * (B 0 0 - B 1 1) = 0 := by
        apply mul_left_cancel₀ hv
        linear_combination (-(G 0 0 - G 1 1)) * T1 - (B 0 1) * a3 + (A 0 1) * b3
      refine ⟨T1, T2, ?_⟩
      apply mul_left_cancel₀ hv
      linear_combination (B 1 0) * a3 - (A 1 0) * b3
    · have T2 : B 0 1 * (A 0 0 - A 1 1) - A 0 1 * (B 0 0 - B 1 1) = 0 := by
        apply mul_left_cancel₀ hw
        linear_combination (B 0 0 - B 1 1) * a2 - (A 0 0 - A 1 1) * b2
      have T1 : A 0 1 * B 1 0 - B 0 1 * A 1 0 = 0 := by
        apply mul_left_cancel₀ hw
        linear_combination (-(G 1 0)) * T2 - (B 0 1) * a3 + (A 0 1) * b3
      refine ⟨T1, T2, ?_⟩
      apply mul_left_cancel₀ hw
      linear_combination (B 0 0 - B 1 1) * a3 - (A 0 0 - A 1 1) * b3
  obtain ⟨T1, T2, T3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination T1
  · linear_combination T2
  · linear_combination T3
  · linear_combination -T1


theorem mat_mul_inv (u : ↥(StatedSL 2 K)) : mat u * mat u⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem sq_eq_one_of_det {A B : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) (hB : B.det = 1) {c : K}
    (h : B * A = c • (A * B)) : c * c = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hA, hB] at h1
  simp only [Fintype.card_fin] at h1
  linear_combination -h1

theorem trace_eq_zero_of_anticomm (h2 : (2 : K) ≠ 0) (G A : ↥(StatedSL 2 K))
    (h : mat G * mat A = -(mat A * mat G)) : (mat A).trace = 0 := by
  have h1 : mat A = -(mat G⁻¹ * mat A * mat G) := by
    calc mat A = mat G⁻¹ * (mat G * mat A) := by
          rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
      _ = -(mat G⁻¹ * mat A * mat G) := by rw [h, Matrix.mul_neg, Matrix.mul_assoc]
  have h2' : (mat G⁻¹ * mat A * mat G).trace = (mat A).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mat_mul_inv, Matrix.one_mul]
  have h3 : (mat A).trace = -(mat A).trace := by
    calc (mat A).trace = (-(mat G⁻¹ * mat A * mat G)).trace := congrArg Matrix.trace h1
      _ = -(mat A).trace := by rw [Matrix.trace_neg, h2']
  have h4 : (2 : K) * (mat A).trace = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h4).resolve_left h2

theorem sq_of_trace_zero {A : Matrix (Fin 2) (Fin 2) K} (hd : A.det = 1) (ht : A.trace = 0) :
    A * A = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (A 0 0) * ht - hd
  · linear_combination (A 0 1) * ht
  · linear_combination (A 1 0) * ht
  · linear_combination (A 1 1) * ht - hd




theorem no_heis (h2 : (2 : K) ≠ 0) (x y : StatedProj (StatedSL 2 K))
    (hx : x * x = 1 → x = 1) (hy : y * y = 1 → y = 1)
    (hcx : ⁅x, y⁆ * x = x * ⁅x, y⁆) (hcy : ⁅x, y⁆ * y = y * ⁅x, y⁆) (hc : ⁅x, y⁆ ≠ 1) : False := by
  classical
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  set g : ↥(StatedSL 2 K) := ⁅a, b⁆ with hg
  have hπg : (⁅(QuotientGroup.mk a : StatedProj (StatedSL 2 K)),
      (QuotientGroup.mk b : StatedProj (StatedSL 2 K))⁆) = QuotientGroup.mk g := by
    rw [hg]
    exact (map_commutatorElement
      (QuotientGroup.mk' ((StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K))) a b).symm
  rw [hπg] at hcx hcy hc
  have hone : ∀ w : ↥(StatedSL 2 K), (mat w).det = 1 := det_mat
  have hsq : ∀ u : ↥(StatedSL 2 K), (mat u).trace = 0 →
      (QuotientGroup.mk u : StatedProj (StatedSL 2 K)) * QuotientGroup.mk u = 1 := by
    intro u hu
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    apply mem_scalars_of_matrix (c := -1)
    show mat (u * u) = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)
    rw [mat_mul]
    exact sq_of_trace_zero (hone u) hu
  have hgne : ∀ c : K, mat g ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro c hcg
    apply hc
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_scalars_of_matrix hcg
  have hcomm : ∀ u : ↥(StatedSL 2 K),
      (QuotientGroup.mk g : StatedProj (StatedSL 2 K)) * QuotientGroup.mk u =
        QuotientGroup.mk u * QuotientGroup.mk g →
      ((QuotientGroup.mk u : StatedProj (StatedSL 2 K)) *
        (QuotientGroup.mk u : StatedProj (StatedSL 2 K)) = 1 →
        (QuotientGroup.mk u : StatedProj (StatedSL 2 K)) = 1) →
      mat u * mat g = mat g * mat u ∨ (QuotientGroup.mk u : StatedProj (StatedSL 2 K)) = 1 := by
    intro u hu hz
    obtain ⟨c, hcu⟩ := exists_scalar_of_commute g u hu
    have hcc := sq_eq_one_of_det (hone g) (hone u) hcu
    rcases mul_self_eq_one_iff.1 hcc with h1 | h1
    · left
      rw [h1, one_smul] at hcu
      exact hcu
    · right
      rw [h1, neg_smul, one_smul] at hcu
      have hcu' : mat g * mat u = -(mat u * mat g) := by rw [hcu, neg_neg]
      exact hz (hsq u (trace_eq_zero_of_anticomm h2 g u hcu'))
  have hA := hcomm a hcx hx
  have hB := hcomm b hcy hy
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · have hab : mat a * mat b = mat b * mat a :=
        commute_of_commute_nonscalar hgne hA hB
      have : a * b = b * a := by
        apply Subtype.ext
        apply Units.ext
        exact hab
      apply hc
      rw [hg, commutatorElement_eq_one_iff_mul_comm.2 this]
      rfl
    · apply hc
      rw [← hπg, hB]
      exact commutatorElement_one_right _
  · apply hc
    rw [← hπg, hA]
    exact commutatorElement_one_left _

end Mat

end KL3L2

theorem kl3FamL2 : KL3FamL2 := by
  intro S _ _ _ p f hp hp2 hf hmodel F _ _ Pb yb hcfg
  obtain ⟨hF3, ⟨e⟩, -, -, -⟩ := hcfg
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hmodel
  have h2 : (2 : K) ≠ 0 :=
    Ring.two_ne_zero (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK)
  have h3 : (3 : F) = 0 := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF3] at h
    exact_mod_cast h
  let φ : SL(3, F) →* StatedProj (StatedSL 2 K) :=
    (eS.toMonoidHom.comp Pb.subtype).comp e.symm.toMonoidHom
  have hφ : Function.Injective φ :=
    eS.injective.comp (Subtype.val_injective.comp e.symm.injective)
  obtain ⟨x, y, hx3, hy3, hc, hcx, hcy⟩ := kl3_heis_of_hom h3 φ hφ
  have hodd : ∀ z : StatedProj (StatedSL 2 K), z ^ 3 = 1 → z * z = 1 → z = 1 := by
    intro z hz hzz
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz, hzz]; simp
  exact KL3L2.no_heis h2 x y (hodd x hx3) (hodd y hy3) hcx hcy hc

end CFSG.GH74.Generic.S1
