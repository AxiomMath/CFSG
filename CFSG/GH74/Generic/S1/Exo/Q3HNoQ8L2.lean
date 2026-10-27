module

public import CFSG.GH74.Filter.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Generic.S1.Exo

open Matrix CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd

namespace NoQ8L2

variable {K : Type} [Field K]

theorem ch2 (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem inv_val_of_det_one (g : GL (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K).trace • (1 : Matrix (Fin 2) (Fin 2) K) - g := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ch2, hg]
  simp

theorem trace_inv_of_det_one (g : GL (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      (g : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [inv_val_of_det_one g hg, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp
  ring

theorem trace_conj (J I : GL (Fin 2) K) :
    ((J * I * J⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      (I : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [Units.val_mul, Matrix.trace_mul_comm, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem scalar_val (u : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem exists_scalar_of_sq_eq_one (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K)
    (hA : (A : Matrix (Fin 2) (Fin 2) K).det = 1) (hsq : A * A = 1) :
    ∃ u : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  have h := ch2 (A : Matrix (Fin 2) (Fin 2) K)
  have hAA : (A : Matrix (Fin 2) (Fin 2) K) * A = 1 := by
    rw [← Units.val_mul, hsq, Units.val_one]
  rw [hAA, hA, one_smul] at h
  have h' : (A : Matrix (Fin 2) (Fin 2) K).trace • (A : Matrix (Fin 2) (Fin 2) K) =
      (2 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [two_smul]
    exact sub_eq_iff_eq_add.mp h.symm
  have ht : (A : Matrix (Fin 2) (Fin 2) K).trace ≠ 0 := by
    intro ht0
    rw [ht0, zero_smul] at h'
    exact h2 (by simpa using (congrFun (congrFun h' 0) 0).symm)
  refine ⟨Units.mk0 (2 / (A : Matrix (Fin 2) (Fin 2) K).trace) (div_ne_zero h2 ht), ?_⟩
  apply Units.ext
  rw [scalar_val]
  have := congrArg (fun M => ((A : Matrix (Fin 2) (Fin 2) K).trace)⁻¹ • M) h'
  simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  rw [Units.val_mk0, div_eq_inv_mul]
  exact this

theorem no_quaternion_pair_gl (h2 : (2 : K) ≠ 0) (I J : GL (Fin 2) K)
    (hI : (I : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hns : ∀ c : Kˣ, I * I ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (c : Kˣ) (h1 : J * I * J⁻¹ = I⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (c' : Kˣ) (h3 : J * J = (I * I) * Matrix.GeneralLinearGroup.scalar (Fin 2) c') : False := by
  have hc : c = 1 := by
    by_contra hc1
    have htr := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).trace) h1
    rw [trace_conj, Units.val_mul, scalar_val, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, trace_inv_of_det_one I hI, smul_eq_mul] at htr
    have ht0 : (I : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
      have hmul : (1 - (c : K)) * (I : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
        linear_combination htr
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd (Units.ext (by rw [Units.val_one]; linear_combination -h)) hc1
      · exact h
    refine hns (-1) (Units.ext ?_)
    have hch := ch2 (I : Matrix (Fin 2) (Fin 2) K)
    rw [ht0, hI, zero_smul, one_smul, zero_sub, ← Units.val_mul] at hch
    rw [hch, scalar_val]
    simp
  subst hc
  simp only [map_one, mul_one] at h1
  have hconj : J * (I * I) * J⁻¹ = I⁻¹ * I⁻¹ := by
    rw [← h1]
    group
  have hs : ∀ g : GL (Fin 2) K, Matrix.GeneralLinearGroup.scalar (Fin 2) c' * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin 2) c' := fun g =>
    Matrix.GeneralLinearGroup.scalar_commute c' g
  have hcen : ∀ X : GL (Fin 2) K, J * (X * Matrix.GeneralLinearGroup.scalar (Fin 2) c') * J⁻¹ =
      J * X * J⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c' := by
    intro X
    calc J * (X * Matrix.GeneralLinearGroup.scalar (Fin 2) c') * J⁻¹
        = J * X * (Matrix.GeneralLinearGroup.scalar (Fin 2) c' * J⁻¹) := by group
      _ = J * X * (J⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c') := by rw [hs J⁻¹]
      _ = J * X * J⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c' := by group
  have h4 : I⁻¹ * I⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c' =
      I * I * Matrix.GeneralLinearGroup.scalar (Fin 2) c' := by
    have e1 : J * (J * J) * J⁻¹ = J * J := by group
    rw [h3] at e1
    calc I⁻¹ * I⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c'
        = J * (I * I) * J⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c' := by rw [hconj]
      _ = J * (I * I * Matrix.GeneralLinearGroup.scalar (Fin 2) c') * J⁻¹ := (hcen (I * I)).symm
      _ = I * I * Matrix.GeneralLinearGroup.scalar (Fin 2) c' := e1
  have h5 : I⁻¹ * I⁻¹ = I * I := mul_right_cancel h4
  have hA : (I * I) * (I * I) = 1 := by
    calc (I * I) * (I * I) = (I * I) * (I⁻¹ * I⁻¹) := by rw [h5]
      _ = 1 := by group
  obtain ⟨u, hu⟩ := exists_scalar_of_sq_eq_one h2 (I * I)
    (by rw [Units.val_mul, Matrix.det_mul, hI, one_mul]) hA
  exact hns u hu

theorem mem_statedSL_iff {n : ℕ} {g : GL (Fin n) K} :
    g ∈ StatedSL n K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem eq_mul_scalar_of_mk_eq {x y : ↥(StatedSL 2 K)}
    (h : (QuotientGroup.mk x : StatedProj (StatedSL 2 K)) = QuotientGroup.mk y) :
    ∃ c : Kˣ, (x : GL (Fin 2) K) = y * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have h1 := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c⁻¹, ?_⟩
  rw [map_inv, hc]
  simp

theorem mk_eq_one_of_scalar {x : ↥(StatedSL 2 K)} (c : Kˣ)
    (hx : (x : GL (Fin 2) K) = Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
    (QuotientGroup.mk x : StatedProj (StatedSL 2 K)) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  exact ⟨c, hx.symm⟩

theorem two_ne_zero_of_card [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : (2 : K) ≠ 0 := by
  intro h0
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h0
  have : Fintype K := Fintype.ofFinite K
  have h1 := FiniteField.even_card_of_char_two (ringChar.eq K 2)
  rw [← Nat.card_eq_fintype_card, hK] at h1
  exact hp2 (hp.even_iff.mp (Nat.even_pow.mp (Nat.even_iff.mpr h1)).1)

end NoQ8L2

open NoQ8L2 in
theorem no_q8_of_statedProj_sl2 {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    (ψ : Q8 →* StatedProj (StatedSL 2 K)) (hψ : Function.Injective ψ) : False := by
  obtain ⟨I, hI⟩ := QuotientGroup.mk_surjective (ψ (QuaternionGroup.a 1))
  obtain ⟨J, hJ⟩ := QuotientGroup.mk_surjective (ψ (QuaternionGroup.xa 0))
  have hz : ψ (QuaternionGroup.a 2) ≠ 1 := fun h =>
    (by decide : (QuaternionGroup.a 2 : Q8) ≠ 1) (hψ (h.trans (map_one ψ).symm))
  have hii : (QuaternionGroup.a 1 : Q8) * QuaternionGroup.a 1 = QuaternionGroup.a 2 := by decide
  have hjj : (QuaternionGroup.xa 0 : Q8) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 := by decide
  have hji : (QuaternionGroup.xa 0 : Q8) * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
      (QuaternionGroup.a 1)⁻¹ := by decide
  have hII : (QuotientGroup.mk (I * I) : StatedProj (StatedSL 2 K)) =
      ψ (QuaternionGroup.a 2) := by
    rw [QuotientGroup.mk_mul, hI, ← map_mul, hii]
  have hJJ : (QuotientGroup.mk (J * J) : StatedProj (StatedSL 2 K)) =
      QuotientGroup.mk (I * I) := by
    rw [hII, QuotientGroup.mk_mul, hJ, ← map_mul, hjj]
  have hJI : (QuotientGroup.mk (J * I * J⁻¹) : StatedProj (StatedSL 2 K)) =
      QuotientGroup.mk I⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hI, hJ, ← map_inv, ← map_mul, ← map_mul, hji, map_inv]
  obtain ⟨c, hc⟩ := eq_mul_scalar_of_mk_eq hJI
  obtain ⟨c', hc'⟩ := eq_mul_scalar_of_mk_eq hJJ
  refine no_quaternion_pair_gl h2 (I : GL (Fin 2) K) (J : GL (Fin 2) K)
    (mem_statedSL_iff.mp I.2) ?_ c ?_ c' ?_
  · intro u hu
    exact hz (hII ▸ mk_eq_one_of_scalar u (by simpa using hu))
  · simpa using hc
  · simpa using hc'

theorem no_q8_of_psl2_model {S : Type} [Group S] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 p f)
    (ψ : CFSG.GH74.Filter.ClassicalOdd.Q8 →* S) (hψ : Function.Injective ψ) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact no_q8_of_statedProj_sl2 (NoQ8L2.two_ne_zero_of_card hp hp2 hK)
    (e.toMonoidHom.comp ψ) (e.injective.comp hψ)

end CFSG.GH74.Generic.S1.Exo
