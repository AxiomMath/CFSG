module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCJ

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

section RankOne

variable (Q : QuadraticForm K (ι → K))

noncomputable abbrev polMat (a b : ι → K) : Matrix ι ι K := rankOneMat (Q.polarBilin.flip a) b

theorem polMat_mulVec (a b v : ι → K) : polMat Q a b *ᵥ v = Q.polarBilin v a • b := by
  rw [polMat, rankOneMat_mulVec, LinearMap.flip_apply]

theorem polMat_mul (a b c d : ι → K) :
    polMat Q a b * polMat Q c d = Q.polarBilin d a • polMat Q c b :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, polMat_mulVec, polMat_mulVec, smul_mulVec, polMat_mulVec, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm]

theorem polMat_smul_left (c : K) (a b : ι → K) : polMat Q (c • a) b = c • polMat Q a b :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [polMat_mulVec, smul_mulVec, polMat_mulVec, map_smul, smul_eq_mul, smul_smul]

theorem polMat_smul_right (c : K) (a b : ι → K) : polMat Q a (c • b) = c • polMat Q a b :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [polMat_mulVec, smul_mulVec, polMat_mulVec, smul_smul, smul_smul, mul_comm]

theorem mul_polMat (N : Matrix ι ι K) (a b : ι → K) : N * polMat Q a b = polMat Q a (N *ᵥ b) :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, polMat_mulVec, mulVec_smul, polMat_mulVec]

theorem polMat_mul_of_adj {N : Matrix ι ι K}
    (hN : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) (a b : ι → K) :
    polMat Q a b * N = polMat Q (N *ᵥ a) b :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, polMat_mulVec, polMat_mulVec, hN]

omit [DecidableEq ι] in
theorem rank_eq_two_of {X : Matrix ι ι K} {u w : ι → K}
    (hli : ∀ a b : K, a • u + b • w = 0 → a = 0 ∧ b = 0)
    (hle : ∀ v, ∃ a b : K, X *ᵥ v = a • u + b • w) (hu : ∃ v, X *ᵥ v = u)
    (hw : ∃ v, X *ᵥ v = w) : X.rank = 2 := by
  rw [Matrix.rank]
  have hR : LinearMap.range X.mulVecLin = Submodule.span K (Set.range ![u, w]) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨a, b, hab⟩ := hle v
      rw [Matrix.mulVecLin_apply, hab]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hu
      · exact hw
  rw [hR, finrank_span_eq_card (LinearIndependent.pair_iff.mpr hli), Fintype.card_fin]

theorem conj_polMat {D : GL ι K} (hD : ∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) (a b : ι → K) :
    ((D⁻¹ : GL ι K) : Matrix ι ι K) * polMat Q a b * D =
      polMat Q (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a) (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ b) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, polMat_mulVec, mulVec_smul, polMat_mulVec]
  congr 1
  conv_lhs => rw [show a = (D : Matrix ι ι K) *ᵥ (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a) by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]]
  exact polarBilin_mulVec_of_isometry Q hD v _

end RankOne

section Hyperbolic

variable {Q : QuadraticForm K (ι → K)} [CharP K 2] {z f : ι → K} (hzf : Q.polarBilin z f = 1)
  (hQz : Q z = 0) (hQf : Q f = 0)

noncomputable abbrev hypMat (Q : QuadraticForm K (ι → K)) (z f : ι → K) (α : K) :
    Matrix ι ι K :=
  1 + (α - 1) • polMat Q f z + (α⁻¹ - 1) • polMat Q z f

omit [CharP K 2] in
theorem hypMat_mulVec (α : K) (v : ι → K) : hypMat Q z f α *ᵥ v =
    v + ((α - 1) * Q.polarBilin v f) • z + ((α⁻¹ - 1) * Q.polarBilin v z) • f := by
  rw [hypMat, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, polMat_mulVec,
    polMat_mulVec, smul_smul, smul_smul]

include hzf in
theorem hypMat_mul_hypMat {α : K} (hα : α ≠ 0) : hypMat Q z f α * hypMat Q z f α⁻¹ = 1 := by
  have hfz : Q.polarBilin f z = 1 := by rw [polarBilin_comm]; exact hzf
  have hzz : Q.polarBilin z z = 0 := by rw [polarBilin_apply_apply]; exact polar_self_eq_zero Q z
  have hff : Q.polarBilin f f = 0 := by rw [polarBilin_apply_apply]; exact polar_self_eq_zero Q f
  refine one_add_two_smul_mul ?_ ?_ ?_ ?_ ?_ ?_
  · rw [polMat_mul, hzf, one_smul]
  · rw [polMat_mul, hfz, one_smul]
  · rw [polMat_mul, hff, zero_smul]
  · rw [polMat_mul, hzz, zero_smul]
  · field_simp
    ring
  · rw [inv_inv]
    field_simp
    ring

@[expose] noncomputable def hypGL (hzf : Q.polarBilin z f = 1) {α : K} (hα : α ≠ 0) : GL ι K where
  val := hypMat Q z f α
  inv := hypMat Q z f α⁻¹
  val_inv := hypMat_mul_hypMat hzf hα
  inv_val := by
    have h := hypMat_mul_hypMat (Q := Q) hzf (inv_ne_zero hα)
    rwa [inv_inv] at h

theorem coe_hypGL {α : K} (hα : α ≠ 0) : (hypGL hzf hα : Matrix ι ι K) = hypMat Q z f α := rfl

theorem coe_hypGL_inv {α : K} (hα : α ≠ 0) :
    ((hypGL hzf hα)⁻¹ : GL ι K) = (hypMat Q z f α⁻¹ : Matrix ι ι K) := rfl

omit [CharP K 2] in
include hzf hQz hQf in
theorem hypMat_isometry {α : K} (hα : α ≠ 0) (v : ι → K) :
    Q (hypMat Q z f α *ᵥ v) = Q v := by
  rw [hypMat_mulVec, quad_add, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQz,
    hQf, smul_zero, smul_zero, add_zero, add_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hzf]
  field_simp
  ring

include hzf in
theorem hypGL_even_commRank {α : K} (hα : α ≠ 0) : Even (commRank (hypGL hzf hα)) := by
  rw [commRank, coe_hypGL, hypMat, add_assoc, add_sub_cancel_left]
  by_cases h1 : α = 1
  · subst h1
    simp
  have hzz : Q.polarBilin z z = 0 := by rw [polarBilin_apply_apply]; exact polar_self_eq_zero Q z
  have hfz : Q.polarBilin f z = 1 := by rw [polarBilin_comm]; exact hzf
  have hff : Q.polarBilin f f = 0 := by rw [polarBilin_apply_apply]; exact polar_self_eq_zero Q f
  have ha : α - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : α⁻¹ - 1 ≠ 0 := fun h => h1 (inv_eq_one.mp (sub_eq_zero.mp h))
  have hX : ∀ v, ((α - 1) • polMat Q f z + (α⁻¹ - 1) • polMat Q z f) *ᵥ v =
      ((α - 1) * Q.polarBilin v f) • z + ((α⁻¹ - 1) * Q.polarBilin v z) • f := fun v => by
    rw [add_mulVec, smul_mulVec, smul_mulVec, polMat_mulVec, polMat_mulVec, smul_smul, smul_smul]
  refine ⟨1, rank_eq_two_of (fun a b h => ?_) (fun v => ⟨_, _, hX v⟩) ⟨(α - 1)⁻¹ • z, ?_⟩
    ⟨(α⁻¹ - 1)⁻¹ • f, ?_⟩⟩
  · have h1 := congrArg (Q.polarBilin z) h
    have h2 := congrArg (Q.polarBilin f) h
    simp only [map_add, map_smul, smul_eq_mul, map_zero, hzz, hzf, hfz, hff, mul_zero,
      mul_one, zero_add, add_zero] at h1 h2
    exact ⟨h2, h1⟩
  · rw [hX]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hzf, hzz, mul_zero, zero_smul,
      add_zero, mul_one, mul_inv_cancel₀ ha, one_smul]
  · rw [hX]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hff, hfz, mul_zero, zero_smul,
      zero_add, mul_one, mul_inv_cancel₀ hb, one_smul]

end Hyperbolic

section Data

variable {Q : QuadraticForm K (ι → K)} [Finite K] [CharP K 2]

structure TypeCData (Q : QuadraticForm K (ι → K)) (N : Matrix ι ι K) (z z' y' : ι → K) :
    Prop where
  sq : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)
  mulVec_z : N *ᵥ z = 0
  mulVec_z' : N *ᵥ z' = z
  quad_z : Q z = 0
  pol_y'z : Q.polarBilin y' z = 1

theorem exists_typeCData (hQ : Q.polarBilin.Nondegenerate) {M : GL ι K}
    (hM : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hM2 : orderOf M = 2)
    (hev : Even (commRank M)) (hc : ∃ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) ≠ 0) :
    ∃ z z' y', TypeCData Q ((M : Matrix ι ι K) - 1) z z' y' := by
  set N := (M : Matrix ι ι K) - 1 with hNdef
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hiso : ∀ v, Q (v + N *ᵥ v) = Q v := fun v => by
    have h1 : v + N *ᵥ v = (M : Matrix ι ι K) *ᵥ v := by rw [hMN, add_mulVec, one_mulVec]
    rw [h1]
    exact hM v
  have hN : N * N = 0 := sub_one_mul_self_eq_zero hM2
  obtain ⟨z, hz⟩ := exists_sqrt_vector Q hQ hN hiso
  obtain ⟨z', hz'⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hc
    apply hv
    rw [← hz v, map_zero, zero_pow two_ne_zero]
  obtain ⟨x, hx⟩ : ∃ x, Q.polarBilin x z ≠ 0 := by
    by_contra! h
    exact hz0 (hQ.2 z h)
  refine ⟨z, z', (Q.polarBilin x z)⁻¹ • x, ⟨hz, mulVec_sqrt_vector hQ hN hiso hz, hz',
    quad_eq_zero_of_sqrt_vector hQ hM hN hev hz, ?_⟩⟩
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]

namespace TypeCData

variable {N : Matrix ι ι K} {z z' y' : ι → K} (hd : TypeCData Q N z z' y') (hN : N * N = 0)
  (hiso : ∀ v, Q (v + N *ᵥ v) = Q v)
include hd hN hiso

omit hd hN hiso [Finite K] [Fintype ι] [DecidableEq ι] in
theorem pol_self (w : ι → K) : Q.polarBilin w w = 0 := by
  rw [polarBilin_apply_apply]
  exact polar_self_eq_zero Q w

omit hiso [Finite K] [DecidableEq ι] [CharP K 2] in
theorem pol_y_z : Q.polarBilin (N *ᵥ y') z = 0 := polar_mulVec_sqrt_vector hN hd.sq y'

omit hN hiso [Finite K] [DecidableEq ι] [CharP K 2] in
theorem quad_y : Q (N *ᵥ y') = 1 := by rw [← hd.sq y', hd.pol_y'z, one_pow]

omit hN [Finite K] [DecidableEq ι] in
theorem pol_y'_y : Q.polarBilin y' (N *ᵥ y') = 1 := by
  rw [polar_self_mulVec Q hiso, hd.quad_y]

omit [Finite K] in
theorem pol_z'_y : Q.polarBilin z' (N *ᵥ y') = 1 := by
  rw [← polar_mulVec_adj Q hN hiso, hd.mulVec_z', polarBilin_comm, hd.pol_y'z]

omit hN [Finite K] [DecidableEq ι] in
theorem pol_z'_z : Q.polarBilin z' z = 0 := by
  rw [← hd.mulVec_z', polar_self_mulVec Q hiso, hd.mulVec_z', hd.quad_z]

omit hd [Finite K] in
theorem pol_v_y (v : ι → K) : Q.polarBilin v (N *ᵥ y') = Q.polarBilin (N *ᵥ v) y' :=
  (polar_mulVec_adj Q hN hiso v y').symm

end TypeCData

@[expose] noncomputable def cTwoX (Q : QuadraticForm K (ι → K)) (y z : ι → K) : Matrix ι ι K :=
  polMat Q y z + polMat Q z y

@[expose] noncomputable def cTwoT (Q : QuadraticForm K (ι → K)) (y z : ι → K) (d : K) :
    Matrix ι ι K :=
  d • cTwoX Q y z + d ^ 2 • polMat Q z z

omit [Finite K] [CharP K 2] in
theorem cTwoT_mulVec (y z : ι → K) (d : K) (v : ι → K) :
    cTwoT Q y z d *ᵥ v = (d * Q.polarBilin v y + d ^ 2 * Q.polarBilin v z) • z +
      (d * Q.polarBilin v z) • y := by
  simp only [cTwoT, cTwoX, add_mulVec, smul_mulVec, polMat_mulVec, smul_add, smul_smul, add_smul]
  abel

omit [Finite K] in
theorem cTwoT_mul {y z : ι → K} (hyz : Q.polarBilin y z = 0) (d d' : K) :
    cTwoT Q y z d * cTwoT Q y z d' = 0 := by
  have hzy : Q.polarBilin z y = 0 := by rw [polarBilin_comm]; exact hyz
  have hyy := TypeCData.pol_self (Q := Q) y
  have hzz := TypeCData.pol_self (Q := Q) z
  simp only [cTwoT, cTwoX, add_mul, mul_add, smul_mul_smul_comm, polMat_mul, hyz, hzy, hyy,
    hzz, zero_smul, smul_zero, add_zero]

omit [Finite K] in
theorem cTwoT_add (y z : ι → K) (d d' : K) :
    cTwoT Q y z d + cTwoT Q y z d' = cTwoT Q y z (d + d') := by
  simp only [cTwoT, CharTwo.add_sq, add_smul]
  abel

omit [Finite K] in
theorem cTwoT_isometry {y z : ι → K} (hQz : Q z = 0) (hQy : Q y = 1)
    (hyz : Q.polarBilin y z = 0) (d : K) (v : ι → K) :
    Q ((1 + cTwoT Q y z d) *ᵥ v) = Q v := by
  rw [add_mulVec, one_mulVec, cTwoT_mulVec, ← add_assoc, quad_add, quad_add,
    QuadraticMap.map_smul, QuadraticMap.map_smul, hQz, hQy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [polarBilin_comm Q z y, hyz]
  linear_combination (d ^ 2 * Q.polarBilin v z ^ 2 + d * Q.polarBilin v y * Q.polarBilin v z) *
    CharTwo.two_eq_zero (R := K)

omit [Finite K] [Fintype ι] [DecidableEq ι] in
theorem add_self_vec (w : ι → K) : w + w = 0 := by
  rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]

namespace TypeCData

variable {N : Matrix ι ι K} {z z' y' : ι → K} (hd : TypeCData Q N z z' y') (hN : N * N = 0)
  (hiso : ∀ v, Q (v + N *ᵥ v) = Q v)
include hd hN hiso

omit [Finite K] in
theorem cTwoT_mulVec_span (d a b : K) :
    cTwoT Q (N *ᵥ y') z d *ᵥ (a • z + b • (N *ᵥ y')) = 0 := by
  have hyy : Q.polarBilin (N *ᵥ y') (N *ᵥ y') = 0 := polar_mulVec_mulVec Q hN hiso y' y'
  have hyz := hd.pol_y_z hN
  have hzy : Q.polarBilin z (N *ᵥ y') = 0 := by rw [polarBilin_comm]; exact hyz
  rw [cTwoT_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyy,
    hyz, hzy, pol_self, mul_zero, add_zero, zero_smul]

omit hd hiso [Finite K] [DecidableEq ι] [CharP K 2] in
theorem mulVec_span (hNz : N *ᵥ z = 0) (a b : K) : N *ᵥ (a • z + b • (N *ᵥ y')) = 0 := by
  rw [mulVec_add, mulVec_smul, mulVec_smul, hNz, mulVec_mulVec, hN, zero_mulVec, smul_zero,
    smul_zero, add_zero]

omit [Finite K] in
theorem cTwoT_mulVec_z' (d : K) : cTwoT Q (N *ᵥ y') z d *ᵥ z' = d • z := by
  rw [cTwoT_mulVec, hd.pol_z'_y hN hiso, hd.pol_z'_z hiso]
  simp

omit hN [Finite K] in
theorem cTwoT_mulVec_y' (d : K) :
    cTwoT Q (N *ᵥ y') z d *ᵥ y' = (d + d ^ 2) • z + d • (N *ᵥ y') := by
  rw [cTwoT_mulVec, hd.pol_y'_y hiso, hd.pol_y'z]
  simp only [mul_one]

omit hiso [Finite K] [CharP K 2] in
theorem mul_cTwoT (d : K) : N * cTwoT Q (N *ᵥ y') z d = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, cTwoT_mulVec, mulVec_span hN hd.mulVec_z, zero_mulVec]

omit [Finite K] [CharP K 2] in
theorem cTwoT_mul_N (d : K) : cTwoT Q (N *ᵥ y') z d * N = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, cTwoT_mulVec, polar_mulVec_mulVec Q hN hiso,
      polar_mulVec_sqrt_vector hN hd.sq, zero_mulVec]
    simp

omit [Finite K] in
theorem cTwoT_mul_cTwoT (d d' : K) : cTwoT Q (N *ᵥ y') z d * cTwoT Q (N *ᵥ y') z d' = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, cTwoT_mulVec _ _ d' v, hd.cTwoT_mulVec_span hN hiso, zero_mulVec]

@[expose] noncomputable def e₁ (Q : QuadraticForm K (ι → K)) (N : Matrix ι ι K) (z y' : ι → K) :
    Matrix ι ι K :=
  N + cTwoT Q (N *ᵥ y') z 1

omit hd hN hiso [Finite K] [CharP K 2] in
theorem e₁_mulVec' (v : ι → K) :
    e₁ Q N z y' *ᵥ v = N *ᵥ v + cTwoT Q (N *ᵥ y') z 1 *ᵥ v := by
  rw [e₁, add_mulVec]

omit [Finite K] in
theorem e₁_mul_cTwoT (d : K) : e₁ Q N z y' * cTwoT Q (N *ᵥ y') z d = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, e₁_mulVec', mulVec_mulVec, mulVec_mulVec, hd.mul_cTwoT hN,
      hd.cTwoT_mul_cTwoT hN hiso]
    simp only [zero_mulVec, add_zero]

omit [Finite K] in
theorem cTwoT_mul_e₁ (d : K) : cTwoT Q (N *ᵥ y') z d * e₁ Q N z y' = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, e₁_mulVec', mulVec_add, mulVec_mulVec, mulVec_mulVec,
      hd.cTwoT_mul_N hN hiso, hd.cTwoT_mul_cTwoT hN hiso]
    simp only [zero_mulVec, add_zero]

omit [Finite K] [CharP K 2] in
theorem e₁_mul_N : e₁ Q N z y' * N = 0 := by
  rw [e₁, add_mul, hN, hd.cTwoT_mul_N hN hiso, add_zero]

omit [Finite K] in
theorem e₁_mul_self : e₁ Q N z y' * e₁ Q N z y' = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, e₁_mulVec' v, mulVec_add, mulVec_mulVec, mulVec_mulVec,
      hd.e₁_mul_N hN hiso, hd.e₁_mul_cTwoT hN hiso]
    simp only [zero_mulVec, add_zero]

omit [Finite K] in
theorem factor (d : K) : (1 + d • e₁ Q N z y') * (1 + cTwoT Q (N *ᵥ y') z d) =
    1 + betaT Q.polarBilin N z d :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have e1 : (1 + cTwoT Q (N *ᵥ y') z d) *ᵥ v = v + cTwoT Q (N *ᵥ y') z d *ᵥ v := by
      rw [add_mulVec, one_mulVec]
    have e2 : ∀ w, (1 + d • e₁ Q N z y') *ᵥ w = w + d • (e₁ Q N z y' *ᵥ w) := fun w => by
      rw [add_mulVec, one_mulVec, smul_mulVec]
    have e3 : e₁ Q N z y' *ᵥ (cTwoT Q (N *ᵥ y') z d *ᵥ v) = 0 := by
      rw [mulVec_mulVec, hd.e₁_mul_cTwoT hN hiso, zero_mulVec]
    rw [← mulVec_mulVec, e1, e2, mulVec_add, e3, add_zero, e₁_mulVec', add_mulVec, one_mulVec,
      betaT_mulVec, cTwoT_mulVec, cTwoT_mulVec]
    have hc1 : d * Q.polarBilin v (N *ᵥ y') + d ^ 2 * Q.polarBilin v z +
        d * (1 * Q.polarBilin v (N *ᵥ y') + 1 ^ 2 * Q.polarBilin v z) =
        (d ^ 2 + d) * Q.polarBilin v z := by
      linear_combination d * Q.polarBilin v (N *ᵥ y') * CharTwo.two_eq_zero (R := K)
    have hc2 : d * Q.polarBilin v z + d * (1 * Q.polarBilin v z) = 0 := by
      linear_combination d * Q.polarBilin v z * CharTwo.two_eq_zero (R := K)
    calc v + ((d * Q.polarBilin v (N *ᵥ y') + d ^ 2 * Q.polarBilin v z) • z +
          (d * Q.polarBilin v z) • (N *ᵥ y')) + d • (N *ᵥ v +
          ((1 * Q.polarBilin v (N *ᵥ y') + 1 ^ 2 * Q.polarBilin v z) • z +
            (1 * Q.polarBilin v z) • (N *ᵥ y')))
        = v + d • (N *ᵥ v) + (d * Q.polarBilin v (N *ᵥ y') + d ^ 2 * Q.polarBilin v z +
            d * (1 * Q.polarBilin v (N *ᵥ y') + 1 ^ 2 * Q.polarBilin v z)) • z +
            (d * Q.polarBilin v z + d * (1 * Q.polarBilin v z)) • (N *ᵥ y') := by module
      _ = v + (d • (N *ᵥ v) + ((d ^ 2 + d) * Q.polarBilin v z) • z) := by
          rw [hc1, hc2, zero_smul, add_zero, add_assoc]

omit [CharP K 2] hd hN hiso [Finite K] in
theorem e₁_mulVec (v : ι → K) : e₁ Q N z y' *ᵥ v = N *ᵥ v +
    (Q.polarBilin v (N *ᵥ y') + Q.polarBilin v z) • z + Q.polarBilin v z • (N *ᵥ y') := by
  rw [e₁_mulVec', cTwoT_mulVec]
  simp only [one_mul, one_pow]
  abel

omit [Finite K] in
theorem quad_e₁ (v : ι → K) : Q (e₁ Q N z y' *ᵥ v) = 0 := by
  rw [e₁_mulVec, add_assoc, quad_add, quad_add, QuadraticMap.map_smul,
    QuadraticMap.map_smul, hd.quad_z, hd.quad_y, ← hd.sq v]
  simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul,
    polar_mulVec_sqrt_vector hN hd.sq, polar_mulVec_mulVec Q hN hiso]
  rw [polarBilin_comm Q z (N *ᵥ y'), hd.pol_y_z hN]
  linear_combination Q.polarBilin v z ^ 2 * CharTwo.two_eq_zero (R := K)

omit hN [Finite K] in
theorem pol_e₁ (v : ι → K) : Q.polarBilin v (e₁ Q N z y' *ᵥ v) = 0 := by
  rw [e₁_mulVec]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [polar_self_mulVec Q hiso, ← hd.sq v]
  linear_combination (Q.polarBilin v z ^ 2 + Q.polarBilin v (N *ᵥ y') * Q.polarBilin v z) *
    CharTwo.two_eq_zero (R := K)

omit [Finite K] in
theorem e₁_isometry (a : K) (v : ι → K) : Q ((1 + a • e₁ Q N z y') *ᵥ v) = Q v := by
  rw [add_mulVec, one_mulVec, smul_mulVec, quad_add, QuadraticMap.map_smul,
    hd.quad_e₁ hN hiso, smul_zero, add_zero, map_smul, smul_eq_mul, hd.pol_e₁ hiso, mul_zero,
    add_zero]

omit [Finite K] in
theorem e₁_mulVec_z : e₁ Q N z y' *ᵥ z = 0 := by
  have h := hd.cTwoT_mulVec_span hN hiso 1 1 0
  rw [one_smul, zero_smul, add_zero] at h
  rw [e₁_mulVec', hd.mulVec_z, h, add_zero]

omit [Finite K] in
theorem e₁_mulVec_z' : e₁ Q N z y' *ᵥ z' = 0 := by
  rw [e₁_mulVec', hd.mulVec_z', hd.cTwoT_mulVec_z' hN hiso, one_smul, add_self_vec]

omit hN [Finite K] in
theorem e₁_mulVec_y' : e₁ Q N z y' *ᵥ y' = 0 := by
  have h11 : (1 : K) + 1 ^ 2 = 0 := by rw [one_pow]; exact CharTwo.add_self_eq_zero 1
  rw [e₁_mulVec', hd.cTwoT_mulVec_y' hiso, h11, zero_smul, zero_add, one_smul, add_self_vec]

omit hd [Finite K] in
theorem adj_e₁ (u v : ι → K) :
    Q.polarBilin (e₁ Q N z y' *ᵥ u) v = Q.polarBilin u (e₁ Q N z y' *ᵥ v) := by
  rw [e₁_mulVec, e₁_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [polar_mulVec_adj Q hN hiso, polarBilin_comm Q z v, polarBilin_comm Q (N *ᵥ y') v,
    polarBilin_comm Q u z, polarBilin_comm Q u (N *ᵥ y')]
  ring

omit [Finite K] in
theorem pair_indep (a b : K) (h : a • z + b • (N *ᵥ y') = 0) : a = 0 ∧ b = 0 := by
  have h1 := congrArg (Q.polarBilin z') h
  have h2 := congrArg (Q.polarBilin y') h
  simp only [map_add, map_smul, smul_eq_mul, map_zero] at h1 h2
  rw [hd.pol_z'_z hiso, hd.pol_z'_y hN hiso] at h1
  rw [hd.pol_y'z, hd.pol_y'_y hiso] at h2
  have hb : b = 0 := by simpa using h1
  subst hb
  exact ⟨by simpa using h2, rfl⟩

omit [Finite K] in
theorem rank_cTwoT {d : K} (hd0 : d ≠ 0) : (cTwoT Q (N *ᵥ y') z d).rank = 2 := by
  refine rank_eq_two_of (hd.pair_indep hN hiso) (fun v => ⟨_, _, cTwoT_mulVec _ _ d v⟩)
    ⟨d⁻¹ • z', by rw [mulVec_smul, hd.cTwoT_mulVec_z' hN hiso, smul_smul, inv_mul_cancel₀ hd0,
      one_smul]⟩ ⟨d⁻¹ • y' - ((1 + d) * d⁻¹) • z', ?_⟩
  rw [mulVec_sub, mulVec_smul, mulVec_smul, hd.cTwoT_mulVec_y' hiso,
    hd.cTwoT_mulVec_z' hN hiso, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ hd0,
    one_smul]
  have h1 : d⁻¹ * (d + d ^ 2) = (1 + d) * d⁻¹ * d := by field_simp
  rw [h1]
  abel

omit [Finite K] in
theorem quad_cTwoT_y' (d : K) : Q (cTwoT Q (N *ᵥ y') z d *ᵥ y') = d ^ 2 := by
  rw [hd.cTwoT_mulVec_y' hiso, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul,
    hd.quad_z, hd.quad_y, map_smul, map_smul, LinearMap.smul_apply, polarBilin_comm Q z,
    hd.pol_y_z hN]
  simp only [smul_eq_mul]
  ring

omit [Finite K] in
theorem rank_e₁ : (e₁ Q N z y').rank = N.rank - 2 := by
  have hsum : N = cTwoT Q (N *ᵥ y') z 1 + e₁ Q N z y' := by
    rw [e₁, add_comm N, ← add_assoc, ← two_smul K, CharTwo.two_eq_zero, zero_smul, zero_add]
  refine rank_eq_sub_two_of_split hsum (hd.rank_cTwoT hN hiso one_ne_zero) (fun v hv => ?_)
    (hd.e₁_mulVec_z' hN hiso) (hd.e₁_mulVec_y' hiso) ?_
  · have hvz : Q.polarBilin v z = 0 := by
      have h := hd.sq v
      rw [hv, QuadraticMap.map_zero] at h
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [e₁_mulVec, hv, hvz, pol_v_y hN hiso, hv, map_zero, LinearMap.zero_apply]
    simp
  · intro a b h
    rw [hd.mulVec_z'] at h
    exact hd.pair_indep hN hiso a b h

@[expose] noncomputable def fVec (Q : QuadraticForm K (ι → K)) (z z' y' : ι → K) : ι → K :=
  y' + z' + Q (y' + z') • z

omit [DecidableEq ι] hN [Finite K] in
theorem pol_z_f : Q.polarBilin z (fVec Q z z' y') = 1 := by
  rw [fVec, map_add, map_add, map_smul, pol_self, smul_zero, add_zero, polarBilin_comm Q z y',
    hd.pol_y'z, polarBilin_comm Q z z', hd.pol_z'_z hiso, add_zero]

omit [DecidableEq ι] hN [Finite K] in
theorem quad_f : Q (fVec Q z z' y') = 0 := by
  have h1 : Q.polarBilin (y' + z') z = 1 := by
    rw [map_add, LinearMap.add_apply, hd.pol_y'z, hd.pol_z'_z hiso, add_zero]
  rw [fVec, quad_add, QuadraticMap.map_smul, hd.quad_z, smul_zero, add_zero, map_smul,
    smul_eq_mul, h1, mul_one, CharTwo.add_self_eq_zero]

omit [Finite K] in
theorem pol_y_f : Q.polarBilin (N *ᵥ y') (fVec Q z z' y') = 0 := by
  rw [fVec, map_add, map_add, map_smul, hd.pol_y_z hN, smul_zero, add_zero,
    polarBilin_comm Q _ y', hd.pol_y'_y hiso, polarBilin_comm Q _ z', hd.pol_z'_y hN hiso,
    CharTwo.add_self_eq_zero]

omit [Finite K] in
theorem e₁_mulVec_f : e₁ Q N z y' *ᵥ fVec Q z z' y' = 0 := by
  rw [fVec, mulVec_add, mulVec_add, mulVec_smul, hd.e₁_mulVec_y' hiso,
    hd.e₁_mulVec_z' hN hiso, hd.e₁_mulVec_z hN hiso, smul_zero, add_zero, add_zero]

omit [Finite K] in
theorem e₁_mul_hypMat (α : K) : e₁ Q N z y' * hypMat Q z (fVec Q z z' y') α =
    hypMat Q z (fVec Q z z' y') α * e₁ Q N z y' :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have h1 : Q.polarBilin (e₁ Q N z y' *ᵥ v) (fVec Q z z' y') = 0 := by
      rw [adj_e₁ hN hiso, hd.e₁_mulVec_f hN hiso, map_zero]
    have h2 : Q.polarBilin (e₁ Q N z y' *ᵥ v) z = 0 := by
      rw [adj_e₁ hN hiso, hd.e₁_mulVec_z hN hiso, map_zero]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hypMat_mulVec, hypMat_mulVec, mulVec_add, mulVec_add,
      mulVec_smul, mulVec_smul, hd.e₁_mulVec_z hN hiso, hd.e₁_mulVec_f hN hiso, h1, h2]
    simp

omit [Finite K] in
theorem conj_cTwoT {c : K} (hc : c ≠ 0) (x : K) :
    ((hypGL (hd.pol_z_f hiso) (inv_ne_zero hc))⁻¹ : GL ι K) * cTwoT Q (N *ᵥ y') z x *
      (hypGL (hd.pol_z_f hiso) (inv_ne_zero hc) : GL ι K) = cTwoT Q (N *ᵥ y') z (c * x) := by
  set D := hypGL (hd.pol_z_f hiso) (inv_ne_zero hc) with hD
  have hDiso : ∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v := fun v => by
    rw [hD, coe_hypGL]
    exact hypMat_isometry (hd.pol_z_f hiso) hd.quad_z (hd.quad_f hiso) (inv_ne_zero hc) v
  have hDi : ((D⁻¹ : GL ι K) : Matrix ι ι K) = hypMat Q z (fVec Q z z' y') c := by
    rw [hD, coe_hypGL_inv, inv_inv]
  have hz : ((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z = c • z := by
    rw [hDi, hypMat_mulVec, hd.pol_z_f hiso, pol_self, mul_one, mul_zero, zero_smul, add_zero]
    rw [← one_smul K z]
    simp only [smul_smul, ← add_smul]
    congr 1
    ring
  have hy : ((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ (N *ᵥ y') = N *ᵥ y' := by
    rw [hDi, hypMat_mulVec, hd.pol_y_f hN hiso, polarBilin_comm Q _ z, polarBilin_comm Q z,
      hd.pol_y_z hN]
    simp
  have hconj : ∀ A B : Matrix ι ι K, ((D⁻¹ : GL ι K) : Matrix ι ι K) * (A + B) * D =
      ((D⁻¹ : GL ι K) : Matrix ι ι K) * A * D + ((D⁻¹ : GL ι K) : Matrix ι ι K) * B * D :=
    fun A B => by rw [mul_add, add_mul]
  have hsmul : ∀ (k : K) (A : Matrix ι ι K), ((D⁻¹ : GL ι K) : Matrix ι ι K) * (k • A) * D =
      k • (((D⁻¹ : GL ι K) : Matrix ι ι K) * A * D) :=
    fun k A => by rw [mul_smul_comm, smul_mul_assoc]
  rw [cTwoT, cTwoX, hconj, hsmul, hsmul, hconj, conj_polMat Q hDiso, conj_polMat Q hDiso,
    conj_polMat Q hDiso, hz, hy, polMat_smul_left, polMat_smul_right, polMat_smul_left,
    polMat_smul_right, cTwoT, cTwoX]
  module

end TypeCData

end Data

section Main

variable [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem splitAt_of_typeCData (Q : QuadraticForm K (ι → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega ⇑Q)} (hZ : Odd (Nat.card (center ↥A)))
    {ℓ : ℕ} (hℓ : 4 ≤ ℓ) {N : Matrix ι ι K} (hN : N * N = 0)
    (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hr : N.rank = ℓ) (hev : Even ℓ) {z z' y' : ι → K}
    (hd : TypeCData Q N z z' y') {J : Subgroup G} (W : K → GL ι K)
    (hWc : ∀ d, (W d : Matrix ι ι K) = 1 + betaT Q.polarBilin N z d)
    (hJ : ∀ j, j ∈ J ↔ ∃ d, j ^ 2 = 1 ∧ Represents e j (W d)) :
    SplitAt A J (Nat.card K)
      (fun x => HasSuzukiType e (fun M v => Q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a (ℓ - 2))
      (fun x => HasSuzukiType e (fun M v => Q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .c 2) := by
  have hz0 : z ≠ 0 := by
    intro h
    have h1 := hd.pol_y'z
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hyz : Q.polarBilin (N *ᵥ y') z = 0 := hd.pol_y_z hN
  have hE₁E₁ := hd.e₁_mul_self hN hiso
  have hsE : ∀ a : K, (a • TypeCData.e₁ Q N z y') * (a • TypeCData.e₁ Q N z y') = 0 := fun a => by
    rw [smul_mul_smul_comm, hE₁E₁, smul_zero]
  have hrE : (TypeCData.e₁ Q N z y').rank = ℓ - 2 := by rw [hd.rank_e₁ hN hiso, hr]
  have hE0 : TypeCData.e₁ Q N z y' ≠ 0 := fun h => by
    rw [h, Matrix.rank_zero] at hrE
    omega
  set W₁ : K → GL ι K := fun a => sqZeroGL (a • TypeCData.e₁ Q N z y') (hsE a) with hW₁
  set W₂ : K → GL ι K := fun a => sqZeroGL (cTwoT Q (N *ᵥ y') z a) (cTwoT_mul hyz a a)
    with hW₂
  have hW₁c : ∀ a, (W₁ a : Matrix ι ι K) = 1 + a • TypeCData.e₁ Q N z y' := fun a => rfl
  have hW₂c : ∀ a, (W₂ a : Matrix ι ι K) = 1 + cTwoT Q (N *ᵥ y') z a := fun a => rfl
  have hev2 : Even (ℓ - 2) := by
    obtain ⟨j, hj⟩ := hev
    exact ⟨j - 1, by omega⟩
  have hrkE : ∀ a : K, a ≠ 0 → (a • TypeCData.e₁ Q N z y').rank = ℓ - 2 := fun a ha => by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ha), hrE]
  have hT₂0 : cTwoT Q (N *ᵥ y') z 0 = 0 := by simp [cTwoT]
  refine splitAt_of_lifts (e := e) hZ W₁ W₂ (fun a => ?_) (fun a => ?_) (fun a b => ?_)
    (fun a b => ?_) (fun a => sqZeroGL_sq _ _) (fun a => sqZeroGL_sq _ _) (fun a b => ?_)
    (fun a c h => ?_) (fun a c h => ?_) (fun a b c h => ?_) (fun j => ?_) (fun c hc => ?_) _ _
    (fun a ha x hx2 hx => ?_) (fun a ha x hx2 hx => ?_)
  ·
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hW₁c]
      exact hd.e₁_isometry hN hiso a v
    · rw [commRank_sqZeroGL]
      by_cases ha : a = 0
      · rw [ha, zero_smul, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [hrkE a ha]
        exact hev2
  ·
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hW₂c]
      exact cTwoT_isometry hd.quad_z hd.quad_y hyz a v
    · rw [commRank_sqZeroGL]
      by_cases ha : a = 0
      · rw [ha, hT₂0, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [hd.rank_cTwoT hN hiso ha]
        exact ⟨1, rfl⟩
  ·
    apply Units.ext
    rw [Units.val_mul, hW₁c, hW₁c, hW₁c, add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm,
      hE₁E₁, smul_zero, add_zero, add_smul]
    abel
  ·
    apply Units.ext
    rw [Units.val_mul, hW₂c, hW₂c, hW₂c, add_mul, one_mul, mul_add, mul_one, cTwoT_mul hyz,
      add_zero, ← cTwoT_add (N *ᵥ y') z a b]
    abel
  ·
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hW₁c, hW₂c, add_mul, one_mul, mul_add, mul_one,
      smul_mul_assoc, hd.e₁_mul_cTwoT hN hiso, smul_zero, add_zero, add_mul, one_mul, mul_add,
      mul_one, mul_smul_comm, hd.cTwoT_mul_e₁ hN hiso, smul_zero, add_zero]
    abel
  ·
    have h0 := eq_zero_of_sqZeroGL_eq_scalar (hsE a) h
    exact (smul_eq_zero.mp h0).resolve_right hE0
  ·
    have h0 := eq_zero_of_sqZeroGL_eq_scalar _ h
    have h1 := hd.cTwoT_mulVec_z' hN hiso a
    rw [h0, zero_mulVec] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hz0
  ·
    have hm := congrArg (fun X : GL ι K => (X : Matrix ι ι K)) h
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hW₁c, hW₂c,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one] at hm
    have hzc : cTwoT Q (N *ᵥ y') z b *ᵥ z = 0 := by
      have h3 := hd.cTwoT_mulVec_span hN hiso b 1 0
      rwa [one_smul, zero_smul, add_zero] at h3
    have hcz : z = (c : K) • z := by
      have h1 := congrArg (· *ᵥ z) hm
      simp only [add_mulVec, one_mulVec, hzc, add_zero, smul_mulVec, hd.e₁_mulVec_z hN hiso,
        smul_zero] at h1
      exact h1
    have hc1 : (c : K) = 1 := by
      by_contra hne
      have h4 : ((c : K) - 1) • z = 0 := by rw [sub_smul, one_smul, ← hcz, sub_self]
      exact hz0 ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne))
    rw [hc1, one_smul, add_right_inj] at hm
    have h5 := congrArg (· *ᵥ y') hm
    simp only [hd.cTwoT_mulVec_y' hiso, smul_mulVec, hd.e₁_mulVec_y' hiso,
      smul_zero] at h5
    obtain ⟨-, hb2⟩ := hd.pair_indep hN hiso _ _ h5
    rw [hb2, hT₂0] at hm
    exact (smul_eq_zero.mp hm.symm).resolve_right hE0
  ·
    rw [hJ]
    refine exists_congr fun d => and_congr_right fun _ => ?_
    have hWd : W d = W₁ d * W₂ d := by
      apply Units.ext
      rw [Units.val_mul, hWc, hW₁c, hW₂c]
      exact (hd.factor hN hiso d).symm
    rw [hWd]
  ·
    set D := hypGL (hd.pol_z_f hiso) (inv_ne_zero hc) with hD
    have hDc : (D : Matrix ι ι K) = hypMat Q z (TypeCData.fVec Q z z' y') c⁻¹ := rfl
    refine ⟨D, ?_, fun x => ⟨?_, ?_⟩⟩
    · refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
      · rw [hDc]
        exact hypMat_isometry (hd.pol_z_f hiso) hd.quad_z (hd.quad_f hiso)
          (inv_ne_zero hc) v
      · exact hypGL_even_commRank (hd.pol_z_f hiso) (inv_ne_zero hc)
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hW₁c, mul_add, mul_one, add_mul, Units.inv_mul,
        mul_smul_comm, smul_mul_assoc, mul_assoc, hDc, hd.e₁_mul_hypMat hN hiso, ← hDc,
        ← mul_assoc, Units.inv_mul, one_mul]
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hW₂c, hW₂c, mul_add, mul_one, add_mul, Units.inv_mul,
        hd.conj_cTwoT hN hiso hc x]
  ·
    refine ⟨hx2, W₁ a, hx, orderOf_sqZeroGL (hsE a) (fun h => ha ?_), ?_, hev2, fun v => ?_⟩
    · exact (smul_eq_zero.mp h).resolve_right hE0
    · rw [commRank_sqZeroGL, hrkE a ha]
    · show Q (((W₁ a : Matrix ι ι K) - 1) *ᵥ v) = 0
      rw [hW₁c, add_sub_cancel_left, smul_mulVec, QuadraticMap.map_smul,
        hd.quad_e₁ hN hiso, smul_zero]
  ·
    refine ⟨hx2, W₂ a, hx, orderOf_sqZeroGL _ (fun h => ?_), ?_, even_two, y', ?_⟩
    · have h1 := hd.rank_cTwoT hN hiso ha
      rw [h, Matrix.rank_zero] at h1
      exact absurd h1 (by norm_num)
    · rw [commRank_sqZeroGL, hd.rank_cTwoT hN hiso ha]
    · show Q (((W₂ a : Matrix ι ι K) - 1) *ᵥ y') ≠ 0
      rw [hW₂c, add_sub_cancel_left, hd.quad_cTwoT_y' hN hiso]
      exact pow_ne_zero 2 ha

theorem splitAt_jGroup_of_typeC (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K)
    (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} {ℓ : ℕ} (hℓ : 4 ≤ ℓ)
    (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .c ℓ)
    (hreg : RegularOn A (jGroup A p) (nonidentity (jGroup A p)))
    (haut : AutCyclic A (jGroup A p) (Nat.card K - 1)) :
    SplitAt A (jGroup A p) (Nat.card K)
      (fun x => HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a (ℓ - 2))
      (fun x => HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .c 2) := by
  subst hq
  obtain ⟨hp2, M, hpM, hM2, hr, ⟨hev, hc⟩⟩ := hp
  have hMiso : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v := statedOmega_isometry hpM.2.1
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    have h1 : v + ((M : Matrix ι ι K) - 1) *ᵥ v = (M : Matrix ι ι K) *ᵥ v := by
      rw [sub_mulVec, one_mulVec, add_sub_cancel]
    rw [h1]
    exact hMiso v
  have hev' : Even (commRank M) := hr ▸ hev
  obtain ⟨z, z', y', hd⟩ := exists_typeCData hQ hMiso hM2 hev' hc
  obtain ⟨W, hWc, hJ⟩ := exists_beta_jGroup Q hQ hT hZ hp2 hpM hM2 hev' hd.sq hreg haut
  exact splitAt_of_typeCData Q hQ hT hZ hℓ (sub_one_mul_self_eq_zero hM2) hiso hr hev hd W hWc hJ

end Main

theorem regularOn_autCyclic_of_case {G : Type} [Group G] {A : Subgroup G} {D : ClassicalModel A}
    {p : G} (h : Case1 D p ∨ Case4 D p) :
    RegularOn A (jGroup A p) (nonidentity (jGroup A p)) ∧ AutCyclic A (jGroup A p) (D.q - 1) := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h

theorem orthPlusSplitC : OrthPlusSplitC := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp hcase
  have hJ := regularOn_autCyclic_of_case hcase
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hreg, haut⟩ := hJ
    have haut' : AutCyclic A (jGroup A p) (Nat.card K - 1) := by
      rw [hK]
      exact haut
    have hsplit := splitAt_jGroup_of_typeC (CFSG.LieType.Universal.Spin.quadPlus n K)
      (StatedQuadPlus n K) (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K) hZ hℓ hp hreg haut'
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem orthMinusSplitC : OrthMinusSplitC := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp hcase
  have hJ := regularOn_autCyclic_of_case hcase
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨hreg, haut⟩ := hJ
    have haut' : AutCyclic A (jGroup A p) (Nat.card K - 1) := by
      rw [hK]
      exact haut
    have hsplit := splitAt_jGroup_of_typeC (CFSG.LieType.Universal.Spin.quadMinus n K b c)
      (StatedQuadMinus n K b c) (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c) hZ hℓ hp hreg haut'
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
