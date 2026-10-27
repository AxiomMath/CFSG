module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpLift
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

section Shape

variable {F : Type} [Field F]

theorem sp4_shape_one (σ : F ≃+* F) (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hdet : A.det ≠ 0) (k : Fin 2)
    (hu : ∀ t : F, A * Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
      Matrix.transvection (Sum.inl k) (Sum.inr k) t * A)
    (hl : ∀ t : F, A * Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
      Matrix.transvection (Sum.inr k) (Sum.inl k) t * A) :
    σ = RingEquiv.refl F ∧ ∃ a : F, a ≠ 0 ∧
      (∀ b, b ≠ Sum.inl k → A (Sum.inl k) b = 0) ∧ (∀ b, b ≠ Sum.inr k → A (Sum.inr k) b = 0) ∧
      (∀ c, c ≠ Sum.inl k → A c (Sum.inl k) = 0) ∧ (∀ c, c ≠ Sum.inr k → A c (Sum.inr k) = 0) ∧
      A (Sum.inl k) (Sum.inl k) = a ∧ A (Sum.inr k) (Sum.inr k) = a := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  obtain ⟨r1, c1, d1⟩ := rel_facts (p := Sum.inl k) (q := Sum.inr k) σ A 1 h1 (by simpa using hu 1)
  obtain ⟨r2, c2, d2⟩ := rel_facts (p := Sum.inr k) (q := Sum.inl k) σ A 1 h1 (by simpa using hl 1)
  rw [map_one, one_mul] at d1 d2
  have hdd : A (Sum.inr k) (Sum.inr k) = A (Sum.inl k) (Sum.inl k) := by linear_combination -d1
  have ha : A (Sum.inl k) (Sum.inl k) ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero (Sum.inl k) fun j => ?_
    by_cases hj : j = Sum.inl k
    · rw [hj, h0]
    · exact r2 j hj
  refine ⟨RingEquiv.ext fun t => ?_, A (Sum.inl k) (Sum.inl k), ha, r2, r1, c1, c2, rfl, hdd⟩
  by_cases ht : t = 0
  · rw [ht, map_zero]
    rfl
  · have := (rel_facts (p := Sum.inl k) (q := Sum.inr k) σ A t ht (hu t)).2.2
    rw [hdd] at this
    have h3 : A (Sum.inl k) (Sum.inl k) * (σ t - t) = 0 := by linear_combination this
    have := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left ha)
    exact this

end Shape

section Swap

variable {F : Type} [Field F]

def swapIdx : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 := Sum.map Fin.rev Fin.rev

theorem swapIdx_swapIdx (c : Fin 2 ⊕ Fin 2) : swapIdx (swapIdx c) = c := by
  rcases c with c | c <;> simp [swapIdx]

def swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun b c => if b = swapIdx c then 1 else 0

theorem swapMat_symp :
    (swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * SymplecticPairs.gram F 2 * swapMat =
      SymplecticPairs.gram F 2 := by
  ext a b
  rw [transpose_mul_gram_mul_apply]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [swapMat, swapIdx, par, sgn, Fintype.sum_sum_type, SymplecticPairs.gram,
      Matrix.fromBlocks, Fin.rev]

theorem swap_comm_apply (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (h : B * swapMat = swapMat * B) (c d : Fin 2 ⊕ Fin 2) :
    B c (swapIdx d) = B (swapIdx c) d := by
  have h1 := congrFun (congrFun h c) d
  have e1 : (B * swapMat (F := F)) c d = B c (swapIdx d) := by
    simp [Matrix.mul_apply, swapMat]
  have e2 : (swapMat (F := F) * B) c d = B (swapIdx c) d := by
    simp only [Matrix.mul_apply, swapMat, Matrix.of_apply]
    rw [Finset.sum_eq_single (swapIdx c)]
    · simp [swapIdx_swapIdx]
    · intro e _ he
      have : c ≠ swapIdx e := fun hce => he (by rw [hce, swapIdx_swapIdx])
      simp [this]
    · simp
  rw [← e1, ← e2]
  exact h1

theorem swap_comm_apply' (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (h : B * swapMat = swapMat * B) (c d : Fin 2 ⊕ Fin 2) :
    B c d = B (swapIdx c) (swapIdx d) := by
  have := swap_comm_apply B h c (swapIdx d)
  rwa [swapIdx_swapIdx] at this

theorem sum_fin_two_rev {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) (k : Fin 2) :
    ∑ i, f i = f k + f (Fin.rev k) := by
  fin_cases k <;> simp [Fin.sum_univ_two, add_comm]

end Swap

section Entries

variable {F : Type} [Field F]

theorem scalar_of_sq_det (h2 : (2 : F) ≠ 0) {a p q r s : F} (ha : a ≠ 0)
    (e11 : a * a = p * p + q * r) (e12 : 0 = p * q + q * s) (e21 : 0 = r * p + s * r)
    (e22 : a * a = r * q + s * s) (hdet : p * s + -(r * q) = a * a) :
    q = 0 ∧ r = 0 ∧ p = s := by
  by_cases hps : p + s = 0
  · exfalso
    have h1 : p * (p + s) = 2 * (a * a) := by linear_combination (-1 : F) * e11 + hdet
    rw [hps, mul_zero] at h1
    exact mul_ne_zero h2 (mul_ne_zero ha ha) h1.symm
  · have hq : q = 0 := by
      have : q * (p + s) = 0 := by linear_combination -e12
      exact (mul_eq_zero.mp this).resolve_right hps
    have hr : r = 0 := by
      have : r * (p + s) = 0 := by linear_combination -e21
      exact (mul_eq_zero.mp this).resolve_right hps
    refine ⟨hq, hr, ?_⟩
    have : (p - s) * (p - s) = 0 := by
      linear_combination (-1 : F) * e11 + (-1 : F) * e22 + (-2 : F) * hdet + (-4 * r) * hq
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

theorem sp4_entries (h2 : (2 : F) ≠ 0) (k : Fin 2)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) {a : F} (ha : a ≠ 0)
    (r1 : ∀ b, b ≠ Sum.inl k → A (Sum.inl k) b = 0)
    (r2 : ∀ b, b ≠ Sum.inr k → A (Sum.inr k) b = 0)
    (c1 : ∀ c, c ≠ Sum.inl k → A c (Sum.inl k) = 0)
    (c2 : ∀ c, c ≠ Sum.inr k → A c (Sum.inr k) = 0)
    (d1 : A (Sum.inl k) (Sum.inl k) = a) (d2 : A (Sum.inr k) (Sum.inr k) = a)
    (hsim : ∃ μ : Fˣ, Aᵀ * formJ 2 F * A = (μ : F) • formJ 2 F)
    (hsw : A * A * swapMat = swapMat * (A * A)) :
    (∀ c e, c ≠ e → A c e = 0) ∧
      A (Sum.inl (Fin.rev k)) (Sum.inl (Fin.rev k)) =
        A (Sum.inr (Fin.rev k)) (Sum.inr (Fin.rev k)) := by
  classical
  have hkk : Fin.rev k ≠ k := by fin_cases k <;> decide
  have z1 : A (Sum.inl k) (Sum.inl (Fin.rev k)) = 0 := r1 _ (by simpa using hkk)
  have z2 : A (Sum.inl k) (Sum.inr k) = 0 := r1 _ (by simp)
  have z3 : A (Sum.inl k) (Sum.inr (Fin.rev k)) = 0 := r1 _ (by simp)
  have z4 : A (Sum.inr k) (Sum.inl k) = 0 := r2 _ (by simp)
  have z5 : A (Sum.inr k) (Sum.inl (Fin.rev k)) = 0 := r2 _ (by simp)
  have z6 : A (Sum.inr k) (Sum.inr (Fin.rev k)) = 0 := r2 _ (by simpa using hkk)
  have z7 : A (Sum.inl (Fin.rev k)) (Sum.inl k) = 0 := c1 _ (by simpa using hkk)
  have z8 : A (Sum.inr (Fin.rev k)) (Sum.inl k) = 0 := c1 _ (by simp)
  have z9 : A (Sum.inl (Fin.rev k)) (Sum.inr k) = 0 := c2 _ (by simp)
  have z10 : A (Sum.inr (Fin.rev k)) (Sum.inr k) = 0 := c2 _ (by simpa using hkk)
  obtain ⟨μ, hμ⟩ := hsim
  have hμ' : Aᵀ * SymplecticPairs.gram F 2 * A = (μ : F) • SymplecticPairs.gram F 2 := hμ
  have hs1 := congrFun (congrFun hμ' (Sum.inl k)) (Sum.inr k)
  have hs2 := congrFun (congrFun hμ' (Sum.inl (Fin.rev k))) (Sum.inr (Fin.rev k))
  rw [transpose_mul_gram_mul_apply] at hs1 hs2
  simp [Fintype.sum_sum_type, sum_fin_two_rev _ k, par, sgn, SymplecticPairs.gram_apply, z1, z2,
    z3, z4, z5, z6, z7, z8, z9, z10, d1, d2] at hs1 hs2
  have hB := swap_comm_apply' (A * A) hsw
  have b11 := hB (Sum.inl k) (Sum.inl k)
  have b12 := hB (Sum.inl k) (Sum.inr k)
  have b21 := hB (Sum.inr k) (Sum.inl k)
  have b22 := hB (Sum.inr k) (Sum.inr k)
  simp [swapIdx, Matrix.mul_apply, Fintype.sum_sum_type, sum_fin_two_rev _ k, z1, z2, z3,
    z4, z5, z6, z7, z8, z9, z10, d1, d2] at b11 b12 b21 b22
  obtain ⟨hq0, hr0, hpq⟩ := scalar_of_sq_det h2 ha b11 b12 b21 b22 (hs2.trans hs1.symm)
  refine ⟨?_, hpq⟩
  intro c e hce
  clear hB b11 b12 b21 b22 hsw hs1 hs2 hμ hμ' hpq
  fin_cases k <;> rcases c with i | i <;> rcases e with j | j <;> fin_cases i <;> fin_cases j <;>
    simp_all

theorem diagonal_commute_blockMat {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → F) {p q : κ}
    (hpq : d p = d q) (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix.diagonal d * CFSG.LieType.Steinberg.Sp.blockMat p q M =
      CFSG.LieType.Steinberg.Sp.blockMat p q M * Matrix.diagonal d := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, CFSG.LieType.Steinberg.Sp.blockMat,
    Matrix.of_apply]
  split_ifs <;> first
    | (subst_vars; simp_all [mul_comm]; done)
    | (rcases eq_or_ne a b with hab | hab <;> simp_all [Matrix.one_apply, mul_comm])

end Entries

section Main

theorem comm_of_conj_conj {G : Type*} [Group G] (a w : G) (h : a * (a * w * a⁻¹) * a⁻¹ = w) :
    a * a * w = w * (a * a) := by
  calc a * a * w = (a * (a * w * a⁻¹) * a⁻¹) * a * a := by group
    _ = w * (a * a) := by rw [h]; group

variable {F : Type} [Field F] [Finite F]

theorem sp4_no_sigma (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    (ψ : StatedSp 2 F →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hperf : Group.IsPerfect (StatedSp 2 F))
    (k : Fin 2) (σ : MulAut X) (hσ2 : ∀ x, σ (σ x) = x)
    (h0 : ∀ r ∈ (longBlock F 2 k).range, σ (ψ r) = ψ r)
    (hnt : ∃ r ∈ (longBlock F 2 (Fin.rev k)).range, σ (ψ r) ≠ ψ r) : False := by
  classical
  have hodd : ringChar F ≠ 2 := by
    intro h
    have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [h])
    exact h2 (by simpa using h3)
  obtain ⟨A, τ, hAτ⟩ := CFSG.ClassicalInvolution.RouteD.exists_semilinear_lift hodd h4 ψ hker σ hσ2
    (fun x => by rw [MonoidHom.range_eq_top.mpr hψ]; exact Subgroup.mem_top _)
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (StatedSp 2 F),
      ∀ g, α g = conjSp 2 F A (fieldSp 2 F τ g) := ⟨conjSp 2 F A * fieldSp 2 F τ, fun g => rfl⟩
  have hlift : ∀ x, ψ (α x) = σ (ψ x) := fun x => by rw [hαdef]; exact (hAτ x).symm
  have hfix : ∀ r ∈ (longBlock F 2 k).range, α r = r := by
    have : Group.IsPerfect (longRootSp2 F 2 k) := (isClassicalSL2_longRootSp2 h2 k).isPerfect h4
    refine eq_of_central_ratio (longRootSp2 F 2 k) α.toMonoidHom (fun r hr => hker ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    show ψ (α r) * (ψ r)⁻¹ = 1
    rw [hlift, h0 r hr, mul_inv_cancel]
  have hu : ∀ t : F,
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (τ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro t
    have hg := hfix (longBlock F 2 k (sl2Upper t)) ⟨_, rfl⟩
    have := rel_of_fixed A τ _ ((hαdef _).symm.trans hg)
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ t : F,
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (τ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro t
    have hg := hfix (longBlock F 2 k (sl2Lower t)) ⟨_, rfl⟩
    have := rel_of_fixed A τ _ ((hαdef _).symm.trans hg)
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hτ1, a, ha, r1, r2, c1, c2, d1, d2⟩ := sp4_shape_one τ _ hdet k hu hl
  subst hτ1
  have := hperf
  have hα2 : ∀ g, α (α g) = g := by
    have := lift_comp_self_eq_id (θ := ψ) hker (σ := σ) hσ2 (α := α.toMonoidHom) hlift
    intro g
    simpa using DFunLike.congr_fun this g
  have hαrefl : ∀ g, α g = conjSp 2 F A g := fun g => by
    rw [hαdef, show fieldSp 2 F (RingEquiv.refl F) = 1 from map_one _]
    rfl
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
  set w : StatedSp 2 F := ofSymplecticMat (swapMat (F := F)) swapMat_symp with hw
  have hsw : Am * Am * swapMat = swapMat * (Am * Am) := by
    have h := congrArg (fun g : StatedSp 2 F => (g : GL (Fin 2 ⊕ Fin 2) F)) (hα2 w)
    simp only [hαrefl, coe_conjSp] at h
    have h' := congrArg
      (fun g : GL (Fin 2 ⊕ Fin 2) F => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
      (comm_of_conj_conj _ _ h)
    have hwm : ((w : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        swapMat := rfl
    simp only [Units.val_mul, hwm] at h'
    exact h'
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  obtain ⟨hoff, hpq⟩ := sp4_entries h2 k _ ha r1 r2 c1 c2 d1 d2 ⟨μ, hμ⟩ hsw
  have hdiag : Am = Matrix.diagonal (fun c => Am c c) := by
    ext c e
    by_cases hce : c = e
    · subst hce
      simp
    · rw [Matrix.diagonal_apply_ne _ hce]
      exact hoff c e hce
  have hcomm : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Am * CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl (Fin.rev k)) (Sum.inr (Fin.rev k)) M =
        CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl (Fin.rev k)) (Sum.inr (Fin.rev k)) M * Am := by
    intro M
    have := diagonal_commute_blockMat (fun c => Am c c) (p := Sum.inl (Fin.rev k))
      (q := Sum.inr (Fin.rev k)) hpq M
    rwa [← hdiag] at this
  have hfix' : ∀ r ∈ (longBlock F 2 (Fin.rev k)).range, α r = r := by
    rintro _ ⟨y, rfl⟩
    rw [hαrefl]
    apply Subtype.ext
    rw [coe_conjSp]
    have hc : (A : GL (Fin 2 ⊕ Fin 2) F) *
        ((longBlock F 2 (Fin.rev k) y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
        ((longBlock F 2 (Fin.rev k) y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
          (A : GL (Fin 2 ⊕ Fin 2) F) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      have := hcomm (y : Matrix (Fin 2) (Fin 2) F)
      rw [← mat_longBlock] at this
      exact this
    exact mul_inv_eq_iff_eq_mul.mpr hc
  obtain ⟨r, hr, hne⟩ := hnt
  exact hne (by rw [← hlift, hfix' r hr])

end Main

end CFSG.ClassicalInvolution.Asc77.T8W
