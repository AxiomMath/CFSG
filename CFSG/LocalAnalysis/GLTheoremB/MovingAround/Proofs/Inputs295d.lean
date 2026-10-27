module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295c2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295d

open Matrix CFSG.Open
open LinearMap (BilinForm)

section Block

variable {n : ℕ} {K : Type} [Field K]

@[expose] def blkMat (M : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (diagonal fun i => M i 0 0) (diagonal fun i => M i 0 1)
    (diagonal fun i => M i 1 0) (diagonal fun i => M i 1 1)

theorem blkMat_mul (M N : Fin n → Matrix (Fin 2) (Fin 2) K) :
    blkMat M * blkMat N = blkMat (fun i => M i * N i) := by
  simp only [blkMat, fromBlocks_multiply, diagonal_mul_diagonal, ← diagonal_add]
  congr 1 <;> congr 1 <;> funext i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem blkMat_one : blkMat (n := n) (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  simp only [blkMat, fromBlocks_one.symm]
  congr 1 <;> simp

theorem blkMat_injective :
    Function.Injective (blkMat : (Fin n → Matrix (Fin 2) (Fin 2) K) → _) := by
  intro M N h
  funext i
  have h1 := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have h2 := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  have h3 := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
  have h4 := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
  simp [blkMat] at h1 h2 h3 h4
  ext p q
  fin_cases p <;> fin_cases q <;> simpa

theorem blkMat_symplectic (M : Fin n → Matrix (Fin 2) (Fin 2) K) (hM : ∀ i, (M i).det = 1) :
    (blkMat M)ᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * blkMat M =
      fromBlocks 0 1 (-1) 0 := by
  simp only [blkMat, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul]
  have hd : ∀ i, M i 0 0 * M i 1 1 - M i 0 1 * M i 1 0 = 1 := fun i => by
    rw [← Matrix.det_fin_two (M i)]; exact hM i
  have key : ∀ f g : Fin n → K, -(diagonal f) + diagonal g = diagonal (fun i => g i - f i) := by
    intro f g
    rw [neg_add_eq_sub, ← diagonal_sub]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, ← diagonal_zero]
    congr 1
    funext i
    simp [mul_comm]
  · rw [key, ← diagonal_one]
    congr 1
    funext i
    have := hd i
    linear_combination this
  · rw [key, ← diagonal_one, diagonal_neg]
    congr 1
    funext i
    have := hd i
    linear_combination (-1 : K) * this
  · rw [key, ← diagonal_zero]
    congr 1
    funext i
    simp [mul_comm]

@[expose] def blkGL : (Fin n → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin n ⊕ Fin n) K where
  toFun M :=
    { val := blkMat fun i =>
        ((M i : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      inv := blkMat fun i =>
        (((M i)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [blkMat_mul]
        simp_rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
        exact blkMat_one
      inv_val := by
        rw [blkMat_mul]
        simp_rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
        exact blkMat_one }
  map_one' := by
    apply Units.ext
    simp only [Units.val_one, Matrix.SpecialLinearGroup.coe_one, Pi.one_apply]
    exact blkMat_one
  map_mul' M N := by
    apply Units.ext
    simp only [Units.val_mul, Pi.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
    exact (blkMat_mul _ _).symm

theorem coe_blkGL (M : Fin n → Matrix.SpecialLinearGroup (Fin 2) K) :
    ((blkGL M : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      blkMat fun i => ((M i : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blkGL_injective : Function.Injective (blkGL (n := n) (K := K)) := by
  intro M N h
  have h' := congrArg
    (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h
  simp only [coe_blkGL] at h'
  have := blkMat_injective h'
  funext i
  exact Subtype.ext (congrFun this i)

theorem blkGL_mem_statedSp (M : Fin n → Matrix.SpecialLinearGroup (Fin 2) K) :
    blkGL M ∈ StatedSp n K := by
  rw [StatedAPI.mem_statedSp_iff, coe_blkGL]
  exact blkMat_symplectic _ fun i => (M i).2

end Block

section Conj

variable {n : ℕ} {K : Type} [Field K]

theorem fromBlocks_eq_neg_J :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = -Matrix.J (Fin n) K := by
  simp [Matrix.J, fromBlocks_neg]

theorem mem_statedSp_iff_J {g : GL (Fin n ⊕ Fin n) K} :
    g ∈ StatedSp n K ↔ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.J (Fin n) K *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.J (Fin n) K := by
  rw [StatedAPI.mem_statedSp_iff, fromBlocks_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

@[expose] noncomputable def jForm (n : ℕ) (K : Type) [Field K] :
    BilinForm K (Fin n ⊕ Fin n → K) :=
  Matrix.toBilin' (Matrix.J (Fin n) K)

theorem jForm_isAlt : (jForm n K).IsAlt := by
  intro x
  simp [jForm, Matrix.toBilin'_apply', Matrix.J, dotProduct, Fintype.sum_sum_type,
    fromBlocks_mulVec, Matrix.neg_mulVec, mul_comm]

theorem jForm_nondegenerate : (jForm n K).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _
    (Matrix.isUnit_det_J (Fin n) K).ne_zero

theorem matrix_of_basis_mem_J (b : Module.Basis (Fin n ⊕ Fin n) K (Fin n ⊕ Fin n → K))
    (hb : ∀ x y, jForm n K (b x) (b y) = Matrix.J (Fin n) K x y) :
    (Matrix.of fun r c => b c r)ᵀ * Matrix.J (Fin n) K * (Matrix.of fun r c => b c r) =
      Matrix.J (Fin n) K := by
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.of fun r c => b c r with hP
  have hcol : ∀ c, P *ᵥ Pi.single c 1 = b c := fun c => by
    ext r
    simp [hP, Matrix.mulVec_single_one]
  ext x y
  have h1 := hb x y
  rw [← hcol x, ← hcol y] at h1
  have h2 := congrArg (fun B => B (Pi.single x 1) (Pi.single y 1))
    (Matrix.toBilin'_comp (Matrix.J (Fin n) K) P P)
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toBilin'_single, Matrix.toLin'_apply] at h2
  rw [← h2]
  exact h1

theorem exists_conj_blkGL (h3 : (3 : K) ≠ 0) (g : GL (Fin n ⊕ Fin n) K) (hg : g ∈ StatedSp n K)
    (hg3 : g ^ 3 = 1) :
    ∃ P : GL (Fin n ⊕ Fin n) K, P ∈ StatedSp n K ∧
      ∃ M : Fin n → Matrix.SpecialLinearGroup (Fin 2) K, g = P * blkGL M * P⁻¹ := by
  set gm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hgm
  have hgJ : gmᵀ * Matrix.J (Fin n) K * gm = Matrix.J (Fin n) K := mem_statedSp_iff_J.1 hg
  have hgm3 : gm * (gm * gm) = 1 := by
    have := congrArg (fun h : GL (Fin n ⊕ Fin n) K =>
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hg3
    simpa [pow_succ, Units.val_mul, hgm, mul_assoc] using this
  set gl : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) := Matrix.toLin' gm with hgl
  have hiso : ∀ x y, jForm n K (gl x) (gl y) = jForm n K x y := by
    intro x y
    have h := congrArg (fun B => B x y) (Matrix.toBilin'_comp (Matrix.J (Fin n) K) gm gm)
    simp only [LinearMap.BilinForm.comp_apply, hgJ] at h
    exact h
  have hgl3 : ∀ x, gl (gl (gl x)) = x := by
    intro x
    simp only [hgl, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [hgm3, Matrix.one_mulVec]
  obtain ⟨m, b, hb, hadapt⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.Sp6.exists_adapted_symplectic_basis
      h3 _ (Fin n ⊕ Fin n → K) rfl (jForm n K) jForm_isAlt jForm_nondegenerate gl hiso hgl3
  have hm : m = n := by
    have h := Module.finrank_eq_card_basis b
    simp at h
    omega
  subst hm
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.of fun r c => b c r with hP
  have hPJ : Pᵀ * Matrix.J (Fin m) K * P = Matrix.J (Fin m) K := matrix_of_basis_mem_J b hb
  have hPunit : IsUnit P.det := by
    have hPe : P = (Pi.basisFun K (Fin m ⊕ Fin m)).toMatrix b := by
      ext r c
      simp [hP, Module.Basis.toMatrix_apply]
    rw [hPe, ← Matrix.isUnit_iff_isUnit_det]
    exact @isUnit_of_invertible _ _ _ ((Pi.basisFun K (Fin m ⊕ Fin m)).invertibleToMatrix b)
  set Pg : GL (Fin m ⊕ Fin m) K := Matrix.GeneralLinearGroup.mk'' P hPunit with hPg
  have hPgval : (Pg : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = P := rfl
  have hPsp : Pg ∈ StatedSp m K := mem_statedSp_iff_J.2 (by rw [hPgval]; exact hPJ)
  choose s t u v h1 h2 using hadapt
  set M' : Fin m → Matrix (Fin 2) (Fin 2) K := fun i => !![s i, u i; t i, v i] with hM'
  have hrel : gm * P = P * blkMat M' := by
    ext r c
    rcases c with i | i
    · have e1 : (gm * P) r (Sum.inl i) = (gl (b (Sum.inl i))) r := by
        simp [Matrix.mul_apply, hgl, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hP]
      have e2 : (P * blkMat M') r (Sum.inl i) =
          (s i • b (Sum.inl i) + t i • b (Sum.inr i)) r := by
        simp [Matrix.mul_apply, Fintype.sum_sum_type, blkMat, hP, Matrix.diagonal_apply, hM',
          mul_comm]
      rw [e1, e2, h1 i]
    · have e1 : (gm * P) r (Sum.inr i) = (gl (b (Sum.inr i))) r := by
        simp [Matrix.mul_apply, hgl, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hP]
      have e2 : (P * blkMat M') r (Sum.inr i) =
          (u i • b (Sum.inl i) + v i • b (Sum.inr i)) r := by
        simp [Matrix.mul_apply, Fintype.sum_sum_type, blkMat, hP, Matrix.diagonal_apply, hM',
          mul_comm]
      rw [e1, e2, h2 i]
  have hdet : ∀ i, (M' i).det = 1 := by
    intro i
    have h := hiso (b (Sum.inl i)) (b (Sum.inr i))
    rw [h1 i, h2 i] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb] at h
    simp [Matrix.J, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂] at h
    simp [hM', Matrix.det_fin_two_of]
    linear_combination (-1 : K) * h
  let M : Fin m → Matrix.SpecialLinearGroup (Fin 2) K := fun i => ⟨M' i, hdet i⟩
  refine ⟨Pg, hPsp, M, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL, hPgval]
  exact hrel

end Conj

section Rank

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (le_pRank_centralizer_statedProj exists_lift_pow_three)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.Sp6
  (cycThree cycThree_pow_three cycThree_ne_one exists_order_three_commute)

variable {n : ℕ} {K : Type} [Field K]

theorem le_pRank_of_conj_blkGL [Finite K] (hn : 1 ≤ n) (g : StatedSp n K) (hg3 : g ^ 3 = 1)
    (P : GL (Fin n ⊕ Fin n) K) (hP : P ∈ StatedSp n K)
    (M : Fin n → Matrix.SpecialLinearGroup (Fin 2) K)
    (hgM : (g : GL (Fin n ⊕ Fin n) K) = P * blkGL M * P⁻¹) :
    n ≤ CFSG.Open.pRank 3 (Subgroup.centralizer
      ({(QuotientGroup.mk g : StatedProj (StatedSp n K))} : Set (StatedProj (StatedSp n K)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : (g : GL (Fin n ⊕ Fin n) K) = MulAut.conj P (blkGL M) := by
    rw [hgM, MulAut.conj_apply]
  have hM3 : ∀ i, M i ^ 3 = 1 := by
    have h1 : MulAut.conj P (blkGL (M ^ 3)) = MulAut.conj P (blkGL 1) := by
      rw [map_pow, map_pow, ← hconj, map_one, map_one, ← Subgroup.coe_pow, hg3]
      rfl
    have h2 := blkGL_injective ((MulAut.conj P).injective h1)
    intro i
    exact congrFun h2 i
  choose c hc3 hc1 hcM using fun i => exists_order_three_commute (hM3 i)
  have hcard : ∀ i, Nat.card (Subgroup.zpowers (c i)) = 3 := fun i => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hc3 i) (hc1 i)
  let ρ : (∀ i, Subgroup.zpowers (c i)) →* (Fin n → Matrix.SpecialLinearGroup (Fin 2) K) :=
    MonoidHom.pi fun i => (Subgroup.zpowers (c i)).subtype.comp
      (Pi.evalMonoidHom (fun j => ↥(Subgroup.zpowers (c j))) i)
  let φ : (∀ i, Subgroup.zpowers (c i)) →* GL (Fin n ⊕ Fin n) K :=
    (MulAut.conj P).toMonoidHom.comp (blkGL.comp ρ)
  have hφ_apply : ∀ a, φ a = MulAut.conj P (blkGL (ρ a)) := fun a => rfl
  have hcomm : ∀ a b : (∀ i, Subgroup.zpowers (c i)), a * b = b * a := by
    intro a b
    funext i
    exact Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative _ (a i).2 (b i).2)
  have hpow : ∀ a : (∀ i, Subgroup.zpowers (c i)), a ^ 3 = 1 := by
    intro a
    funext i
    have h := pow_card_eq_one' (G := Subgroup.zpowers (c i)) (x := a i)
    rw [hcard i] at h
    exact h
  have hA : Nat.card (∀ i, Subgroup.zpowers (c i)) = 3 ^ n := by
    rw [Nat.card_pi]
    simp [hcard]
  have hρ : Function.Injective ρ := by
    intro a a' h
    funext i
    exact Subtype.ext (congrFun h i)
  have hφ : Function.Injective φ := by
    intro a a' h
    exact hρ (blkGL_injective ((MulAut.conj P).injective h))
  have hH : ∀ a, φ a ∈ StatedSp n K := by
    intro a
    rw [hφ_apply, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hP (blkGL_mem_statedSp _))
      (Subgroup.inv_mem _ hP)
  have hsc : ∀ a, φ a ∈ StatedScalars (Fin n ⊕ Fin n) K → a = 1 := by
    intro a ha
    rw [StatedScalars, MonoidHom.mem_range] at ha
    obtain ⟨u, hu⟩ := ha
    have hsp : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) u ∈ StatedSp n K := hu ▸ hH a
    have hu2 : u ^ 2 = 1 := (StatedAPI.scalar_mem_statedSp_iff hn u).1 hsp
    have h2 : (φ a) ^ 2 = 1 := by
      rw [← hu, ← map_pow, hu2, map_one]
    have h3 : (φ a) ^ 3 = 1 := by rw [← map_pow, hpow a, map_one]
    have h1 : φ a = 1 := by
      calc φ a = (φ a) ^ 3 * ((φ a) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    exact hφ (h1.trans (map_one φ).symm)
  have hg : ∀ a, (g : GL (Fin n ⊕ Fin n) K) * φ a = φ a * (g : GL (Fin n ⊕ Fin n) K) := by
    intro a
    have hcommX : blkGL M * blkGL (ρ a) = blkGL (ρ a) * blkGL M := by
      rw [← map_mul, ← map_mul]
      congr 1
      funext i
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (a i).2
      have hk' : Commute (M i) (c i ^ k) := ((hcM i).zpow_left k).symm
      show M i * ((a i : Subgroup.zpowers (c i)) : Matrix.SpecialLinearGroup (Fin 2) K) =
        ((a i : Subgroup.zpowers (c i)) : Matrix.SpecialLinearGroup (Fin 2) K) * M i
      rw [← hk]
      exact hk'.eq
    rw [hconj, hφ_apply, ← map_mul (MulAut.conj P), ← map_mul (MulAut.conj P), hcommX]
  exact le_pRank_centralizer_statedProj hcomm hpow hA φ hφ hH hsc g hg

theorem statedSp_scalar_sq (hn : 1 ≤ n) (z : StatedSp n K)
    (hz : z ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) : z ^ 2 = 1 := by
  have hz' := Subgroup.mem_subgroupOf.1 hz
  rw [StatedScalars, MonoidHom.mem_range] at hz'
  obtain ⟨u, hu⟩ := hz'
  have hsp : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) u ∈ StatedSp n K := hu ▸ z.2
  have hu2 : u ^ 2 = 1 := (StatedAPI.scalar_mem_statedSp_iff hn u).1 hsp
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hu, ← map_pow, hu2, map_one]
  rfl

theorem le_pRank_centralizer_projSp [Finite K] (h3 : (3 : K) ≠ 0) (hn : 1 ≤ n)
    (x : StatedProj (StatedSp n K)) (hx : orderOf x = 3) :
    n ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedSp n K)))) := by
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three (H := StatedSp n K) (N := 2) (by norm_num)
    (fun z hz => statedSp_scalar_sq hn z hz) hx3
  have hg3' : (g : GL (Fin n ⊕ Fin n) K) ^ 3 = 1 := by
    have := congrArg (fun h : StatedSp n K => (h : GL (Fin n ⊕ Fin n) K)) hg3
    simpa using this
  obtain ⟨P, hP, M, hgM⟩ := exists_conj_blkGL h3 (g : GL (Fin n ⊕ Fin n) K) g.2 hg3'
  exact le_pRank_of_conj_blkGL hn g hg3 P hP M hgM

theorem le_pRank_top_projSp [Finite K] (hn : 1 ≤ n) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) := by
  have h := le_pRank_of_conj_blkGL (K := K) hn 1 (one_pow 3) 1 (one_mem _) 1 (by simp)
  exact h.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)

end Rank

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (fieldAut spLinearAutGroup spSemilinearAutGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem congr_pow_three_eq_one {G H : Type*} [Group G] [Group H] {α : MulAut G} (e : G ≃* H)
    (h : α ^ 3 = 1) : MulAut.congr e α ^ 3 = 1 := by
  rw [← map_pow, h, map_one]

theorem congr_not_mem_range_conj {G H : Type*} [Group G] [Group H] {α : MulAut G} (e : G ≃* H)
    (h : α ∉ (MulAut.conj : G →* MulAut G).range) :
    MulAut.congr e α ∉ (MulAut.conj : H →* MulAut H).range := by
  rintro ⟨k, hk⟩
  apply h
  refine ⟨e.symm k, MulEquiv.ext fun y => ?_⟩
  have h1 : k * e y * k⁻¹ = e (α (e.symm (e y))) := congrArg (fun φ : MulAut H => φ (e y)) hk
  rw [MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem pRank_map_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (A : Subgroup G) : CFSG.Open.pRank 3 (A.map e.toMonoidHom) = CFSG.Open.pRank 3 A := by
  refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map (by norm_num) e.toMonoidHom e.injective A)
  have h := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) e.symm.toMonoidHom
    e.symm.injective (A.map e.toMonoidHom)
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext; simp
  rwa [Subgroup.map_map, hid, Subgroup.map_id] at h

theorem le_pRank_fixSubgroup_fieldAut_sp {r : ℕ} (hr : 1 ≤ r) {F : Type} [Field F] [Finite F]
    {σ : F ≃+* F} (hσ : σ ^ 3 = 1) :
    r ≤ CFSG.Open.pRank 3 (fixSubgroup (fieldAut r F σ)) := by
  haveI : NeZero r := ⟨by omega⟩
  have hfix : fixSubgroup (fieldAut r F σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldInj (r := r) σ).range := by
    rw [CFSG.RankThree.PartOne.KCSpComm.range_subfieldInj,
      ← CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range (by decide : Odd 3) hσ]
    exact Subgroup.ext fun x =>
      mem_fixSubgroup.trans CFSG.RankThree.PartOne.KCSpComm.mem_spFixedGroup.symm
  rw [hfix, MonoidHom.range_eq_map]
  exact (le_pRank_top_projSp hr).trans (CFSG.SectionRank.pRank_le_map (by norm_num) _
    (CFSG.RankThree.PartOne.KCSpComm.subfieldInj_injective σ) ⊤)

theorem three_le_pRank_fixSubgroup_projSp {r : ℕ} (hr : 3 ≤ r) {F : Type} [Field F] [Finite F]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f)
    (β : MulAut (StatedProj (StatedSp r F))) (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : StatedProj (StatedSp r F) →* MulAut _).range) :
    3 ≤ CFSG.Open.pRank 3 (fixSubgroup β) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := F) (r := r) hℓ hf (by omega) hF
  have hodd : Odd (orderOf β) := (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  have hE : β ∈ spSemilinearAutGroup r F :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β ∈ spLinearAutGroup r F
  · exfalso
    have : (inner (StatedProj (StatedSp r F))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r F))).relIndex (spLinearAutGroup r F) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    exact hout (CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ)
  · have hne1 : β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have hord : orderOf β = 3 := orderOf_eq_prime hβ hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 3 Nat.prime_three β hE hD hord
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    rw [hβeq, Inputs295c.fixSubgroup_conj]
    exact (hr.trans (le_pRank_fixSubgroup_fieldAut_sp (by omega) hσ3)).trans
      (CFSG.SectionRank.pRank_le_map (by norm_num) _ h.injective _)

theorem outer295At_of_projSp {d : TauCeti.ValidLieTypeIndex} {r : ℕ} (hr : 3 ≤ r)
    (h : ∀ (K : Type) [Group K], (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (F : Type) (_ : Field F) (ℓ f : ℕ), ℓ.Prime ∧ 1 ≤ f ∧ Nat.card F = ℓ ^ f ∧
        Nonempty (K ≃* StatedProj (StatedSp r F))) :
    Inputs295c.Outer295At d := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨F, _, ℓ, f, hℓ, hf, hF, ⟨φ⟩⟩ := h K e
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hℓ.ne_zero)
  have hβ := three_le_pRank_fixSubgroup_projSp hr hℓ hf hF (MulAut.congr φ α)
    (congr_pow_three_eq_one φ hα) (congr_not_mem_range_conj φ hout)
  rw [Inputs295c.fixSubgroup_congr, pRank_map_mulEquiv] at hβ
  exact Or.inr (Or.inl hβ)

theorem inner295At_of_projSp {d : TauCeti.ValidLieTypeIndex} {r : ℕ} (hr : 4 ≤ r)
    (h : ∀ (K : Type) [Group K], (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), (3 : F) ≠ 0 ∧
        Nonempty (K ≃* StatedProj (StatedSp r F))) :
    Inputs295c.Inner295At d := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨F, _, _, h3, ⟨f⟩⟩ := h K e
  have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact Or.inr (Or.inl (hr.trans ((le_pRank_centralizer_projSp h3 (by omega) (f x) hfx).trans
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.le_pRank_centralizer_of_mulEquiv
      f x))))

theorem at_typeB_even {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hp2 : q.p = 2) (hr : 3 ≤ r) :
    Inputs295c.Outer295At ⟨.B r q, hv⟩ ∧ (4 ≤ r → Inputs295c.Inner295At ⟨.B r q, hv⟩) := by
  refine ⟨outer295At_of_projSp hr fun K _ e => ?_, fun hr4 => inner295At_of_projSp hr4
    fun K _ e => ?_⟩
  · obtain ⟨-, F, _, _, hF, hf⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 hr e
    exact ⟨F, inferInstance, q.p, q.exponent, q.prime_p, q.exponent_pos, hF, hf⟩
  · obtain ⟨-, F, _, _, hF, hf⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 hr e
    exact ⟨F, inferInstance, inferInstance,
      Inputs295c.three_ne_zero_of_card q.prime_p (by omega) hF, hf⟩

theorem at_typeC {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    (hp3 : q.p ≠ 3) :
    Inputs295c.Outer295At ⟨.C r q, hv⟩ ∧ (4 ≤ r → Inputs295c.Inner295At ⟨.C r q, hv⟩) := by
  have hr : 3 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  refine ⟨outer295At_of_projSp hr fun K _ e => ?_, fun hr4 => inner295At_of_projSp hr4
    fun K _ e => ?_⟩
  · obtain ⟨-, F, _, _, hF, hf⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    exact ⟨F, inferInstance, q.p, q.exponent, q.prime_p, q.exponent_pos, hF, hf⟩
  · obtain ⟨-, F, _, _, hF, hf⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    exact ⟨F, inferInstance, inferInstance, Inputs295c.three_ne_zero_of_card q.prime_p hp3 hF, hf⟩

end Symplectic

section Orthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus

section Planes

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_four_rotPairs [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ y, g (g (g y)) = y) :
    ∃ (c₁ c₂ c₃ c₄ : K) (u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ : V),
      IsRotPair Q c₁ u₁ v₁ ∧ IsRotPair Q c₂ u₂ v₂ ∧ IsRotPair Q c₃ u₃ v₃ ∧
      IsRotPair Q c₄ u₄ v₄ ∧
      RotMode g u₁ v₁ ∧ RotMode g u₂ v₂ ∧ RotMode g u₃ v₃ ∧ RotMode g u₄ v₄ ∧
      RotOrth Q u₁ v₁ u₂ v₂ ∧ RotOrth Q u₁ v₁ u₃ v₃ ∧ RotOrth Q u₁ v₁ u₄ v₄ ∧
      RotOrth Q u₂ v₂ u₃ v₃ ∧ RotOrth Q u₂ v₂ u₄ v₄ ∧ RotOrth Q u₃ v₃ u₄ v₄ := by
  have hS₀ : PolarNondegOn Q (⊤ : Submodule K V) := polarNondegOn_top hQ
  have hg₀ : ∀ x ∈ (⊤ : Submodule K V), g x ∈ (⊤ : Submodule K V) := fun x _ => Submodule.mem_top
  have hdim₀ : 3 ≤ Module.finrank K (⊤ : Submodule K V) := by rw [finrank_top]; omega
  obtain ⟨c₁, u₁, v₁, h₁, hu₁, hv₁, m₁⟩ := exists_rotPair_in h3 hg hg3 hS₀ hg₀ hdim₀
  have hS₁ := h₁.polarNondegOn_inf_perp2 h3 hS₀ hu₁ hv₁
  have hg₁ := m₁.stable_inf_perp2 hg hg₀
  have hf₁ := h₁.finrank_inf_perp2 h3 hu₁ hv₁
  rw [finrank_top] at hf₁
  obtain ⟨c₂, u₂, v₂, h₂, hu₂, hv₂, m₂⟩ := exists_rotPair_in h3 hg hg3 hS₁ hg₁ (by omega)
  have hS₂ := h₂.polarNondegOn_inf_perp2 h3 hS₁ hu₂ hv₂
  have hg₂ := m₂.stable_inf_perp2 hg hg₁
  have hf₂ := h₂.finrank_inf_perp2 h3 hu₂ hv₂
  obtain ⟨c₃, u₃, v₃, h₃, hu₃, hv₃, m₃⟩ := exists_rotPair_in h3 hg hg3 hS₂ hg₂ (by omega)
  have hS₃ := h₃.polarNondegOn_inf_perp2 h3 hS₂ hu₃ hv₃
  have hg₃ := m₃.stable_inf_perp2 hg hg₂
  have hf₃ := h₃.finrank_inf_perp2 h3 hu₃ hv₃
  obtain ⟨c₄, u₄, v₄, h₄, hu₄, hv₄, m₄⟩ := exists_rotPair_in h3 hg hg3 hS₃ hg₃ (by omega)
  have a₂ : u₂ ∈ perp2 Q u₁ v₁ ∧ v₂ ∈ perp2 Q u₁ v₁ :=
    ⟨(Submodule.mem_inf.1 hu₂).2, (Submodule.mem_inf.1 hv₂).2⟩
  have a₃ : u₃ ∈ perp2 Q u₂ v₂ ∧ v₃ ∈ perp2 Q u₂ v₂ :=
    ⟨(Submodule.mem_inf.1 hu₃).2, (Submodule.mem_inf.1 hv₃).2⟩
  have a₃' : u₃ ∈ perp2 Q u₁ v₁ ∧ v₃ ∈ perp2 Q u₁ v₁ :=
    ⟨(Submodule.mem_inf.1 (Submodule.mem_inf.1 hu₃).1).2,
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 hv₃).1).2⟩
  have a₄ : u₄ ∈ perp2 Q u₃ v₃ ∧ v₄ ∈ perp2 Q u₃ v₃ :=
    ⟨(Submodule.mem_inf.1 hu₄).2, (Submodule.mem_inf.1 hv₄).2⟩
  have a₄' : u₄ ∈ perp2 Q u₂ v₂ ∧ v₄ ∈ perp2 Q u₂ v₂ :=
    ⟨(Submodule.mem_inf.1 (Submodule.mem_inf.1 hu₄).1).2,
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 hv₄).1).2⟩
  have a₄'' : u₄ ∈ perp2 Q u₁ v₁ ∧ v₄ ∈ perp2 Q u₁ v₁ :=
    ⟨(Submodule.mem_inf.1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hu₄).1).1).2,
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hv₄).1).1).2⟩
  exact ⟨c₁, c₂, c₃, c₄, u₁, v₁, u₂, v₂, u₃, v₃, u₄, v₄, h₁, h₂, h₃, h₄, m₁, m₂, m₃, m₄,
    RotOrth.of_mem_perp2 a₂.1 a₂.2, RotOrth.of_mem_perp2 a₃'.1 a₃'.2,
    RotOrth.of_mem_perp2 a₄''.1 a₄''.2, RotOrth.of_mem_perp2 a₃.1 a₃.2,
    RotOrth.of_mem_perp2 a₄'.1 a₄'.2, RotOrth.of_mem_perp2 a₄.1 a₄.2⟩

end Planes

section Quad

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def quadHom (t₁ t₂ t₃ t₄ : G) (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1) (h₃ : t₃ ^ 3 = 1)
    (h₄ : t₄ ^ 3 = 1) (c₁₂ : Commute t₁ t₂) (c₁₃ : Commute t₁ t₃) (c₁₄ : Commute t₁ t₄)
    (c₂₃ : Commute t₂ t₃) (c₂₄ : Commute t₂ t₄) (c₃₄ : Commute t₃ t₄) :
    Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3)) →* G :=
  (powHom t₁ h₁).noncommCoprod (cubeHom t₂ t₃ t₄ h₂ h₃ h₄ c₂₃ c₂₄ c₃₄)
    fun a p => (c₁₂.pow_pow _ _).mul_right ((c₁₃.pow_pow _ _).mul_right (c₁₄.pow_pow _ _))

theorem quadHom_apply (t₁ t₂ t₃ t₄ : G) (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1) (h₃ : t₃ ^ 3 = 1)
    (h₄ : t₄ ^ 3 = 1) (c₁₂ : Commute t₁ t₂) (c₁₃ : Commute t₁ t₃) (c₁₄ : Commute t₁ t₄)
    (c₂₃ : Commute t₂ t₃) (c₂₄ : Commute t₂ t₄) (c₃₄ : Commute t₃ t₄)
    (a b c d : Multiplicative (ZMod 3)) :
    quadHom t₁ t₂ t₃ t₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ (a, b, c, d) =
      t₁ ^ a.toAdd.val * (t₂ ^ b.toAdd.val * (t₃ ^ c.toAdd.val * t₄ ^ d.toAdd.val)) := rfl

theorem quadHom_injective (t₁ t₂ t₃ t₄ : G) (h₁ : t₁ ^ 3 = 1) (h₂ : t₂ ^ 3 = 1)
    (h₃ : t₃ ^ 3 = 1) (h₄ : t₄ ^ 3 = 1) (c₁₂ : Commute t₁ t₂) (c₁₃ : Commute t₁ t₃)
    (c₁₄ : Commute t₁ t₄) (c₂₃ : Commute t₂ t₃) (c₂₄ : Commute t₂ t₄) (c₃₄ : Commute t₃ t₄)
    (x₁ x₂ x₃ x₄ : X) (n₁ : t₁ • x₁ ≠ x₁) (n₂ : t₂ • x₂ ≠ x₂) (n₃ : t₃ • x₃ ≠ x₃)
    (n₄ : t₄ • x₄ ≠ x₄) (f₁₂ : t₂ • x₁ = x₁) (f₁₃ : t₃ • x₁ = x₁) (f₁₄ : t₄ • x₁ = x₁)
    (f₂₁ : t₁ • x₂ = x₂) (f₂₃ : t₃ • x₂ = x₂) (f₂₄ : t₄ • x₂ = x₂)
    (f₃₁ : t₁ • x₃ = x₃) (f₃₂ : t₂ • x₃ = x₃) (f₃₄ : t₄ • x₃ = x₃)
    (f₄₁ : t₁ • x₄ = x₄) (f₄₂ : t₂ • x₄ = x₄) (f₄₃ : t₃ • x₄ = x₄) :
    Function.Injective (quadHom t₁ t₂ t₃ t₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, c, d⟩ habcd
  have hval : ∀ (z : Multiplicative (ZMod 3)), z.toAdd.val < 3 := fun z => ZMod.val_lt _
  have hzero : ∀ (z : Multiplicative (ZMod 3)), z.toAdd.val = 0 → z = 1 := fun z hz =>
    toAdd_eq_zero.1 ((ZMod.val_eq_zero z.toAdd).1 hz)
  rw [quadHom_apply] at habcd
  have ha : a = 1 := by
    apply hzero
    refine eq_zero_of_pow_smul h₁ n₁ (hval a) ?_
    have := congrArg (fun k : G => k • x₁) habcd
    simp only [mul_smul, one_smul] at this
    rwa [pow_smul_eq_self' f₁₄, pow_smul_eq_self' f₁₃, pow_smul_eq_self' f₁₂] at this
  have hrest : cubeHom t₂ t₃ t₄ h₂ h₃ h₄ c₂₃ c₂₄ c₃₄ (b, c, d) = 1 := by
    rw [cubeHom_apply]
    rw [ha] at habcd
    simpa using habcd
  have hbcd := cubeHom_injective (X := X) t₂ t₃ t₄ h₂ h₃ h₄ c₂₃ c₂₄ c₃₄ x₂ x₃ x₄ n₂ n₃ n₄
    f₂₃ f₂₄ f₃₂ f₃₄ f₄₂ f₄₃ (hrest.trans (map_one _).symm)
  rw [ha, hbcd]
  rfl

end Quad

section Hom

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_injective_hom_four [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) :
    ∃ φ : Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ×
        Multiplicative (ZMod 3)) →* (V ≃ₗ[K] V), Function.Injective φ ∧
      (∀ a, φ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧ ∀ a, φ a * g = g * φ a := by
  have hg3' : ∀ y, g (g (g y)) = y := fun y => by
    have h := congrArg (fun f : V ≃ₗ[K] V => f y) hg3
    simpa [pow_succ] using h
  obtain ⟨c₁, c₂, c₃, c₄, u₁, v₁, u₂, v₂, u₃, v₃, u₄, v₄, h₁, h₂, h₃, h₄, m₁, m₂, m₃, m₄,
    o₁₂, o₁₃, o₁₄, o₂₃, o₂₄, o₃₄⟩ := exists_four_rotPairs h3 hQ hdim hg hg3'
  have p₁ := h₁.rotAut_pow_three
  have p₂ := h₂.rotAut_pow_three
  have p₃ := h₃.rotAut_pow_three
  have p₄ := h₄.rotAut_pow_three
  have k₁₂ : Commute h₁.rotAut h₂.rotAut :=
    h₁.rotAut_comm_rotAut h₂ o₁₂.uu o₁₂.uv o₁₂.vu o₁₂.vv
  have k₁₃ : Commute h₁.rotAut h₃.rotAut :=
    h₁.rotAut_comm_rotAut h₃ o₁₃.uu o₁₃.uv o₁₃.vu o₁₃.vv
  have k₁₄ : Commute h₁.rotAut h₄.rotAut :=
    h₁.rotAut_comm_rotAut h₄ o₁₄.uu o₁₄.uv o₁₄.vu o₁₄.vv
  have k₂₃ : Commute h₂.rotAut h₃.rotAut :=
    h₂.rotAut_comm_rotAut h₃ o₂₃.uu o₂₃.uv o₂₃.vu o₂₃.vv
  have k₂₄ : Commute h₂.rotAut h₄.rotAut :=
    h₂.rotAut_comm_rotAut h₄ o₂₄.uu o₂₄.uv o₂₄.vu o₂₄.vv
  have k₃₄ : Commute h₃.rotAut h₄.rotAut :=
    h₃.rotAut_comm_rotAut h₄ o₃₄.uu o₃₄.uv o₃₄.vu o₃₄.vv
  refine ⟨quadHom h₁.rotAut h₂.rotAut h₃.rotAut h₄.rotAut p₁ p₂ p₃ p₄ k₁₂ k₁₃ k₁₄ k₂₃ k₂₄ k₃₄,
    ?_, ?_, ?_⟩
  · refine quadHom_injective (X := V) h₁.rotAut h₂.rotAut h₃.rotAut h₄.rotAut p₁ p₂ p₃ p₄
      k₁₂ k₁₃ k₁₄ k₂₃ k₂₄ k₃₄ u₁ u₂ u₃ u₄ (h₁.rotAut_ne h3) (h₂.rotAut_ne h3) (h₃.rotAut_ne h3)
      (h₄.rotAut_ne h3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h₂.rotAut_of_perp o₁₂.symm.uu o₁₂.symm.vu
    · exact h₃.rotAut_of_perp o₁₃.symm.uu o₁₃.symm.vu
    · exact h₄.rotAut_of_perp o₁₄.symm.uu o₁₄.symm.vu
    · exact h₁.rotAut_of_perp o₁₂.uu o₁₂.vu
    · exact h₃.rotAut_of_perp o₂₃.symm.uu o₂₃.symm.vu
    · exact h₄.rotAut_of_perp o₂₄.symm.uu o₂₄.symm.vu
    · exact h₁.rotAut_of_perp o₁₃.uu o₁₃.vu
    · exact h₂.rotAut_of_perp o₂₃.uu o₂₃.vu
    · exact h₄.rotAut_of_perp o₃₄.symm.uu o₃₄.symm.vu
    · exact h₁.rotAut_of_perp o₁₄.uu o₁₄.vu
    · exact h₂.rotAut_of_perp o₂₄.uu o₂₄.vu
    · exact h₃.rotAut_of_perp o₃₄.uu o₃₄.vu
  · rintro ⟨a, b, c, d⟩
    rw [quadHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ h₁.rotAut_mem_orthogonalGroup _)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ h₂.rotAut_mem_orthogonalGroup _)
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ h₃.rotAut_mem_orthogonalGroup _)
          (Subgroup.pow_mem _ h₄.rotAut_mem_orthogonalGroup _)))
  · rintro ⟨a, b, c, d⟩
    rw [quadHom_apply]
    have e₁ : Commute h₁.rotAut g := h₁.rotAut_comm_of_mode hg m₁
    have e₂ : Commute h₂.rotAut g := h₂.rotAut_comm_of_mode hg m₂
    have e₃ : Commute h₃.rotAut g := h₃.rotAut_comm_of_mode hg m₃
    have e₄ : Commute h₄.rotAut g := h₄.rotAut_comm_of_mode hg m₄
    exact ((e₁.pow_left _).mul_left ((e₂.pow_left _).mul_left
      ((e₃.pow_left _).mul_left (e₄.pow_left _)))).eq

end Hom

theorem four_le_pRank_centralizer_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (h3 : (3 : K) ≠ 0) {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ0 : ⇑Q = Q₀) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hdim : 9 ≤ Fintype.card ι) (x : StatedProj (StatedOmega Q₀)) (hx : orderOf x = 3) :
    4 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedOmega Q₀)))) := by
  classical
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, Q v₀ ≠ 0 := by
    have hne : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨m, hm0⟩ := exists_ne (0 : ι → K)
    obtain ⟨n, -, hn⟩ := exists_mem_map_ne_zero (Q := Q) (polarNondegOn_top hnd)
      (Submodule.mem_top (x := m)) hm0
    exact ⟨n, hn⟩
  have hΩO : ∀ A : GL ι K, A ∈ StatedOmega Q₀ →
      toLinEquiv ι K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun A hA =>
    toLinEquiv_mem_orthogonalGroup hQ0 hA
  have hZ : ∀ z ∈ (StatedScalars ι K).subgroupOf (StatedOmega Q₀), z ^ 2 = 1 := by
    intro z hz
    have hzs := Subgroup.mem_subgroupOf.1 hz
    exact Subtype.ext (scalar_sq_eq_one hv₀ hzs (hΩO _ z.2))
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨g, hg3, hgx⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.exists_lift_pow_three (N := 2)
      (by norm_num) hZ hx3
  have hg3' : (g : GL ι K) ^ 3 = 1 := by
    have := congrArg Subtype.val hg3
    simpa using this
  set ĝ := toLinEquiv ι K (g : GL ι K) with hĝ
  have hĝO : ĝ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hΩO _ g.2
  have hĝ3 : ĝ ^ 3 = 1 := by rw [hĝ, ← map_pow, hg3', map_one]
  have hdim' : 9 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hdim
  obtain ⟨φ₀, hinj, hφO, hφcomm⟩ := exists_injective_hom_four h3 hnd hdim' hĝO hĝ3
  let φ : Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3)) →* GL ι K :=
    (toLinEquiv ι K).symm.toMonoidHom.comp φ₀
  have hφ_apply : ∀ a, toLinEquiv ι K (φ a) = φ₀ a := fun a => by simp [φ]
  have hφinj : Function.Injective φ := (toLinEquiv ι K).symm.injective.comp hinj
  have hpowA : ∀ a : Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3) × Multiplicative (ZMod 3)), a ^ 3 = 1 := by decide
  have hcommA : ∀ a b : Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3) × Multiplicative (ZMod 3)), a * b = b * a := fun a b => mul_comm a b
  have hcardA : Nat.card (Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) = 3 ^ 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hH : ∀ a, φ a ∈ StatedOmega Q₀ := by
    intro a
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hφ_apply]
    obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
    refine hodd (φ₀ a) (hφO a) ?_
    have : orderOf (φ₀ a) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpowA a, map_one])
    exact Odd.of_dvd_nat (by decide) this
  have hsc : ∀ a, φ a ∈ StatedScalars ι K → a = 1 := by
    intro a ha
    have hsq : φ a ^ 2 = 1 := scalar_sq_eq_one hv₀ ha (by rw [hφ_apply]; exact hφO a)
    have hcube : φ a ^ 3 = 1 := by rw [← map_pow, hpowA a, map_one]
    have h1 : φ a = 1 := by
      have e : φ a = φ a ^ 3 * (φ a ^ 2)⁻¹ := by group
      rw [e, hcube, hsq]
      simp
    exact hφinj (h1.trans (map_one φ).symm)
  have hg : ∀ a, (g : GL ι K) * φ a = φ a * (g : GL ι K) := by
    intro a
    apply (toLinEquiv ι K).injective
    rw [map_mul, map_mul, hφ_apply]
    exact (hφcomm a).symm
  have key := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.le_pRank_centralizer_statedProj
    hcommA hpowA hcardA φ hφinj hH hsc g hg
  rw [hgx] at key
  exact key

theorem inner295At_of_statedOmega {d : TauCeti.ValidLieTypeIndex}
    (h : ∀ (K : Type) [Group K], (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (F : Type) (_ : Field F) (_ : Finite F)
        (Q : QuadraticForm F (ι → F)) (Q₀ : (ι → F) → F), (3 : F) ≠ 0 ∧ ⇑Q = Q₀ ∧
        (polarBilin Q).Nondegenerate ∧
        (∃ T : Submodule F (ι → F), Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) ∧
        9 ≤ Fintype.card ι ∧ Nonempty (K ≃* StatedProj (StatedOmega Q₀))) :
    Inputs295c.Inner295At d := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨ι, _, _, F, _, _, Q, Q₀, h3, hQ0, hnd, hT, hdim, ⟨f⟩⟩ := h K e
  have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact Or.inr (Or.inl ((four_le_pRank_centralizer_statedOmega h3 hQ0 hnd hT hdim (f x) hfx).trans
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.le_pRank_centralizer_of_mulEquiv
      f x)))

theorem inner295At_typeD {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (hp3 : q.p ≠ 3) (hr : 5 ≤ r) : Inputs295c.Inner295At ⟨.D r q, hv⟩ := by
  refine inner295At_of_statedOmega fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, hf⟩ := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  obtain ⟨hnd, hT⟩ := regular_quadPlus (K := F) (n := r) (by omega)
  exact ⟨Fin r ⊕ Fin r, inferInstance, inferInstance, F, inferInstance, inferInstance,
    CFSG.LieType.Universal.Spin.quadPlus r F, StatedQuadPlus r F,
    Inputs295c.three_ne_zero_of_card q.prime_p hp3 hF,
    CFSG.LieType.Universal.Spin.coe_quadPlus r F, hnd, hT, by simp; omega, hf⟩

theorem inner295At_typeTwistedD {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hp3 : q.p ≠ 3) (hr : 5 ≤ r) :
    Inputs295c.Inner295At ⟨.twistedD r q, hv⟩ := by
  refine inner295At_of_statedOmega fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, b, c, hirr, hf⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  obtain ⟨hnd, hT⟩ := regular_quadMinus (K := F) (n := r) (b := b) (c := c) (by omega) hirr
  exact ⟨Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2, inferInstance, inferInstance, F, inferInstance,
    inferInstance, CFSG.LieType.Universal.Spin.quadMinus r F b c, StatedQuadMinus r F b c,
    Inputs295c.three_ne_zero_of_card q.prime_p hp3 hF,
    CFSG.LieType.Universal.Spin.coe_quadMinus r F b c, hnd, hT, by simp; omega, hf⟩

theorem inner295At_typeB_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hp2 : q.p ≠ 2) (hp3 : q.p ≠ 3) (hr : 4 ≤ r) :
    Inputs295c.Inner295At ⟨.B r q, hv⟩ := by
  refine inner295At_of_statedOmega fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, hf⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 (by omega) e
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hc := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hF
    have hq : (ringChar F).Prime := hc ▸ q.prime_p
    exact hp2 (hc ▸ (CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hq).1 h)
  obtain ⟨hnd, hT⟩ := regular_quadOdd (K := F) (n := r) h2 (by omega)
  exact ⟨Fin r ⊕ Fin r ⊕ Unit, inferInstance, inferInstance, F, inferInstance, inferInstance,
    CFSG.LieType.Universal.Spin.quadOdd r F, StatedQuadOdd r F,
    Inputs295c.three_ne_zero_of_card q.prime_p hp3 hF,
    CFSG.LieType.Universal.Spin.coe_quadOdd r F, hnd, hT, by simp; omega, hf⟩

end Orthogonal

section Unitary

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.RankFourTheoremC.TorusU
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (le_pRank_centralizer_statedProj exists_lift_pow_three)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossUni

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K} {ζ : K} {p n : ℕ}

@[expose] def torusHom4 (χ : Multiplicative (ZMod p) →* K) (i0 i1 i2 i3 i4 : Fin n) :
    (Fin 4 → Multiplicative (ZMod p)) →* (Fin n → K) where
  toFun x := Pi.mulSingle i0 (χ (x 0)) * Pi.mulSingle i1 (χ (x 1)) *
    Pi.mulSingle i2 (χ (x 2)) * Pi.mulSingle i3 (χ (x 3)) *
    Pi.mulSingle i4 (χ (x 0 * x 1 * x 2 * x 3)⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have e : (x 0 * y 0) * (x 1 * y 1) * (x 2 * y 2) * (x 3 * y 3) =
        (x 0 * x 1 * x 2 * x 3) * (y 0 * y 1 * y 2 * y 3) := by ac_rfl
    simp only [Pi.mul_apply, map_mul, Pi.mulSingle_mul, e, mul_inv]
    ring

theorem exists_torusHom_rank4 (hσ : IsUnitaryInvolution σ) (hp : p.Prime) (hp5 : p ≠ 5)
    (hζ : IsPrimitiveRoot ζ p) (hσζ : σ ζ = ζ⁻¹) (hn : 5 ≤ n) (s : GL (Fin n) K)
    (hsiso : conjTr σ (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1)
    (hs : s ^ p = 1) :
    ∃ F : (Fin 4 → Multiplicative (ZMod p)) →* SUid σ n,
      Function.Injective F ∧
      (∀ x, s * ((F x : SUid σ n) : GL (Fin n) K) = ((F x : SUid σ n) : GL (Fin n) K) * s) ∧
      ∀ x, ((F x : SUid σ n) : GL (Fin n) K) ∈ StatedScalars (Fin n) K → F x = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : K) ≠ 0 := (hζ.neZero').out
  set sM : Matrix (Fin n) (Fin n) K := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hsM
  have hspow : sM ^ p = 1 := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hs
    simpa [hsM] using this
  have hSp : (Matrix.toLin' sM) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hspow, Matrix.toLin'_one]
    rfl
  have hS : ∀ x y, herm σ (Matrix.toLin' sM x) (Matrix.toLin' sM y) = herm σ x y := by
    intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_mulVec, hsiso, Matrix.one_mulVec]
  obtain ⟨b, u, hb, hu⟩ := exists_orthonormal_eigenbasis hσ hζ hp.pos hp0 hσζ hSp hS
  have hu' : ∀ i, sM *ᵥ b i = u i • b i := fun i => by
    rw [← Matrix.toLin'_apply]
    exact hu i
  have hP : conjTr σ (colMatrix b) * colMatrix b = 1 := conjTr_colMatrix_mul_self hb
  have hsP : sM * colMatrix b = colMatrix b * diagonal u := mul_colMatrix hu'
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let i4 : Fin n := ⟨4, by omega⟩
  set T := torusHom4 (charHom hζ) i0 i1 i2 i3 i4
  have hTx : ∀ x j, T x j = (Pi.mulSingle i0 (charHom hζ (x 0)) : Fin n → K) j *
      (Pi.mulSingle i1 (charHom hζ (x 1)) : Fin n → K) j *
        (Pi.mulSingle i2 (charHom hζ (x 2)) : Fin n → K) j *
          (Pi.mulSingle i3 (charHom hζ (x 3)) : Fin n → K) j *
            (Pi.mulSingle i4 (charHom hζ (x 0 * x 1 * x 2 * x 3)⁻¹) : Fin n → K) j :=
    fun x j => rfl
  have hms : ∀ (i j : Fin n) (a : K), σ a * a = 1 →
      σ ((Pi.mulSingle i a : Fin n → K) j) * (Pi.mulSingle i a : Fin n → K) j = 1 := by
    intro i j a ha
    by_cases h : j = i
    · subst h
      simpa using ha
    · simp [Pi.mulSingle_eq_of_ne h]
  have hmul : ∀ a b : K, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := by
    intro a b ha hb
    rw [map_mul]
    calc σ a * σ b * (a * b) = (σ a * a) * (σ b * b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  have hT : ∀ x j, σ (T x j) * T x j = 1 := by
    intro x j
    rw [hTx]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hms _ _ _ (norm_charHom hζ hσζ _))
      (hms _ _ _ (norm_charHom hζ hσζ _))) (hms _ _ _ (norm_charHom hζ hσζ _)))
      (hms _ _ _ (norm_charHom hζ hσζ _))) (hms _ _ _ (norm_charHom hζ hσζ _))
  have hdet : ∀ x, ∏ j, T x j = 1 := by
    intro x
    simp only [hTx, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨F, hF⟩ := exists_hom_conjDiag hσ.invol hP T hT hdet
  have hne : ∀ a b : Fin n, a.val ≠ b.val → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  have hone : ∀ (i j : Fin n) (a : K), j ≠ i → (Pi.mulSingle i a : Fin n → K) j = 1 :=
    fun i j a h => by simp [Pi.mulSingle_apply, h]
  have hT0 : ∀ x, T x i0 = charHom hζ (x 0) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i1 i0 _ (hne _ _ (by simp [i0, i1])),
      hone i2 i0 _ (hne _ _ (by simp [i0, i2])), hone i3 i0 _ (hne _ _ (by simp [i0, i3])),
      hone i4 i0 _ (hne _ _ (by simp [i0, i4]))]
    simp
  have hT1 : ∀ x, T x i1 = charHom hζ (x 1) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i0 i1 _ (hne _ _ (by simp [i0, i1])),
      hone i2 i1 _ (hne _ _ (by simp [i1, i2])), hone i3 i1 _ (hne _ _ (by simp [i1, i3])),
      hone i4 i1 _ (hne _ _ (by simp [i1, i4]))]
    simp
  have hT2 : ∀ x, T x i2 = charHom hζ (x 2) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i0 i2 _ (hne _ _ (by simp [i0, i2])),
      hone i1 i2 _ (hne _ _ (by simp [i1, i2])), hone i3 i2 _ (hne _ _ (by simp [i2, i3])),
      hone i4 i2 _ (hne _ _ (by simp [i2, i4]))]
    simp
  have hT3 : ∀ x, T x i3 = charHom hζ (x 3) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i0 i3 _ (hne _ _ (by simp [i0, i3])),
      hone i1 i3 _ (hne _ _ (by simp [i1, i3])), hone i2 i3 _ (hne _ _ (by simp [i2, i3])),
      hone i4 i3 _ (hne _ _ (by simp [i3, i4]))]
    simp
  have hT4 : ∀ x, T x i4 = charHom hζ (x 0 * x 1 * x 2 * x 3)⁻¹ := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i0 i4 _ (hne _ _ (by simp [i0, i4])),
      hone i1 i4 _ (hne _ _ (by simp [i1, i4])), hone i2 i4 _ (hne _ _ (by simp [i2, i4])),
      hone i3 i4 _ (hne _ _ (by simp [i3, i4]))]
    simp
  refine ⟨F, (injective_iff_map_eq_one F).mpr fun x hx => ?_, fun x => ?_, fun x hx => ?_⟩
  · have h1 : conjDiag σ (colMatrix b) (T x) = 1 := by
      rw [← hF x, hx]
      rfl
    have h2 := eq_one_of_conjDiag_eq_one hP h1
    have e0 : x 0 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT0 x]; exact h2 i0)
    have e1 : x 1 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT1 x]; exact h2 i1)
    have e2 : x 2 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT2 x]; exact h2 i2)
    have e3 : x 3 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT3 x]; exact h2 i3)
    funext k
    fin_cases k
    exacts [e0, e1, e2, e3]
  · apply Units.ext
    simp only [Units.val_mul]
    rw [hF x]
    exact commute_conjDiag hP hsP _
  · obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx
    have h1 : Matrix.scalar (Fin n) (c : K) = conjDiag σ (colMatrix b) (T x) := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
      simpa [hF x] using this
    have h2 : diagonal (T x) = diagonal fun _ => (c : K) := by
      rw [diagonal_eq_conjDiag hP, ← h1, Matrix.scalar_apply, ← smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP]
    have h3 : ∀ j, T x j = c := fun j => by
      have := congrFun (congrFun h2 j) j
      simpa using this
    have e0 : charHom hζ (x 0) = c := (hT0 x).symm.trans (h3 i0)
    have e1 : charHom hζ (x 1) = c := (hT1 x).symm.trans (h3 i1)
    have e2 : charHom hζ (x 2) = c := (hT2 x).symm.trans (h3 i2)
    have e3 : charHom hζ (x 3) = c := (hT3 x).symm.trans (h3 i3)
    have e4 : charHom hζ (x 0 * x 1 * x 2 * x 3)⁻¹ = c := (hT4 x).symm.trans (h3 i4)
    have hcp : (c : K) ^ p = 1 := by
      rw [← e0, ← map_pow, pow_prime_eq_one_zmod, map_one]
    have hc5 : (c : K) ^ 5 = 1 := by
      have h0 : ((c : K) * c * c * c) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero c.ne_zero c.ne_zero) c.ne_zero) c.ne_zero
      have h4 := e4
      rw [map_inv, map_mul, map_mul, map_mul, e0, e1, e2, e3] at h4
      calc (c : K) ^ 5 = (c : K) * ((c : K) * c * c * c) := by ring
        _ = ((c : K) * c * c * c)⁻¹ * ((c : K) * c * c * c) := by rw [h4]
        _ = 1 := inv_mul_cancel₀ h0
    have hcop : Nat.Coprime p 5 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
    have hc1 : c = 1 := Units.ext (by
      have := pow_gcd_eq_one.2 ⟨hcp, hc5⟩
      rwa [hcop.gcd_eq_one, pow_one] at this)
    apply Subtype.ext
    apply Units.ext
    show (((F x : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [hF x, ← h1, hc1]
    simp

end Torus

theorem three_le_pRank_top_projSU {K : Type} [Field K] [Finite K] {Q n : ℕ}
    (hK : Nat.card K = Q ^ 2) (hQ3 : ¬ 3 ∣ Q)
    (hn : (3 ∣ Q + 1 ∧ 4 ≤ n) ∨ (¬ 3 ∣ Q + 1 ∧ 6 ≤ n)) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n Q K))) := by
  obtain ⟨r, f, hr, hchar, rfl⟩ := exists_prime_pow_of_card_sq hK
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  have hσ : IsUnitaryInvolution (unitaryInvolution K r f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hq : 1 < r ^ f := one_lt_pow_of_card hK
  have h1S : (1 : StatedSU n (r ^ f) K) ^ 3 = 1 := one_pow 3
  have hsiso : conjTr (unitaryInvolution K r f)
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
    simp [conjTr]
  have hs : (1 : GL (Fin n) K) ^ 3 = 1 := one_pow 3
  have hfin : ∀ {k : ℕ} (F : (Fin k → Multiplicative (ZMod 3)) →* SUid (unitaryInvolution K r f) n),
      Function.Injective F →
      (∀ x, ((F x : SUid (unitaryInvolution K r f) n) : GL (Fin n) K) ∈
        StatedScalars (Fin n) K → F x = 1) →
      k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (r ^ f) K))) := by
    intro k F hFi hFs
    have hA : Nat.card (Fin k → Multiplicative (ZMod 3)) = 3 ^ k := by
      simp [Nat.card_eq_fintype_card]
    have h := le_pRank_centralizer_statedProj (H := StatedSU n (r ^ f) K)
      (A := Fin k → Multiplicative (ZMod 3)) (k := k) (fun a b => mul_comm a b)
      (fun a => funext fun i => pow_prime_eq_one_zmod (a i)) hA
      ((SUid (unitaryInvolution K r f) n).subtype.comp F)
      ((SUid (unitaryInvolution K r f) n).subtype_injective.comp hFi)
      (fun a => by
        rw [← SUid_eq_statedSU hK n]
        exact (F a).2)
      (fun a ha => hFi (by rw [hFs a ha, map_one])) 1 (fun a => by simp)
    exact h.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)
  rcases hn with ⟨h3, hn4⟩ | ⟨h3, hn6⟩
  · have hcard : 3 ∣ Nat.card Kˣ := by
      rw [card_units_of_card hK, sq_sub_one_eq _ hq.le]
      exact Dvd.dvd.mul_right h3 _
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hcard
    have hσζ : unitaryInvolution K r f ζ = ζ⁻¹ := by
      rw [unitaryInvolution_apply]
      have h1 : ζ ^ (r ^ f + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).2 h3
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
    · obtain ⟨F, hFi, -, hFs⟩ := exists_torusHom_four hσ Nat.prime_three (by norm_num) hζ hσζ
        (1 : GL (Fin 4) K) hsiso hs
      exact hfin F hFi hFs
    · obtain ⟨F, hFi, -, hFs⟩ := exists_torusHom_rank4 hσ Nat.prime_three (by norm_num) hζ hσζ
        hn5 (1 : GL (Fin n) K) hsiso hs
      exact (hfin F hFi hFs).trans' (by norm_num)
  · obtain ⟨m, hm⟩ : ∃ m, r ^ f = 3 * m + 1 := ⟨(r ^ f) / 3, by omega⟩
    have hcard : 3 ∣ Nat.card Kˣ := by
      rw [card_units_of_card hK, sq_sub_one_eq _ hq.le]
      exact Dvd.dvd.mul_left (by omega) _
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hcard
    have hσζ : unitaryInvolution K r f ζ = ζ := by
      rw [unitaryInvolution_apply, hm, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    have hnorm : ∀ c : K, c ^ 3 = 1 → unitaryInvolution K r f c * c = 1 → c = 1 := by
      intro c hc3 hcq
      rw [unitaryInvolution_apply, ← pow_succ] at hcq
      have h1 := pow_gcd_eq_one.2 ⟨hc3, hcq⟩
      rwa [((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).gcd_eq_one, pow_one] at h1
    have hSp : (Matrix.toLin' ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ 3 = 1 := by
      rw [Units.val_one, Matrix.toLin'_one, ← Module.End.one_eq_id, one_pow]
    have hS : ∀ x y, herm (unitaryInvolution K r f)
        (Matrix.toLin' ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x)
        (Matrix.toLin' ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y) =
        herm (unitaryInvolution K r f) x y := by
      intro x y
      simp
    obtain ⟨u, w, hpairs⟩ := exists_hypPairs hσ hζ hσζ hSp hS 3 (by omega)
    obtain ⟨F, hFi, -, hFs⟩ := exists_torusHom_pairs hσ.invol hζ hnorm
      (1 : GL (Fin n) K) hsiso hs hpairs
    exact hfin F hFi hFs

theorem mod_three_cube (q₀ : ℕ) : q₀ ^ 3 % 3 = q₀ % 3 := by
  have h := Nat.mod_lt q₀ (by norm_num : 0 < 3)
  rw [Nat.pow_mod]
  interval_cases hq : q₀ % 3 <;> norm_num

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel in
theorem three_le_pRank_fixSubgroup_primeFormP {ℓ f n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ ≠ 3) (hg : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1))
    (hn : (3 ∣ ℓ ^ f + 1 ∧ 4 ≤ n) ∨ (¬ 3 ∣ ℓ ^ f + 1 ∧ 6 ≤ n))
    (β : MulAut (primeFormP h (idGram K n))) (hβ3 : β ^ 3 = 1)
    (hβo : β ∉ (MulAut.conj : primeFormP h (idGram K n) →* MulAut _).range) :
    3 ≤ CFSG.Open.pRank 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hne : ¬ (n = 3 ∧ ℓ ^ f = 2) := by omega
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn3 hne β with hσdef
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hD : β ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hne]
      exact h1
    exact hβo (CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn3 hne
      Nat.prime_three hg hD hβ3)
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβ3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hβ1 : β ≠ 1 := fun h1 => hβo ⟨1, by rw [h1, map_one]⟩
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne
      Nat.prime_three (by norm_num) (Ne.symm hℓ3) β hβord σ rfl hσord
  have hβeq : β = primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one σ *
      (primeFormConjHom h _ M)⁻¹ := by
    rw [← hM]
    group
  have hZ : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (by omega)]
    exact hg
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -⟩ :=
    CFSG.RankThree.Classical.prime_subfield_fixed_group_package h Nat.prime_three (by norm_num)
      hσord n hn3 hne hZ
  set h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three
    (by norm_num) hσord with hh₀
  haveI := h₀.finite
  have hmod : StatedClassicalModel (primeFormP h₀ ((1 : GL (Fin n)
      (CFSG.LieType.Chevalley.fixSubfield σ)) : Matrix (Fin n) (Fin n)
        (CFSG.LieType.Chevalley.fixSubfield σ))) .PSU n ℓ (f / 3) := by
    refine ⟨⟨h.prime, h₀.one_le, hn3, fun he => by simp only [Prod.mk.injEq] at he; omega⟩,
      CFSG.LieType.Chevalley.fixSubfield σ, inferInstance, inferInstance, ?_,
      ⟨(CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).symm.trans
        (unitaryPSUEquiv h₀ (by omega))⟩⟩
    rw [h₀.card, ← pow_mul, mul_comm]
  obtain ⟨-, k, _, _, hk, ⟨ek⟩⟩ := hmod
  have hq0 : ℓ ^ f = (ℓ ^ (f / 3)) ^ 3 := by
    rw [← pow_mul, Nat.div_mul_cancel hpf]
  have hmod3 : (ℓ ^ (f / 3) + 1) % 3 = (ℓ ^ f + 1) % 3 := by
    have := mod_three_cube (ℓ ^ (f / 3))
    rw [hq0]
    omega
  have hQ3 : ¬ 3 ∣ ℓ ^ (f / 3) := fun hd => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
    h.prime).1 (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  have hrk := three_le_pRank_top_projSU (n := n) hk hQ3 (by omega)
  have hrk' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (primeFormP h₀ ((1 : GL (Fin n)
      (CFSG.LieType.Chevalley.fixSubfield σ)) : Matrix (Fin n) (Fin n)
        (CFSG.LieType.Chevalley.fixSubfield σ)))) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) ek]
    exact hrk
  have hrange_le : (CFSG.RankThree.Classical.primeSubfieldPSU h Nat.prime_three (by norm_num)
      hσord n).range ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormFieldHom h isPrimeFormGram_one σ) := by
    rw [hrange]
    intro y hy
    exact hy
  rw [hβeq, Inputs295c.fixSubgroup_conj]
  refine hrk'.trans ((CFSG.SectionRank.pRank_le_map (by norm_num) _ hinj ⊤).trans ?_)
  rw [← MonoidHom.range_eq_map]
  exact (CFSG.SectionRank.pRank_mono (by norm_num) hrange_le).trans
    (CFSG.SectionRank.pRank_le_map (by norm_num) _ (primeFormConjHom h _ M).injective _)

theorem outer295At_typeTwistedA {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hp3 : q.p ≠ 3)
    (hg : ¬ 3 ∣ Nat.gcd (r + 1) (q.card + 1))
    (hn : (3 ∣ q.card + 1 ∧ 3 ≤ r) ∨ (¬ 3 ∣ q.card + 1 ∧ 5 ≤ r)) :
    Inputs295c.Outer295At ⟨.twistedA r q, hv⟩ := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨-, -, -, -, F, _, h, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  haveI := h.finite
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hβ := three_le_pRank_fixSubgroup_primeFormP h hp3 (by rwa [← hqc]) (by
      rw [← hqc]
      omega) (MulAut.congr θ α) (congr_pow_three_eq_one θ hα) (congr_not_mem_range_conj θ hout)
  rw [Inputs295c.fixSubgroup_congr, pRank_map_mulEquiv] at hβ
  exact Or.inr (Or.inl hβ)

end Unitary

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295d
