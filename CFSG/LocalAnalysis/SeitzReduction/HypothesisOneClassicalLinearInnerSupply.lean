module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearInnerRigid
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero

public noncomputable section

namespace CFSG.SeitzReduction.ClassicalLinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL
open scoped commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

theorem rankOne_eq {x y a a' : Fin n → K} (hxy : x = y) (ha : a = a') (h : a ⬝ᵥ x = 0)
    (h' : a' ⬝ᵥ y = 0) : rankOne x a h = rankOne y a' h' := by
  subst hxy ha
  rfl

theorem rankOne_zero_left (a : Fin n → K) (h : a ⬝ᵥ (0 : Fin n → K) = 0) : rankOne 0 a h = 1 := by
  apply Subtype.ext
  rw [coe_rankOne, zero_vecMulVec, add_zero]
  rfl

theorem rankOne_zero_right (x : Fin n → K) (h : (0 : Fin n → K) ⬝ᵥ x = 0) :
    rankOne x 0 h = 1 := by
  apply Subtype.ext
  rw [coe_rankOne, vecMulVec_zero, add_zero]
  rfl

theorem rankOne_add_left (x y a : Fin n → K) (hx : a ⬝ᵥ x = 0) (hy : a ⬝ᵥ y = 0)
    (h : a ⬝ᵥ (x + y) = 0) : rankOne (x + y) a h = rankOne x a hx * rankOne y a hy := by
  apply Subtype.ext
  change 1 + vecMulVec (x + y) a = (1 + vecMulVec x a) * (1 + vecMulVec y a)
  rw [add_vecMulVec, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, hy, zero_smul, vecMulVec_zero, add_zero]
  abel

theorem rankOne_add_right (x a a' : Fin n → K) (ha : a ⬝ᵥ x = 0) (ha' : a' ⬝ᵥ x = 0)
    (h : (a + a') ⬝ᵥ x = 0) : rankOne x (a + a') h = rankOne x a ha * rankOne x a' ha' := by
  apply Subtype.ext
  change 1 + vecMulVec x (a + a') = (1 + vecMulVec x a) * (1 + vecMulVec x a')
  rw [vecMulVec_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, ha, zero_smul, vecMulVec_zero, add_zero]
  abel

theorem rankOne_smul_right (x a : Fin n → K) (c : K) (h : (c • a) ⬝ᵥ x = 0)
    (h' : a ⬝ᵥ (c • x) = 0) : rankOne x (c • a) h = rankOne (c • x) a h' := by
  apply Subtype.ext
  rw [coe_rankOne, coe_rankOne, vecMulVec_smul, smul_vecMulVec]

theorem rankOne_sum_left_mem {H : Subgroup (SpecialLinearGroup (Fin n) K)} {ι : Type*}
    (s : Finset ι) (f : ι → Fin n → K) (a : Fin n → K) (hf : ∀ i ∈ s, a ⬝ᵥ f i = 0)
    (hH : ∀ i ∈ s, ∀ h, rankOne (f i) a h ∈ H) (h : a ⬝ᵥ ∑ i ∈ s, f i = 0) :
    rankOne (∑ i ∈ s, f i) a h ∈ H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [rankOne_eq Finset.sum_empty rfl h (dotProduct_zero a), rankOne_zero_left]
    exact H.one_mem
  | insert j s hj ih =>
    have hfj := hf j (Finset.mem_insert_self j s)
    have hs' : ∀ i ∈ s, a ⬝ᵥ f i = 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : a ⬝ᵥ ∑ i ∈ s, f i = 0 := by
      rw [dotProduct_sum]
      exact Finset.sum_eq_zero hs'
    have hsum' : a ⬝ᵥ (f j + ∑ i ∈ s, f i) = 0 := by rw [dotProduct_add, hfj, hsum, add_zero]
    rw [rankOne_eq (Finset.sum_insert hj) rfl h hsum', rankOne_add_left _ _ _ hfj hsum]
    exact H.mul_mem (hH j (Finset.mem_insert_self j s) hfj)
      (ih hs' (fun i hi => hH i (Finset.mem_insert_of_mem hi)) hsum)

theorem rankOne_sum_right_mem {H : Subgroup (SpecialLinearGroup (Fin n) K)} {ι : Type*}
    (s : Finset ι) (x : Fin n → K) (g : ι → Fin n → K) (hg : ∀ i ∈ s, g i ⬝ᵥ x = 0)
    (hH : ∀ i ∈ s, ∀ h, rankOne x (g i) h ∈ H) (h : (∑ i ∈ s, g i) ⬝ᵥ x = 0) :
    rankOne x (∑ i ∈ s, g i) h ∈ H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [rankOne_eq rfl Finset.sum_empty h (zero_dotProduct x), rankOne_zero_right]
    exact H.one_mem
  | insert j s hj ih =>
    have hgj := hg j (Finset.mem_insert_self j s)
    have hs' : ∀ i ∈ s, g i ⬝ᵥ x = 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hsum : (∑ i ∈ s, g i) ⬝ᵥ x = 0 := by
      rw [sum_dotProduct]
      exact Finset.sum_eq_zero hs'
    have hsum' : (g j + ∑ i ∈ s, g i) ⬝ᵥ x = 0 := by rw [add_dotProduct, hgj, hsum, add_zero]
    rw [rankOne_eq rfl (Finset.sum_insert hj) h hsum', rankOne_add_right _ _ _ hgj hsum]
    exact H.mul_mem (hH j (Finset.mem_insert_self j s) hgj)
      (ih hs' (fun i hi => hH i (Finset.mem_insert_of_mem hi)) hsum)

theorem one_add_mul_one_add_mul_one_sub_mul_one_sub (P Q : Matrix (Fin n) (Fin n) K) :
    (1 + P) * (1 + Q) * (1 - P) * (1 - Q) = 1 + P * Q - Q * P - P * P - Q * Q + Q * (P * Q) +
      P * P * Q - P * (Q * Q) - P * Q * P + P * Q * (P * Q) := by
  noncomm_ring

theorem one_add_mul_one_add_mul_one_sub_mul_one_sub' (P Q : Matrix (Fin n) (Fin n) K) :
    (1 + P) * (1 + Q) * (1 - P) * (1 - Q) = 1 + P * Q - Q * P - P * P - Q * Q + Q * P * Q +
      P * P * Q - P * (Q * Q) - P * (Q * P) + P * (Q * P) * Q := by
  noncomm_ring

theorem coe_inv_of_sq_eq_zero {g : SpecialLinearGroup (Fin n) K} {P : Matrix (Fin n) (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + P) (hP : P * P = 0) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - P :=
  coe_inv_eq_of_mul_eq_one (by
    rw [hg, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP, sub_zero,
      sub_add_cancel])

theorem coe_commutator_of_mul_eq_zero {g h : SpecialLinearGroup (Fin n) K}
    {P Q : Matrix (Fin n) (Fin n) K} (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + P)
    (hh : (h : Matrix (Fin n) (Fin n) K) = 1 + Q) (hP : P * P = 0) (hQ : Q * Q = 0)
    (hPQ : P * Q = 0) :
    ((⁅g, h⁆ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - Q * P := by
  have e : ((⁅g, h⁆ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  rw [e, coe_inv_of_sq_eq_zero hg hP, coe_inv_of_sq_eq_zero hh hQ, hg, hh,
    one_add_mul_one_add_mul_one_sub_mul_one_sub, hP, hQ, hPQ]
  simp

theorem coe_commutator_of_mul_eq_zero' {g h : SpecialLinearGroup (Fin n) K}
    {P Q : Matrix (Fin n) (Fin n) K} (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + P)
    (hh : (h : Matrix (Fin n) (Fin n) K) = 1 + Q) (hP : P * P = 0) (hQ : Q * Q = 0)
    (hQP : Q * P = 0) :
    ((⁅g, h⁆ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + P * Q := by
  have e : ((⁅g, h⁆ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  rw [e, coe_inv_of_sq_eq_zero hg hP, coe_inv_of_sq_eq_zero hh hQ, hg, hh,
    one_add_mul_one_add_mul_one_sub_mul_one_sub', hP, hQ, hQP]
  simp

theorem vecMulVec_sq_eq_zero {x a : Fin n → K} (h : a ⬝ᵥ x = 0) :
    vecMulVec x a * vecMulVec x a = 0 := by
  rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

theorem commutator_rankOne_of_dotProduct_left {x a y b : Fin n → K} (hxa : a ⬝ᵥ x = 0)
    (hyb : b ⬝ᵥ y = 0) (hbx : b ⬝ᵥ x = 0) (h : b ⬝ᵥ ((a ⬝ᵥ y) • x) = 0) :
    ⁅rankOne x a hxa, rankOne y b hyb⁆ = rankOne ((a ⬝ᵥ y) • x) b h := by
  apply Subtype.ext
  rw [coe_commutator_of_mul_eq_zero' (coe_rankOne x a hxa) (coe_rankOne y b hyb)
    (vecMulVec_sq_eq_zero hxa) (vecMulVec_sq_eq_zero hyb)
    (by rw [vecMulVec_mul_vecMulVec, hbx, zero_smul, vecMulVec_zero]),
    vecMulVec_mul_vecMulVec, vecMulVec_smul, ← smul_vecMulVec]
  rfl

theorem commutator_rankOne_of_dotProduct_right {x a y b : Fin n → K} (hxa : a ⬝ᵥ x = 0)
    (hyb : b ⬝ᵥ y = 0) (hay : a ⬝ᵥ y = 0) (h : a ⬝ᵥ (-(b ⬝ᵥ x) • y) = 0) :
    ⁅rankOne x a hxa, rankOne y b hyb⁆ = rankOne (-(b ⬝ᵥ x) • y) a h := by
  apply Subtype.ext
  rw [coe_commutator_of_mul_eq_zero (coe_rankOne x a hxa) (coe_rankOne y b hyb)
    (vecMulVec_sq_eq_zero hxa) (vecMulVec_sq_eq_zero hyb)
    (by rw [vecMulVec_mul_vecMulVec, hay, zero_smul, vecMulVec_zero]),
    vecMulVec_mul_vecMulVec, vecMulVec_smul, coe_rankOne, smul_vecMulVec, neg_smul, sub_eq_add_neg,
    ← smul_vecMulVec]

section Dual

variable {ι : Type*} (b : Module.Basis ι K (Fin n → K))

@[expose] def dualVec (j : ι) : Fin n → K := fun k => b.repr (Pi.single k 1) j

theorem dualVec_dotProduct (j : ι) (v : Fin n → K) : dualVec b j ⬝ᵥ v = b.repr v j := by
  conv_rhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, dotProduct, dualVec]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem dualVec_dotProduct_basis [DecidableEq ι] (j i : ι) :
    dualVec b j ⬝ᵥ b i = if i = j then 1 else 0 := by
  rw [dualVec_dotProduct, b.repr_self, Finsupp.single_apply]

theorem eq_sum_dualVec [Fintype ι] (m : Fin n → K) : m = ∑ j, (m ⬝ᵥ b j) • dualVec b j := by
  funext k
  have hk : m k = m ⬝ᵥ Pi.single k 1 := by rw [dotProduct_single, mul_one]
  rw [hk]
  conv_lhs => rw [← b.sum_repr (Pi.single k 1)]
  rw [dotProduct_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct_smul, dualVec]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_of_forall_dotProduct_eq {a a' : Fin n → K} (h : ∀ v, a ⬝ᵥ v = a' ⬝ᵥ v) : a = a' := by
  funext k
  have := h (Pi.single k 1)
  rwa [dotProduct_single, dotProduct_single, mul_one, mul_one] at this

end Dual

theorem mem_comap_centralizer_of_coe {s : GL (Fin n) K} {g : SpecialLinearGroup (Fin n) K}
    {Q : Matrix (Fin n) (Fin n) K} (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + Q)
    (hQ : Q * ((s : Matrix (Fin n) (Fin n) K) - 1) = ((s : Matrix (Fin n) (Fin n) K) - 1) * Q) :
    g ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →*
      GL (Fin n) K) := by
  rw [mem_comap, mem_centralizer_singleton_iff]
  apply Units.ext
  change (g : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) =
    (s : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)
  set N := (s : Matrix (Fin n) (Fin n) K) - 1 with hN
  have hs : (s : Matrix (Fin n) (Fin n) K) = 1 + N := by rw [hN, add_sub_cancel]
  rw [hg, hs]
  calc (1 + Q) * (1 + N) = 1 + Q + N + Q * N := by noncomm_ring
    _ = 1 + Q + N + N * Q := by rw [hQ]
    _ = (1 + N) * (1 + Q) := by noncomm_ring

theorem rankOne_mem_comap_centralizer {s : GL (Fin n) K} {x a : Fin n → K} (h : a ⬝ᵥ x = 0)
    (hx : ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ x = 0)
    (ha : a ᵥ* ((s : Matrix (Fin n) (Fin n) K) - 1) = 0) :
    rankOne x a h ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) :=
  mem_comap_centralizer_of_coe (coe_rankOne x a h) (by
    rw [vecMulVec_mul, mul_vecMulVec, hx, ha, vecMulVec_zero, zero_vecMulVec])

theorem conjAut_proj_eq_of_mem {s : GL (Fin n) K} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →*
      GL (Fin n) K)) :
    conjAut n K s (proj n K g) = proj n K g := by
  rw [conjAut_proj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  have h : SpecialLinearGroup.toGL g * s = s * SpecialLinearGroup.toGL g :=
    mem_centralizer_singleton_iff.mp hg
  rw [← h, mul_inv_cancel_right]

section Adapted

variable {ℓ r : ℕ} (b : Module.Basis (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K (Fin n → K))
  {N : Matrix (Fin n) (Fin n) K}

theorem repr_mulVec_inl (hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, N *ᵥ b (.inr k) = 0) (v : Fin n → K) (i : Fin ℓ) :
    b.repr (N *ᵥ v) (.inl i) = 0 := by
  have key : (b.coord (.inl i)).comp (Matrix.mulVecLin N) = 0 := by
    refine b.ext fun j => ?_
    rcases j with i' | k
    · simp [Module.Basis.coord_apply, hbX]
    · simp [hbL]
  simpa [Module.Basis.coord_apply] using LinearMap.congr_fun key v

theorem repr_mulVec_inr_inl (hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, N *ᵥ b (.inr k) = 0) (v : Fin n → K) (i : Fin ℓ) :
    b.repr (N *ᵥ v) (.inr (.inl i)) = b.repr v (.inl i) := by
  have key : (b.coord (.inr (.inl i))).comp (Matrix.mulVecLin N) = b.coord (.inl i) := by
    refine b.ext fun j => ?_
    rcases j with i' | k
    · simp [Module.Basis.coord_apply, hbX, Finsupp.single_apply]
    · simp [Module.Basis.coord_apply, hbL]
  simpa [Module.Basis.coord_apply] using LinearMap.congr_fun key v

theorem repr_mulVec_inr_inr (hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, N *ᵥ b (.inr k) = 0) (v : Fin n → K) (k : Fin r) :
    b.repr (N *ᵥ v) (.inr (.inr k)) = 0 := by
  have key : (b.coord (.inr (.inr k))).comp (Matrix.mulVecLin N) = 0 := by
    refine b.ext fun j => ?_
    rcases j with i' | k'
    · simp [Module.Basis.coord_apply, hbX]
    · simp [hbL]
  simpa [Module.Basis.coord_apply] using LinearMap.congr_fun key v

theorem dualVec_inl_vecMul (hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, N *ᵥ b (.inr k) = 0) (i : Fin ℓ) : dualVec b (.inl i) ᵥ* N = 0 :=
  eq_of_forall_dotProduct_eq fun v => by
    rw [← dotProduct_mulVec, dualVec_dotProduct, repr_mulVec_inl b hbX hbL, zero_dotProduct]

theorem dualVec_inr_inl_vecMul (hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, N *ᵥ b (.inr k) = 0) (i : Fin ℓ) :
    dualVec b (.inr (.inl i)) ᵥ* N = dualVec b (.inl i) :=
  eq_of_forall_dotProduct_eq fun v => by
    rw [← dotProduct_mulVec, dualVec_dotProduct, dualVec_dotProduct,
      repr_mulVec_inr_inl b hbX hbL]

theorem dualVec_inr_inr_vecMul (hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, N *ᵥ b (.inr k) = 0) (k : Fin r) : dualVec b (.inr (.inr k)) ᵥ* N = 0 :=
  eq_of_forall_dotProduct_eq fun v => by
    rw [← dotProduct_mulVec, dualVec_dotProduct, repr_mulVec_inr_inr b hbX hbL, zero_dotProduct]

@[expose] def elemRankOne : Set (SpecialLinearGroup (Fin n) K) :=
  {g | ∃ (x a : Fin n → K) (h : a ⬝ᵥ x = 0), g = rankOne x a h ∧
    ((∃ (c : K) (i' i : Fin ℓ), x = c • b (.inr (.inl i')) ∧ a = dualVec b (.inl i)) ∨
      (∃ (c : K) (k : Fin r) (i : Fin ℓ), x = c • b (.inr (.inr k)) ∧ a = dualVec b (.inl i)) ∨
      (∃ (c : K) (i : Fin ℓ) (k : Fin r), x = c • b (.inr (.inl i)) ∧
        a = dualVec b (.inr (.inr k))))}

theorem rankOne_mem_elemRankOne₁ (c : K) (i' i : Fin ℓ) (h) :
    rankOne (c • b (.inr (.inl i'))) (dualVec b (.inl i)) h ∈ elemRankOne b :=
  ⟨_, _, h, rfl, Or.inl ⟨c, i', i, rfl, rfl⟩⟩

theorem rankOne_mem_elemRankOne₂ (c : K) (k : Fin r) (i : Fin ℓ) (h) :
    rankOne (c • b (.inr (.inr k))) (dualVec b (.inl i)) h ∈ elemRankOne b :=
  ⟨_, _, h, rfl, Or.inr (Or.inl ⟨c, k, i, rfl, rfl⟩)⟩

theorem rankOne_mem_elemRankOne₃ (c : K) (i : Fin ℓ) (k : Fin r) (h) :
    rankOne (c • b (.inr (.inl i))) (dualVec b (.inr (.inr k))) h ∈ elemRankOne b :=
  ⟨_, _, h, rfl, Or.inr (Or.inr ⟨c, i, k, rfl, rfl⟩)⟩

@[expose] def leviQ (i' i : Fin ℓ) : Matrix (Fin n) (Fin n) K :=
  vecMulVec (b (.inl i')) (dualVec b (.inl i)) +
    vecMulVec (b (.inr (.inl i'))) (dualVec b (.inr (.inl i)))

theorem leviQ_mul_self {i' i : Fin ℓ} (hii : i' ≠ i) : leviQ b i' i * leviQ b i' i = 0 := by
  simp [leviQ, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis,
    hii]

@[expose] def leviElt {i' i : Fin ℓ} (hii : i' ≠ i) : SpecialLinearGroup (Fin n) K :=
  rankOne (b (.inl i')) (dualVec b (.inl i)) (by simp [dualVec_dotProduct_basis, hii]) *
    rankOne (b (.inr (.inl i'))) (dualVec b (.inr (.inl i)))
      (by simp [dualVec_dotProduct_basis, hii])

theorem coe_leviElt {i' i : Fin ℓ} (hii : i' ≠ i) :
    ((leviElt b hii : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + leviQ b i' i := by
  change (1 + vecMulVec (b (.inl i')) (dualVec b (.inl i))) *
    (1 + vecMulVec (b (.inr (.inl i'))) (dualVec b (.inr (.inl i)))) = _
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, vecMulVec_mul_vecMulVec,
    dualVec_dotProduct_basis]
  simp only [reduceCtorEq, ite_false, zero_smul, vecMulVec_zero, add_zero, leviQ]
  abel

theorem leviElt_mem {s : GL (Fin n) K}
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) {i' i : Fin ℓ}
    (hii : i' ≠ i) :
    leviElt b hii ∈ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) :=
  mem_comap_centralizer_of_coe (coe_leviElt b hii) (by
    rw [leviQ, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul, vecMulVec_mul, mul_vecMulVec,
      mul_vecMulVec, dualVec_inl_vecMul b hbX hbL, dualVec_inr_inl_vecMul b hbX hbL, hbX, hbL,
      vecMulVec_zero, zero_vecMulVec, zero_add, add_zero])

theorem closure_elemRankOne_le {s : GL (Fin n) K}
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) :
    closure (elemRankOne b) ≤ (centralizer {s}).comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
  rw [closure_le]
  rintro _ ⟨x, a, h, rfl, hx⟩
  have hxN : ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ x = 0 := by
    rcases hx with ⟨c, i', i, rfl, -⟩ | ⟨c, k, i, rfl, -⟩ | ⟨c, i, k, rfl, -⟩ <;>
      rw [mulVec_smul, hbL, smul_zero]
  have haN : a ᵥ* ((s : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
    rcases hx with ⟨c, i', i, -, rfl⟩ | ⟨c, k, i, -, rfl⟩ | ⟨c, i, k, -, rfl⟩
    · exact dualVec_inl_vecMul b hbX hbL i
    · exact dualVec_inl_vecMul b hbX hbL i
    · exact dualVec_inr_inr_vecMul b hbX hbL k
  exact rankOne_mem_comap_centralizer h hxN haN

theorem closure_elemRankOne_le_commutator {s : GL (Fin n) K}
    (hbX : ∀ i, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inl i) = b (.inr (.inl i)))
    (hbL : ∀ k, ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ b (.inr k) = 0) (hr : 0 < r)
    (hℓr : 2 ≤ ℓ ∨ 2 ≤ r) :
    closure (elemRankOne b) ≤ ⁅closure (elemRankOne b), (centralizer {s}).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K)⁆ := by
  have hRP := closure_elemRankOne_le b hbX hbL
  rw [closure_le]
  rintro _ ⟨x, a, h, rfl, (⟨c, i', i, rfl, rfl⟩ | ⟨c, k, i, rfl, rfl⟩ | ⟨c, i, k, rfl, rfl⟩)⟩
  ·
    set k₀ : Fin r := ⟨0, hr⟩
    have h₁ : dualVec b (.inr (.inr k₀)) ⬝ᵥ (c • b (.inr (.inl i'))) = 0 := by
      simp [dualVec_dotProduct_basis]
    have h₂ : dualVec b (.inl i) ⬝ᵥ b (.inr (.inr k₀)) = 0 := by simp [dualVec_dotProduct_basis]
    have h₃ : dualVec b (.inl i) ⬝ᵥ ((dualVec b (.inr (.inr k₀)) ⬝ᵥ b (.inr (.inr k₀))) •
        (c • b (.inr (.inl i')))) = 0 := by simp [dualVec_dotProduct_basis]
    rw [rankOne_eq (show c • b (.inr (.inl i')) = (dualVec b (.inr (.inr k₀)) ⬝ᵥ
        b (.inr (.inr k₀))) • (c • b (.inr (.inl i'))) by simp [dualVec_dotProduct_basis]) rfl h h₃,
      ← commutator_rankOne_of_dotProduct_left h₁ h₂ h h₃]
    refine commutator_mem_commutator (subset_closure (rankOne_mem_elemRankOne₃ b c i' k₀ h₁))
      (hRP (subset_closure ?_))
    exact ⟨_, _, h₂, rfl, Or.inr (Or.inl ⟨1, k₀, i, (one_smul K _).symm, rfl⟩)⟩
  ·
    rcases hℓr with hℓ | hr2
    · have : Nontrivial (Fin ℓ) := Fin.nontrivial_iff_two_le.mpr hℓ
      obtain ⟨i', hii⟩ := exists_ne i
      have h₁ : dualVec b (.inl i') ⬝ᵥ (c • b (.inr (.inr k))) = 0 := by
        simp [dualVec_dotProduct_basis]
      have e : ⁅rankOne (c • b (.inr (.inr k))) (dualVec b (.inl i')) h₁, leviElt b hii⁆ =
          rankOne (c • b (.inr (.inr k))) (dualVec b (.inl i)) h := by
        apply Subtype.ext
        rw [coe_commutator_of_mul_eq_zero' (coe_rankOne _ _ h₁) (coe_leviElt b hii)
          (vecMulVec_sq_eq_zero h₁) (leviQ_mul_self b hii) ?_, coe_rankOne]
        · simp [leviQ, Matrix.mul_add, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis]
        · simp [leviQ, Matrix.add_mul, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis]
      rw [← e]
      exact commutator_mem_commutator (subset_closure (rankOne_mem_elemRankOne₂ b c k i' h₁))
        (leviElt_mem b hbX hbL hii)
    · have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr2
      obtain ⟨k', hkk⟩ := exists_ne k
      have h₁ : dualVec b (.inl i) ⬝ᵥ ((-c) • b (.inr (.inr k'))) = 0 := by
        simp [dualVec_dotProduct_basis]
      have h₂ : dualVec b (.inr (.inr k')) ⬝ᵥ b (.inr (.inr k)) = 0 := by
        simp [dualVec_dotProduct_basis, hkk.symm]
      have hay : dualVec b (.inl i) ⬝ᵥ b (.inr (.inr k)) = 0 := by
        simp [dualVec_dotProduct_basis]
      have h₃ : dualVec b (.inl i) ⬝ᵥ ((-(dualVec b (.inr (.inr k')) ⬝ᵥ
          ((-c) • b (.inr (.inr k'))))) • b (.inr (.inr k))) = 0 := by
        simp [dualVec_dotProduct_basis]
      rw [rankOne_eq (show c • b (.inr (.inr k)) = (-(dualVec b (.inr (.inr k')) ⬝ᵥ
          ((-c) • b (.inr (.inr k'))))) • b (.inr (.inr k)) by simp [dualVec_dotProduct_basis])
          rfl h h₃, ← commutator_rankOne_of_dotProduct_right h₁ h₂ hay h₃]
      exact commutator_mem_commutator (subset_closure (rankOne_mem_elemRankOne₂ b (-c) k' i h₁))
        (rankOne_mem_comap_centralizer h₂ (hbL _) (dualVec_inr_inr_vecMul b hbX hbL k'))
  ·
    rcases hℓr with hℓ | hr2
    · have : Nontrivial (Fin ℓ) := Fin.nontrivial_iff_two_le.mpr hℓ
      obtain ⟨i', hii⟩ := exists_ne i
      have h₁ : dualVec b (.inr (.inr k)) ⬝ᵥ ((-c) • b (.inr (.inl i'))) = 0 := by
        simp [dualVec_dotProduct_basis]
      have e : ⁅rankOne ((-c) • b (.inr (.inl i'))) (dualVec b (.inr (.inr k))) h₁,
          leviElt b hii.symm⁆ = rankOne (c • b (.inr (.inl i))) (dualVec b (.inr (.inr k))) h := by
        apply Subtype.ext
        rw [coe_commutator_of_mul_eq_zero (coe_rankOne _ _ h₁) (coe_leviElt b hii.symm)
          (vecMulVec_sq_eq_zero h₁) (leviQ_mul_self b hii.symm) ?_, coe_rankOne]
        · simp [leviQ, Matrix.add_mul, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis,
            sub_eq_add_neg]
        · simp [leviQ, Matrix.mul_add, vecMulVec_mul_vecMulVec, dualVec_dotProduct_basis]
      rw [← e]
      exact commutator_mem_commutator
        (subset_closure (rankOne_mem_elemRankOne₃ b (-c) i' k h₁)) (leviElt_mem b hbX hbL _)
    · have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr2
      obtain ⟨k', hkk⟩ := exists_ne k
      have h₁ : dualVec b (.inr (.inr k')) ⬝ᵥ (c • b (.inr (.inl i))) = 0 := by
        simp [dualVec_dotProduct_basis]
      have h₂ : dualVec b (.inr (.inr k)) ⬝ᵥ b (.inr (.inr k')) = 0 := by
        simp [dualVec_dotProduct_basis, hkk]
      have h₃ : dualVec b (.inr (.inr k)) ⬝ᵥ ((dualVec b (.inr (.inr k')) ⬝ᵥ
          b (.inr (.inr k'))) • (c • b (.inr (.inl i)))) = 0 := by
        simp [dualVec_dotProduct_basis]
      rw [rankOne_eq (show c • b (.inr (.inl i)) = (dualVec b (.inr (.inr k')) ⬝ᵥ
          b (.inr (.inr k'))) • (c • b (.inr (.inl i))) by simp [dualVec_dotProduct_basis])
          rfl h h₃, ← commutator_rankOne_of_dotProduct_left h₁ h₂ h h₃]
      exact commutator_mem_commutator (subset_closure (rankOne_mem_elemRankOne₃ b c i k' h₁))
        (rankOne_mem_comap_centralizer h₂ (hbL _) (dualVec_inr_inr_vecMul b hbX hbL k))

end Adapted

theorem exists_rankOne_mem_closure_odd_fixed [Finite K] [CharP K 2] (hn : 4 ≤ n)
    {s : GL (Fin n) K} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hWL : LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) ≠
      LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))) :
    ∃ a₀ v₀ w₀ x₂ : Fin n → K,
      a₀ ∈ dotOrth (LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))) ∧
      a₀ ⬝ᵥ v₀ = 1 ∧ w₀ ∈ LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) ∧
      w₀ ≠ 0 ∧ x₂ ∈ LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) ∧
      x₂ ∉ LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) ∧
      (∀ x ∈ LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)),
        ∀ h : a₀ ⬝ᵥ x = 0, proj n K (rankOne x a₀ h) ∈
          closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)}) ∧
      (∀ m ∈ dotOrth (LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))),
        ∀ h : m ⬝ᵥ w₀ = 0, proj n K (rankOne w₀ m h) ∈
          closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)}) := by
  classical
  have : NeZero n := ⟨by omega⟩
  set N := (s : Matrix (Fin n) (Fin n) K) - 1 with hNdef
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hs' : (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, hs, Units.val_one]
  have hNN : N * N = 0 := by
    calc N * N = (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) + 1 -
          ((s : Matrix (Fin n) (Fin n) K) + (s : Matrix (Fin n) (Fin n) K)) := by
          rw [hNdef]; noncomm_ring
      _ = 0 := by rw [hs', CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, sub_zero]
  set f := Matrix.mulVecLin N with hf
  have hf2 : f ∘ₗ f = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, hf, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_mulVec,
      hNN, zero_mulVec, LinearMap.zero_apply]
  obtain ⟨r, b, hb1, hb2⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_basis_sq_eq_zero f hf2
  have hbX : ∀ i, N *ᵥ b (.inl i) = b (.inr (.inl i)) := hb1
  have hbL : ∀ k, N *ᵥ b (.inr k) = 0 := hb2
  have hcard := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun] at hcard
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrank
  have hWL' : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hf2, LinearMap.zero_apply]
  have hℓ : 0 < Module.finrank K (LinearMap.range f) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨v, hv⟩ : ∃ v, N *ᵥ v ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hs1
      apply Units.ext
      rw [Units.val_one, ← sub_eq_zero]
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
      exact hall v
    exact ⟨⟨N *ᵥ v, v, rfl⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hr : 0 < r := by
    by_contra h0
    apply hWL
    exact Submodule.eq_of_le_of_finrank_eq hWL' (by omega)
  have hℓr : 2 ≤ Module.finrank K (LinearMap.range f) ∨ 2 ≤ r := by omega
  set i₀ : Fin (Module.finrank K (LinearMap.range f)) := ⟨0, hℓ⟩
  set k₀ : Fin r := ⟨0, hr⟩
  have hRP := closure_elemRankOne_le (s := s) b hbX hbL
  have hD : (closure (elemRankOne b)).map (proj n K) ≤
      closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} := by
    refine le_closure_odd_fixed_of_le_commutator (map_mono hRP) ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact conjAut_proj_eq_of_mem hg
    · rw [← map_commutator]
      exact map_mono (closure_elemRankOne_le_commutator b hbX hbL hr hℓr)
  have hmem : ∀ g ∈ closure (elemRankOne b), proj n K g ∈
      closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)} :=
    fun g hg => hD (mem_map_of_mem _ hg)
  have hreprL : ∀ x ∈ LinearMap.ker f, ∀ i, b.repr x (.inl i) = 0 := by
    intro x hx i
    have hx' : N *ᵥ x = 0 := hx
    rw [← repr_mulVec_inr_inl b hbX hbL, hx', map_zero, Finsupp.zero_apply]
  refine ⟨dualVec b (.inl i₀), b (.inl i₀), b (.inr (.inl i₀)), b (.inr (.inr k₀)), ?_, ?_,
    ⟨b (.inl i₀), hb1 i₀⟩, b.ne_zero _, hb2 _, ?_, ?_, ?_⟩
  · rw [mem_dotOrth]
    intro x hx
    rw [dualVec_dotProduct, hreprL x hx]
  · simp [dualVec_dotProduct_basis]
  · rintro ⟨v, hv⟩
    have h1 := repr_mulVec_inr_inr b hbX hbL v k₀
    rw [show N *ᵥ v = b (.inr (.inr k₀)) from hv, b.repr_self] at h1
    simp at h1
  ·
    intro x hx h
    apply hmem
    have hsum : dualVec b (.inl i₀) ⬝ᵥ ∑ j, b.repr x j • b j = 0 := by rw [b.sum_repr]; exact h
    rw [rankOne_eq (b.sum_repr x).symm rfl h hsum]
    refine rankOne_sum_left_mem Finset.univ (fun j => b.repr x j • b j) _ ?_ ?_ hsum
    · intro j _
      rw [dotProduct_smul, dualVec_dotProduct_basis]
      split_ifs with hj
      · rw [hj, hreprL x hx, zero_smul]
      · rw [smul_zero]
    · intro j _ hj
      rcases j with i | i | k
      · rw [rankOne_eq (by rw [hreprL x hx, zero_smul]) rfl hj (dotProduct_zero _),
          rankOne_zero_left]
        exact one_mem _
      · exact subset_closure (rankOne_mem_elemRankOne₁ b _ i i₀ hj)
      · exact subset_closure (rankOne_mem_elemRankOne₂ b _ k i₀ hj)
  ·
    intro m hm h
    apply hmem
    have hmW : ∀ i, m ⬝ᵥ b (.inr (.inl i)) = 0 := fun i =>
      mem_dotOrth.mp hm _ ⟨b (.inl i), hb1 i⟩
    have hsum : (∑ j, (m ⬝ᵥ b j) • dualVec b j) ⬝ᵥ b (.inr (.inl i₀)) = 0 := by
      rw [← eq_sum_dualVec b m]; exact h
    rw [rankOne_eq rfl (eq_sum_dualVec b m) h hsum]
    refine rankOne_sum_right_mem Finset.univ _ (fun j => (m ⬝ᵥ b j) • dualVec b j) ?_ ?_ hsum
    · intro j _
      rw [smul_dotProduct, dualVec_dotProduct_basis]
      split_ifs with hj
      · rw [← hj, hmW, zero_smul]
      · rw [smul_zero]
    · intro j _ hj
      rcases j with i | i | k
      · rw [rankOne_smul_right _ _ _ hj (by simp [dualVec_dotProduct_basis])]
        exact subset_closure (rankOne_mem_elemRankOne₁ b _ i₀ i _)
      · rw [rankOne_eq rfl (by rw [hmW, zero_smul]) hj (zero_dotProduct _), rankOne_zero_right]
        exact one_mem _
      · rw [rankOne_smul_right _ _ _ hj (by simp [dualVec_dotProduct_basis])]
        exact subset_closure (rankOne_mem_elemRankOne₃ b _ i₀ k _)

end CFSG.SeitzReduction.ClassicalLinear
