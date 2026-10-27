module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBLift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBFrame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBRBlock

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem ite_two {α : Type*} [DecidableEq α] {i j : α} (hij : i ≠ j) (f : α → K) (a : α) :
    f a - ((if a = i then 2 * f i else 0) + if a = j then 2 * f j else 0) =
      if a = i ∨ a = j then -f a else f a := by
  by_cases hi : a = i
  · subst hi
    simp only [↓reduceIte, true_or, hij, add_zero]
    ring
  · by_cases hj : a = j
    · subst hj
      simp only [↓reduceIte, hi, or_true, zero_add]
      ring
    · simp only [hi, hj, ↓reduceIte, or_self, add_zero, sub_zero]

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem la_mem_statedOmega [Finite K] (hK : 4 ≤ Nat.card K) {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) (fr : Frame Q) (A : SL(2, K)) :
    (toLinEquiv ι K).symm (fr.La A) ∈ StatedOmega Q₀ := by
  have := CFSG.ClassicalInvolution.sl2_isPerfect (F := K) hK
  rw [statedOmega_eq_comap hQ₀, mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hle : Subgroup.map fr.La (⊤ : Subgroup SL(2, K)) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨B, -, rfl⟩
    exact Frame.La_mem_orthogonalGroup _ B
  have h1 : fr.La A ∈ Subgroup.map fr.La ⁅(⊤ : Subgroup SL(2, K)), ⊤⁆ :=
    mem_map_of_mem _ (Group.IsPerfect.mem_commutator (G := SL(2, K)))
  rw [map_commutator] at h1
  exact commutator_mono hle hle h1

@[expose] def statedOmegaEquiv {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ₀ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((StatedOmega Q₀).equivMapOfInjective (toLinEquiv ι K).toMonoidHom
    (toLinEquiv ι K).injective).trans (MulEquiv.subgroupCongr (by
      rw [statedOmega_eq_comap hQ₀, map_comap_eq_self_of_surjective
        (f := (toLinEquiv ι K).toMonoidHom) (toLinEquiv ι K).surjective]))

end Matrices

section Coords

variable {ι₁ ι₂ σ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype σ] [DecidableEq σ] (e : ι₁ ⊕ ι₂ ≃ σ)

theorem uMat_mulVec_inl (x : σ → K) (i : ι₁) :
    (((uMat e : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inl i)) = x (e (.inl i)) := by
  rw [uMat, reGL_mulVec, Function.comp_apply, Equiv.symm_apply_apply, blockR_mulVec]
  rfl

theorem uMat_mulVec_inr (x : σ → K) (j : ι₂) :
    (((uMat e : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inr j)) = -x (e (.inr j)) := by
  rw [uMat, reGL_mulVec, Function.comp_apply, Equiv.symm_apply_apply, blockR_mulVec]
  simp [Units.val_neg, neg_mulVec]

theorem reGL_blockL_mulVec_inl (g : GL ι₁ K) (x : σ → K) (i : ι₁) :
    (((reGL e (blockL ι₂ g) : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inl i)) =
      ((g : Matrix ι₁ ι₁ K) *ᵥ fun i' => x (e (.inl i'))) i := by
  rw [reGL_mulVec, Function.comp_apply, Equiv.symm_apply_apply, blockL_mulVec]
  rfl

theorem reGL_blockL_mulVec_inr (g : GL ι₁ K) (x : σ → K) (j : ι₂) :
    (((reGL e (blockL ι₂ g) : GL σ K) : Matrix σ σ K) *ᵥ x) (e (.inr j)) = x (e (.inr j)) := by
  rw [reGL_mulVec, Function.comp_apply, Equiv.symm_apply_apply, blockL_mulVec]
  rfl

omit [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
theorem spinMatrix_eq_of_apply {Q : QuadraticForm K (σ → K)} {x : spinGroup Q} {M : GL σ K}
    (h : ∀ v y, spinAction Q x v (e y) = ((M : Matrix σ σ K) *ᵥ v) (e y)) :
    spinMatrix Q x = M := by
  apply (toLinEquiv σ K).injective
  rw [toLinEquiv_spinMatrix]
  refine LinearEquiv.ext fun v => funext fun k => ?_
  obtain ⟨y, rfl⟩ := e.surjective k
  rw [h, toLinEquiv_apply]

end Coords

section Spin

variable {σ : Type} [Fintype σ] [DecidableEq σ] {Q : QuadraticForm K (σ → K)}

theorem spinMatrix_eq_neg_one
    (hker : ∀ x, x ∈ (spinMatrix Q).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q) = -1)
    (hcen : center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q)) {v₀ : σ → K}
    (hv₀ : Q v₀ = 1) {t : spinGroup Q} (htZ : t ∈ center (spinGroup Q)) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra Q) ≠ -1) : spinMatrix Q t = -1 := by
  obtain ⟨c, hc⟩ := DA.smul_of_le_comap hcen t htZ
  have hc2 : c * c = 1 := by
    have h1 := map_spinAction Q t v₀
    rw [hc, QuadraticMap.map_smul, hv₀, smul_eq_mul, mul_one] at h1
    exact h1
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  · exfalso
    have h1 : t ∈ (spinMatrix Q).ker := by
      rw [MonoidHom.mem_ker]
      apply (toLinEquiv σ K).injective
      rw [toLinEquiv_spinMatrix, map_one]
      exact LinearEquiv.ext fun v => by rw [hc, one_smul]; rfl
    rcases (hker t).mp h1 with h | h
    · exact ht1 h
    · exact htn h
  · apply (toLinEquiv σ K).injective
    rw [toLinEquiv_spinMatrix]
    refine LinearEquiv.ext fun v => ?_
    rw [hc, toLinEquiv_apply, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec, neg_one_smul]

variable {m : ℕ} (F : HypFrame Q m)

theorem ker_mul_longSL2 (hQ : Q ≠ 0)
    (hker : ∀ x, x ∈ (spinMatrix Q).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q) = -1) {i j : Fin m}
    (hij : i ≠ j) {z : spinGroup Q} (hz : z ∈ (spinMatrix Q).ker) :
    ∃ s, z * F.longSL2 hij true true (-1) = F.longSL2 hij true s (-1) := by
  rcases (hker z).mp hz with rfl | hz1
  · exact ⟨true, one_mul _⟩
  · have hzn : z = CliffordAlgebra.spinGroup.negOne Q hQ :=
      Subtype.ext (by rw [CliffordAlgebra.spinGroup.coe_negOne, hz1])
    exact ⟨false, by rw [hzn]; exact (T1.longSL2_neg_one_not F hij hQ true true).symm⟩

theorem conclZ_of_block [Finite K] (hQ : Q ≠ 0) [Finite (spinGroup Q)]
    (hker : ∀ x, x ∈ (spinMatrix Q).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q) = -1)
    (hrange : (spinMatrix Q).range = StatedOmega ⇑Q)
    (hrangeE : (spinAction Q).range ≤ elementaryGroup Q)
    (hcen : center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {i j k i' j' : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hi'j' : i' ≠ j')
    (hii' : i ≠ i') (hij' : i ≠ j')
    {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Nonempty ι₂]
    (e : ι₁ ⊕ ι₂ ≃ σ) {Q₁ : (ι₁ → K) → K} {Q₂ : (ι₂ → K) → K}
    (hQe : pullQ e ⇑Q = sumQ Q₁ Q₂)
    (hu : spinMatrix Q (F.longSL2 hij true true (-1)) = uMat e)
    (hx₀ : spinMatrix Q (F.longSL2 hi'j' true true (-1)) ∈ rblock e Q₁)
    (hBq : IsQuasisimple (StatedOmega Q₁))
    (hneg : (-1 : GL σ K) ∈ StatedOmega ⇑Q → (-1 : GL ι₁ K) ∈ StatedOmega Q₁)
    (hlie : ∃ (τ' : StatedLieTag) (n' : ℕ),
      Blueprint.LieModel (StatedOmega Q₁ ⧸ center (StatedOmega Q₁)) τ' n' p f)
    {t : spinGroup Q} (htZ : t ∈ center (spinGroup Q)) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra Q) ≠ -1) : ConclZ p f (spinGroup Q) t := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hZ := DA.smul_of_le_comap hcen
  have hkerc : (spinMatrix Q).ker ≤ center (spinGroup Q) := by
    rw [ker_spinMatrix]
    exact ker_spinAction_le_center Q
  have hB : rblock e Q₁ ≤ (spinMatrix Q).range := by
    rw [hrange]
    exact rblock_le_statedOmega e hQe
  have hBq' : IsQuasisimple (rblock e Q₁) :=
    LocalCores.isQuasisimple_of_mulEquiv (rblockEquiv e).symm hBq
  have hBu : rblock e Q₁ ≤ centralizer {spinMatrix Q (F.longSL2 hij true true (-1))} := by
    rw [hu]
    exact rblock_le_centralizer e
  have hc : ∀ c ∈ centralizer {F.longSL2 hij true true (-1)}, ∀ b ∈ rblock e Q₁,
      spinMatrix Q c * b * (spinMatrix Q c)⁻¹ ∈ rblock e Q₁ := by
    intro c hc b hb
    have hcΩ : spinMatrix Q c ∈ StatedOmega ⇑Q := hrange ▸ MonoidHom.mem_range.mpr ⟨c, rfl⟩
    have hcu : spinMatrix Q c * uMat e = uMat e * spinMatrix Q c := by
      rw [← hu, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc]
    exact conj_mem_rblock e h2 hQe (statedOmega_le_isoGroup _ hcΩ) hcu hb
  have hJq := isQuasisimple_liftJ hkerc hB hBq'
  obtain ⟨z, hz, hzx⟩ := exists_ker_mul_mem_liftJ hB hBq'.1 hx₀
  obtain ⟨s', hs'⟩ := ker_mul_longSL2 F hQ hker hi'j' hz
  rw [hs'] at hzx
  have hx2 := T1.orderOf_longSL2_neg_one F hi'j' hodd true s'
  have h2J : 2 ∣ Nat.card (liftJ (spinMatrix Q) (rblock e Q₁)) := by
    have h1 := orderOf_dvd_natCard (⟨_, hzx⟩ : liftJ (spinMatrix Q) (rblock e Q₁))
    rwa [Subgroup.orderOf_mk, hx2] at h1
  have hJc := isTwoComponentIn_of_normal_of_even (liftJ_le_centralizer hkerc hBu)
    (normal_liftJ hc) hJq h2J
  have hπneg : spinMatrix Q (CliffordAlgebra.spinGroup.negOne Q hQ) = 1 :=
    (hker _).mpr (Or.inr (CliffordAlgebra.spinGroup.coe_negOne Q hQ))
  have hJu : ∀ s, F.longSL2 hij true s (-1) ∉ liftJ (spinMatrix Q) (rblock e Q₁) := by
    intro s hs
    have h1 : spinMatrix Q (F.longSL2 hij true s (-1)) = uMat e := by
      cases s
      · have h := T1.longSL2_neg_one_not F hij hQ true true
        rw [Bool.not_true] at h
        rw [h, map_mul, hπneg, one_mul, hu]
      · exact hu
    have h3 := liftJ_le_comap _ _ hs
    rw [mem_comap, h1] at h3
    exact uMat_not_mem_rblock e h2 h3
  have hv₀ : Q (F.vec i true + F.vec i false) = 1 := by
    have h1 := F.polar_vec_not i true
    rw [QuadraticMap.polar, F.map_vec, F.map_vec, sub_zero, sub_zero] at h1
    exact h1
  have hπt := spinMatrix_eq_neg_one hker hcen hv₀ htZ ht1 htn
  have htu : spinMatrix Q (t * F.longSL2 hij true true (-1)) ∈ rblock e Q₁ := by
    rw [map_mul, hπt, hu]
    refine neg_one_mul_uMat_mem_rblock e (hneg ?_)
    rw [← hπt, ← hrange]
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  obtain ⟨z', hz', hz'J⟩ := exists_ker_mul_mem_liftJ hB hBq'.1 htu
  obtain ⟨s, hs⟩ := ker_mul_longSL2 F hQ hker hij hz'
  have htuJ : t * F.longSL2 hij true s (-1) ∈ liftJ (spinMatrix Q) (rblock e Q₁) := by
    rw [← hs, ← mul_assoc, (mem_center_iff.mp (hkerc hz') t), mul_assoc]
    exact hz'J
  have hJl : ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel
      (liftJ (spinMatrix Q) (rblock e Q₁) ⧸ center (liftJ (spinMatrix Q) (rblock e Q₁)))
      τ' n' p f := by
    obtain ⟨τ', n', h⟩ := hlie
    obtain ⟨e₁⟩ := nonempty_liftJ_quotCenter hkerc hB hBq'.1
    have e₂ : rblock e Q₁ ⧸ center (rblock e Q₁) ≃*
        StatedOmega Q₁ ⧸ center (StatedOmega Q₁) :=
      QuotientGroup.congr _ _ (rblockEquiv e) (Subgroup.map_center_eq _)
    exact ⟨τ', n', LieType.CurtisTits.lieModel_of_mulEquiv (e₁.trans e₂).symm h⟩
  exact conclZ_of_frame F hij hki hkj hp hp2 hK h5 hrangeE hZ hQ hJc hJu hJq
    ⟨_, hzx, hx2, DA.longSL2_neg_one_not_mem_center F hodd hZ hi'j' hii' hij' true s'⟩ hJl htuJ

end Spin

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
