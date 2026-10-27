module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionKernel
public import CFSG.RankThree.PartOne.U5K.Hyp.Cyc

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K]

theorem eq_one_of_pow_two_pow_eq_one (h : UnitaryFieldData 2 f K) {c : K} {k : ℕ}
    (hc : c ^ 2 ^ k = 1) : c = 1 := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hc
    exact zero_ne_one hc
  set u : Kˣ := Units.mk0 c hc0
  have hu : u ^ 2 ^ k = 1 := Units.ext (by simp [u, hc])
  have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Fintype.card Kˣ := orderOf_dvd_card
  have hodd : Odd (Fintype.card Kˣ) := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h.card_eq_sq, ← pow_mul]
    have hpos : 0 < 2 ^ (f * 2) := by positivity
    have heven : Even (2 ^ (f * 2)) := (Nat.even_pow' (by have := h.one_le; omega)).2 even_two
    obtain ⟨m, hm⟩ := heven
    exact ⟨m - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (Fintype.card Kˣ) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hord : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have : u = 1 := orderOf_eq_one_iff.1 hord
  simpa [u] using congrArg Units.val this

theorem twoCentralizerV (h : UnitaryFieldData 2 f K) : TwoCentralizerV h := by
  intro _ hZ ρ ⟨k, hk⟩ hρ
  obtain ⟨x, hxL, hx, hE, hF⟩ := lam_lift_of_central hZ hρ
  have hxk : x ^ 2 ^ k = 1 :=
    Phi_injOn_Lam (pow_mem hxL _) (one_mem _) (by rw [map_pow, hx, hk, map_one])
  have hzz : lmat x (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by
    have h1 : (psiL h ⟨x, hxL⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxL⟩ : Lam h) ^ 2 ^ k = 1 := Subtype.ext hxk
      rw [this, map_one]
    exact eq_one_of_pow_two_pow_eq_one h h1
  obtain ⟨hxr, hxP, -⟩ := hxL
  have hP1 : blkP (lmat x) = 1 := by
    ext a b
    fin_cases a; fin_cases b
    exact hzz
  have hA : lmat x = blk3 1 (blkX (lmat x)) (blkY (lmat x)) 1 (blkQ (lmat x)) 1 := by
    have h1 := eq_blk3_of_para hxP
    have hEA : blkA (lmat x) = 1 := hE
    have hFD : blkD (lmat x) = 1 := hF
    rwa [hEA, hFD, hP1] at h1
  obtain ⟨ν, -, -, hgram⟩ := x.2
  have hg' : ((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x = ν • hypGram 2 1 K := hgram
  rw [hA] at hg'
  have hν : ν = 1 := by
    have e := congrFun (congrFun hg' (.inl 0)) (.inr (.inr 0))
    simp [Fintype.sum_sum_type, Matrix.mul_apply, hypGram] at e
    exact e.symm
  have hgram' : ((blk3 1 (blkX (lmat x)) (blkY (lmat x)) 1 (blkQ (lmat x)) 1).map h.bar)ᵀ *
      hypGram 2 1 K * blk3 1 (blkX (lmat x)) (blkY (lmat x)) 1 (blkQ (lmat x)) 1 =
        hypGram 2 1 K := by
    rw [hg', hν, one_smul]
  rw [blk3_gram_iff] at hgram'
  obtain ⟨-, -, hXQ, hYQ⟩ := hgram'
  set X := blkX (lmat x)
  set Y := blkY (lmat x)
  set Q := blkQ (lmat x)
  have hQ : Q = -(X.map h.bar)ᵀ := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
      Matrix.mul_one] at hXQ
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hXQ
  set v : Fin 2 → K := fun i => X i 0 with hv
  have hXv : X = replicateCol (Fin 1) v := by
    ext i l
    fin_cases l
    rfl
  have hQv : Q = replicateRow (Fin 1) fun j => -h.bar (v j) := by
    ext l j
    fin_cases l
    rw [hQ]
    simp [hv]
  have hcon : Y + (Y.map h.bar)ᵀ = -vecMulVec v fun j => h.bar (v j) := by
    have := h.charP
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
      Matrix.one_mul] at hYQ
    rw [hQv] at hYQ
    ext i j
    have e := congrFun (congrFun hYQ i) j
    simp [Matrix.mul_apply, vecMulVec, h.bar_bar] at e ⊢
    linear_combination e
  have hAN : lmat x = oddUni h v Y := by
    rw [hA, hXv, hQv]
    rfl
  obtain ⟨g, hg, hgm⟩ := exists_mem_Ssub hcon
  have hxg : x = inlG g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Units.ext
      change lmat x = mat g
      rw [hgm, hAN]
    · rw [hxr]
      rfl
  rw [← hx, hxg, Phi_inlG]
  exact ⟨g, hg, rfl⟩

theorem gram_inv (h : UnitaryFieldData 2 f K) {M M' : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hMM : M * M' = 1) {μ : K} (hμ : μ ≠ 0)
    (hM : (M.map h.bar)ᵀ * hypGram 2 1 K * M = μ • hypGram 2 1 K) :
    (M'.map h.bar)ᵀ * hypGram 2 1 K * M' = μ⁻¹ • hypGram 2 1 K := by
  have h1 : (M'.map h.bar)ᵀ * (M.map h.bar)ᵀ = 1 := by
    rw [← conjTranspose_mul', hMM, Matrix.map_one _ (map_zero _) (map_one _), transpose_one]
  calc (M'.map h.bar)ᵀ * hypGram 2 1 K * M'
      = μ⁻¹ • ((M'.map h.bar)ᵀ * (μ • hypGram 2 1 K) * M') := by
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • ((M'.map h.bar)ᵀ * ((M.map h.bar)ᵀ * hypGram 2 1 K * M) * M') := by rw [hM]
    _ = μ⁻¹ • (((M'.map h.bar)ᵀ * (M.map h.bar)ᵀ) * hypGram 2 1 K * (M * M')) := by
        simp only [Matrix.mul_assoc]
    _ = μ⁻¹ • hypGram 2 1 K := by rw [h1, hMM, Matrix.one_mul, Matrix.mul_one]

theorem exists_inlG_eq_commutator (h : UnitaryFieldData 2 f K) {x y : Gam h} (hx : x ∈ Gam1 h)
    (hy : y ∈ Gam1 h) : ∃ g : hypSU h 2 1, ⁅x, y⁆ = inlG g := by
  have hxr : x.1.right = 1 := mem_Gam1.1 hx
  have hyr : y.1.right = 1 := mem_Gam1.1 hy
  have hcr : (⁅x, y⁆ : Gam h).1.right = 1 := by
    rw [commutatorElement_def]
    simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hxr, hyr]
  set A : GL (HypIndex 2 1) K := x.1.left
  set B : GL (HypIndex 2 1) K := y.1.left
  have hc : (⁅x, y⁆ : Gam h).1.left = A * B * A⁻¹ * B⁻¹ := by
    rw [commutatorElement_def]
    simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right, hxr, hyr, A, B]
  obtain ⟨μ, hμ0, -, hA⟩ := x.2
  obtain ⟨ν, hν0, -, hB⟩ := y.2
  change ((A : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map h.bar)ᵀ * hypGram 2 1 K *
    (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = μ • hypGram 2 1 K at hA
  change ((B : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map h.bar)ᵀ * hypGram 2 1 K *
    (B : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = ν • hypGram 2 1 K at hB
  have hA' := gram_inv h (M := (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K))
    (M' := ((A⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hμ0 hA
  have hB' := gram_inv h (M := (B : Matrix (HypIndex 2 1) (HypIndex 2 1) K))
    (M' := ((B⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hν0 hB
  set C : GL (HypIndex 2 1) K := A * B * A⁻¹ * B⁻¹ with hC
  set a : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with ha
  set b : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    (B : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hb
  set a' : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    ((A⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with ha'
  set b' : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    ((B⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hb'
  have hCm : (C : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = a * b * a' * b' := by
    simp [hC, Units.val_mul, a, b, a', b']
  set J := hypGram 2 1 K
  have hgram : ((C : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map h.bar)ᵀ * J *
      (C : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = J := by
    rw [hCm, conjTranspose_mul', conjTranspose_mul', conjTranspose_mul']
    have e : (b'.map h.bar)ᵀ * ((a'.map h.bar)ᵀ * ((b.map h.bar)ᵀ * (a.map h.bar)ᵀ)) * J *
        (a * b * a' * b') = (b'.map h.bar)ᵀ * ((a'.map h.bar)ᵀ *
          ((b.map h.bar)ᵀ * ((a.map h.bar)ᵀ * J * a) * b) * a') * b' := by
      simp only [Matrix.mul_assoc]
    rw [e, hA]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [hB]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [hA']
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [hB']
    simp only [smul_smul]
    convert one_smul K J using 2
    field_simp
  have hdet : (C : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det = 1 := by
    rw [hCm, det_mul, det_mul, det_mul]
    have e1 : a.det * a'.det = 1 := by
      rw [← det_mul, ha, ha', ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    have e2 : b.det * b'.det = 1 := by
      rw [← det_mul, hb, hb', ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    calc a.det * b.det * a'.det * b'.det = (a.det * a'.det) * (b.det * b'.det) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  refine ⟨⟨C, mem_hypSU.2 ⟨hgram, hdet⟩⟩, ?_⟩
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact hc
  · exact hcr

theorem commutator_Dlin_le_Pi (h : UnitaryFieldData 2 f K) : ⁅Dlin h, Dlin h⁆ ≤ Pi h := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨g, hg⟩ := exists_inlG_eq_commutator h hx hy
  rw [← map_commutatorElement, hg, Phi_inlG, ← range_innM]
  exact ⟨g, rfl⟩

theorem perfectLeInn (h : UnitaryFieldData 2 f K) : PerfectLeInn h := by
  intro hf _ D hD
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [h.card_eq_sq, ← pow_mul, mul_comm]
  obtain ⟨σ, -, -, hzσ, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hcard
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, hzσ⟩
  have hcomm : ∀ a b : K ≃+* K, a * b = b * a := fun a b => (IsCyclic.commGroup).mul_comm a b
  set τ : Gam h →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (UnitaryHigher.semilinearSimilitudes h 2 1).subtype with hτ
  set E : Subgroup (Gam h) := D.comap (Phi h) with hE
  have hEmap : E.map (Phi h) = D := Subgroup.map_comap_eq_self_of_surjective (Phi_surjective h) D
  have hEE : ⁅E, E⁆ ≤ Gam1 h := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Gam1, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hDlin : D ≤ Dlin h := by
    calc D = ⁅D, D⁆ := hD.symm
      _ = ⁅E, E⁆.map (Phi h) := by rw [Subgroup.map_commutator, hEmap]
      _ ≤ (Gam1 h).map (Phi h) := Subgroup.map_mono hEE
  calc D = ⁅D, D⁆ := hD.symm
    _ ≤ ⁅Dlin h, Dlin h⁆ := Subgroup.commutator_mono hDlin hDlin
    _ ≤ Pi h := commutator_Dlin_le_Pi h

theorem exists_lift_sq_eq_one (h : UnitaryFieldData 2 f K) {z : hypPSU h 2 1} (hz : z * z = 1) :
    ∃ s : hypSU h 2 1, s * s = 1 ∧ hypProj h 2 1 s = z := by
  obtain ⟨s₀, rfl⟩ := hypProj_surjective h 2 1 z
  have h1 : s₀ * s₀ ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj h 2 1, MonoidHom.mem_ker, map_mul]
    exact hz
  obtain ⟨c, -, hc5, hc⟩ := h1
  have h5 : (s₀ * s₀) ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hc, ← map_pow, hc5, map_one, Subgroup.coe_one]
  refine ⟨s₀ ^ 5, ?_, ?_⟩
  · rw [← pow_add, show 5 + 5 = 2 * 5 by rfl, pow_mul, sq, h5]
  · rw [map_pow]
    have hz2 : hypProj h 2 1 s₀ ^ 2 = 1 := by rw [sq]; exact hz
    rw [show 5 = 2 * 2 + 1 by rfl, pow_succ, pow_mul, hz2, one_pow, one_mul]

theorem hypForm_sub_sub_eq_zero (h : UnitaryFieldData 2 f K) {s : hypSU h 2 1} (hs : s * s = 1)
    (u v : HypIndex 2 1 → K) : hypForm h 2 1 (s • u - u) (s • v - v) = 0 := by
  have := h.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hsu : hypForm h 2 1 (s • u) v = hypForm h 2 1 u (s • v) := by
    have := hypForm_smul_smul h s (s • u) v
    rw [smul_smul, hs, one_smul] at this
    exact this.symm
  simp only [map_sub, LinearMap.sub_apply]
  rw [hypForm_smul_smul, hsu]
  linear_combination h2 (hypForm h 2 1 u v) - h2 (hypForm h 2 1 u (s • v))

theorem involutionsConjIntoV (h : UnitaryFieldData 2 f K) : InvolutionsConjIntoV h := by
  intro _ _ z hz
  obtain ⟨s, hss, rfl⟩ := exists_lift_sq_eq_one h hz
  by_cases hs1 : s = 1
  · refine ⟨1, 1, one_mem _, ?_⟩
    rw [hs1, map_one]
    group
  set W : Submodule K (HypIndex 2 1 → K) :=
    LinearMap.range (mulVecLin ((s : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K)
      - LinearMap.id) with hW
  have hmemW : ∀ u : HypIndex 2 1 → K, s • u - u ∈ W := fun u => ⟨u, rfl⟩
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact hypForm_sub_sub_eq_zero h hss u v
  have hW0 : W ≠ ⊥ := by
    intro hbot
    apply hs1
    apply Subtype.ext
    apply Units.ext
    ext a b
    have h1 : ((s : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ
        (Pi.single b 1 : HypIndex 2 1 → K) = Pi.single b 1 := by
      have := hmemW (Pi.single b 1)
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have h2 := congrFun h1 a
    rw [mulVec_single_one, Matrix.col_apply] at h2
    change ((s : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b =
      (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b
    rw [h2, Matrix.one_apply, Pi.single_apply]
  obtain ⟨-, hd2, g, hg⟩ := UnitaryHigher.exists_smul_hypFlag_eq h le_rfl hW0 hWiso
  set d := Module.finrank K W
  have hF : hypFlag h 2 1 d = posFlag 2 1 K d := hypFlag_eq_posFlag h le_rfl (by omega)
  set s' := g⁻¹ * s * g with hs'
  have hrow : ∀ (a b : HypIndex 2 1), 2 ≤ fullPos a →
      ((s' : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b =
        (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
    intro a b ha
    set u : HypIndex 2 1 → K := Pi.single b 1
    have hsu : s • (g • u) - g • u ∈ W := hmemW _
    rw [← hg] at hsu
    obtain ⟨w, hw, hwu⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hsu
    have hw' : g⁻¹ • (s • (g • u) - g • u) = w := by rw [← hwu, inv_smul_smul]
    have hs'u : s' • u - u = w := by
      rw [← hw', smul_sub, inv_smul_smul, hs', mul_smul, mul_smul]
    rw [hF] at hw
    have h1 := congrFun hs'u a
    rw [Pi.sub_apply, hw a (le_trans (by omega) ha), sub_eq_zero] at h1
    change (((s' : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ
      (Pi.single b (1 : K) : HypIndex 2 1 → K)) a = (Pi.single b (1 : K) : HypIndex 2 1 → K) a
      at h1
    rw [mulVec_single_one, Matrix.col_apply] at h1
    rw [h1, Matrix.one_apply, Pi.single_apply]
  set M := ((s' : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hM
  have hblk : M = blk3 (blkA M) (blkX M) (blkY M) 1 0 1 := by
    ext a b
    rcases a with i | k | j
    · rcases b with i' | k' | j' <;> rfl
    · have ha : 2 ≤ fullPos (.inr (.inl k) : HypIndex 2 1) := by simp
      rw [hrow _ b ha]
      rcases b with i' | k' | j' <;> simp [Matrix.one_apply]
    · have ha : 2 ≤ fullPos (.inr (.inr j) : HypIndex 2 1) := by simp; omega
      rw [hrow _ b ha]
      rcases b with i' | k' | j' <;> simp [Matrix.one_apply]
  have hgram : (M.map h.bar)ᵀ * hypGram 2 1 K * M = hypGram 2 1 K := (mem_hypSU.1 s'.2).1
  rw [hblk, blk3_gram_iff] at hgram
  obtain ⟨hA, -, hX, -⟩ := hgram
  have hA1 : blkA M = 1 := by
    rw [Matrix.mul_one] at hA
    have := congrArg (fun N => (N.map h.bar)ᵀ) hA
    simpa [conjTranspose_conjTranspose', Matrix.map_one _ (map_zero _) (map_one _)] using this
  have hX0 : blkX M = 0 := by
    rw [Matrix.mul_one, Matrix.mul_zero, add_zero] at hX
    have := congrArg (fun N => (N.map h.bar)ᵀ) hX
    simpa [conjTranspose_conjTranspose'] using this
  have hMN : M = oddUni h 0 (blkY M) := by
    have e : M = blk3 1 0 (blkY M) 1 0 1 := by
      conv_lhs => rw [hblk]
      rw [hA1, hX0]
    have hc : (replicateCol (Fin 1) (0 : Fin 2 → K)) = 0 := by ext; simp
    have hr : (replicateRow (Fin 1) fun j : Fin 2 => -h.bar ((0 : Fin 2 → K) j)) = 0 := by
      ext; simp
    rw [oddUni, hc, hr]
    exact e
  refine ⟨hypProj h 2 1 g, s', mem_Vsub_of_mat hMN, ?_⟩
  rw [hs', map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.EvenBN.U5
