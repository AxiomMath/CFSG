module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClEmb
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieSBlocks

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.CatLeafProof.EndOddSp (not_mem_scalars_of_ne_smul)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (QuatBlock quatBlock_of_isSolvable)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem gram_apply' {m : Type*} [Fintype m] (E : Matrix ι m K) (R : Matrix ι ι K) (a b : m) :
    (Eᵀ * R * E) a b = (fun i => E i a) ⬝ᵥ (R *ᵥ fun i => E i b) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec]

abbrev frame4 (A : Matrix ι ι K) (u : Fin 2 → ι → K) : Matrix ι (Fin 2 ⊕ Fin 2) K :=
  Matrix.of fun i a => Sum.elim u (fun k => A *ᵥ u k) a i

abbrev frameA (d : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (d • (1 : Matrix (Fin 2) (Fin 2) K))
    (1 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K)

theorem mul_frame4 {A : Matrix ι ι K} {d : K} (hAA : A * A = d • 1) (u : Fin 2 → ι → K) :
    A * frame4 A u = frame4 A u * frameA d := by
  ext i (k | k)
  · change (A *ᵥ u k) i = _
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, frame4, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  · change (A *ᵥ (A *ᵥ u k)) i = _
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, frame4, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

omit [DecidableEq ι] in
theorem dotProduct_mulVec_self_of_alt' (h2 : (2 : K) ≠ 0) {R : Matrix ι ι K}
    (hR : Rᵀ = -R) (v : ι → K) : v ⬝ᵥ (R *ᵥ v) = 0 := by
  have h : v ⬝ᵥ (R *ᵥ v) = -(v ⬝ᵥ (R *ᵥ v)) := by
    calc v ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (Rᵀ *ᵥ v) := by
          rw [mulVec_transpose, dotProduct_comm v (v ᵥ* R), ← dotProduct_mulVec]
      _ = -(v ⬝ᵥ (R *ᵥ v)) := by rw [hR, neg_mulVec, dotProduct_neg]
  have h' : (2 : K) * (v ⬝ᵥ (R *ᵥ v)) = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left h2

omit [DecidableEq ι] in
theorem dotProduct_mulVec_antisymm {R : Matrix ι ι K} (hR : Rᵀ = -R) (u v : ι → K) :
    u ⬝ᵥ (R *ᵥ v) = -(v ⬝ᵥ (R *ᵥ u)) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hR, neg_mulVec, dotProduct_comm, dotProduct_neg]

omit [DecidableEq ι] in
theorem dotProduct_mulVec_left (A R : Matrix ι ι K) (u v : ι → K) :
    (A *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ ((Aᵀ * R) *ᵥ v) := by
  symm
  rw [← mulVec_mulVec, dotProduct_mulVec u Aᵀ, vecMul_transpose]

end Frame

variable {r : ℕ}

theorem exists_sp_quat_pair (h2 : (2 : K) ≠ 0) (hr : 3 ≤ r) {A : gsp r K}
    {E : Matrix (Fin r ⊕ Fin r) (Fin 2 ⊕ Fin 2) K} {F : Matrix (Fin 2 ⊕ Fin 2) (Fin r ⊕ Fin r) K}
    {G A₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hFE : F * E = 1)
    (h1 : Eᵀ * formJ r K = G * F) (h2' : formJ r K * E = Fᵀ * G)
    (hAE : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * E =
      E * A₄)
    (hFA : F * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      A₄ * F)
    {x₄ y₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hx : x₄ * x₄ = -1) (hy : y₄ * y₄ = -1)
    (hyx : y₄ * x₄ = -(x₄ * y₄)) (hxG : x₄ᵀ * G * x₄ = G) (hyG : y₄ᵀ * G * y₄ = G)
    (hxA : A₄ * x₄ = x₄ * A₄) (hyA : A₄ * y₄ = y₄ * A₄) :
    ∃ x y z : StatedSp r K, x ∈ ⁅spCent r K A, spCent r K A⁆ ∧
      y ∈ ⁅spCent r K A, spCent r K A⁆ ∧ z ^ 2 = 1 ∧ x ^ 2 = z ∧ y ^ 2 = z ∧
      x * y = z * (y * x) ∧ z ∉ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) := by
  set T : GL (Fin 2 ⊕ Fin 2) K →* GL (Fin r ⊕ Fin r) K := Units.map (embHom hFE) with hT
  have hTv : ∀ g : GL (Fin 2 ⊕ Fin 2) K,
      ((T g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        embT E F g := fun g => rfl
  have hS : ∀ g : GL (Fin 2 ⊕ Fin 2) K,
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * G * g = G → T g ∈ StatedSp r K := by
    intro g hg
    rw [mem_statedSp_iff, hTv]
    exact embT_isometry hFE h1 h2' hg
  have hC : ∀ (g : GL (Fin 2 ⊕ Fin 2) K) (hg : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      G * g = G), A₄ * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = g * A₄ →
      (⟨T g, hS g hg⟩ : StatedSp r K) ∈ spCent r K A := by
    intro g hg hgA
    rw [mem_spCent]
    change ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      embT E F g = embT E F g * ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    exact embT_commute hAE hFA hgA
  set uX : GL (Fin 2 ⊕ Fin 2) K := ⟨x₄, -x₄, by rw [Matrix.mul_neg, hx, neg_neg],
    by rw [Matrix.neg_mul, hx, neg_neg]⟩ with huX
  set uY : GL (Fin 2 ⊕ Fin 2) K := ⟨y₄, -y₄, by rw [Matrix.mul_neg, hy, neg_neg],
    by rw [Matrix.neg_mul, hy, neg_neg]⟩ with huY
  set uW : GL (Fin 2 ⊕ Fin 2) K := ⟨quatW x₄ y₄, quatW' x₄ y₄,
    quatW_mul_quatW' hx hy hyx h2, quatW'_mul_quatW hx hy hyx h2⟩ with huW
  have hWG : (uW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * G * uW = G :=
    quatW_isometry hx hy hyx h2 hxG hyG
  have hWA : A₄ * (uW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = uW * A₄ :=
    quatW_commute hxA hyA
  have hXYG : ((uX * uY : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      G * (uX * uY : GL (Fin 2 ⊕ Fin 2) K) = G := by
    change (x₄ * y₄)ᵀ * G * (x₄ * y₄) = G
    rw [transpose_mul]
    calc y₄ᵀ * x₄ᵀ * G * (x₄ * y₄) = y₄ᵀ * (x₄ᵀ * G * x₄) * y₄ := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hxG, hyG]
  have hXYA : A₄ * ((uX * uY : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      = (uX * uY : GL (Fin 2 ⊕ Fin 2) K) * A₄ := by
    change A₄ * (x₄ * y₄) = x₄ * y₄ * A₄
    rw [← Matrix.mul_assoc, hxA, Matrix.mul_assoc, hyA, Matrix.mul_assoc]
  have hz2 : (-1 : GL (Fin 2 ⊕ Fin 2) K) ^ 2 = 1 := by rw [neg_one_sq]
  have hx2 : uX ^ 2 = -1 := Units.ext (by rw [pow_two]; exact hx)
  have hy2 : uY ^ 2 = -1 := Units.ext (by rw [pow_two]; exact hy)
  have hxy : uX * uY = -1 * (uY * uX) := Units.ext (by
    change x₄ * y₄ = ((-1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (y₄ * x₄)
    rw [Units.val_neg, Units.val_one, Matrix.neg_mul, Matrix.one_mul, hyx, neg_neg])
  have hw1 : uW * uY * uW⁻¹ = uX * uY := Units.ext (by
    change quatW x₄ y₄ * y₄ * quatW' x₄ y₄ = x₄ * y₄
    rw [quatW_mul_y hx hy hyx, Matrix.mul_assoc, quatW_mul_quatW' hx hy hyx h2, Matrix.mul_one])
  have hw2 : uW * (uX * uY) * uW⁻¹ = uX := Units.ext (by
    change quatW x₄ y₄ * (x₄ * y₄) * quatW' x₄ y₄ = x₄
    rw [quatW_mul_xy hx hy hyx, Matrix.mul_assoc, quatW_mul_quatW' hx hy hyx h2,
      Matrix.mul_one])
  obtain ⟨hcX, hcY⟩ := commutatorElement_quat hz2 hx2 hy2 hxy hw1 hw2
  set sW : StatedSp r K := ⟨T uW, hS uW hWG⟩ with hsW
  set sY : StatedSp r K := ⟨T uY, hS uY hyG⟩ with hsY
  set sXY : StatedSp r K := ⟨T (uX * uY), hS _ hXYG⟩ with hsXY
  have hneg : ((-1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * G *
      ((-1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = G := by
    rw [Units.val_neg, Units.val_one, transpose_neg, transpose_one, Matrix.neg_mul,
      Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  refine ⟨⟨T uX, hS uX hxG⟩, sY, ⟨T (-1), hS _ hneg⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (⟨T uX, hS uX hxG⟩ : StatedSp r K) = ⁅sW, sY⁆ := by
      apply Subtype.ext
      change T uX = ⁅T uW, T uY⁆
      rw [← map_commutatorElement, hcX]
    rw [e]
    exact commutator_mem_commutator (hC uW hWG hWA) (hC uY hyG hyA)
  · have e : sY = ⁅sW, sXY⁆ := by
      apply Subtype.ext
      change T uY = ⁅T uW, T (uX * uY)⁆
      rw [← map_commutatorElement, hcY]
    rw [e]
    exact commutator_mem_commutator (hC uW hWG hWA) (hC _ hXYG hXYA)
  · apply Subtype.ext
    change T (-1) ^ 2 = 1
    rw [← map_pow, hz2, map_one]
  · apply Subtype.ext
    change T uX ^ 2 = T (-1)
    rw [← map_pow, hx2]
  · apply Subtype.ext
    change T uY ^ 2 = T (-1)
    rw [← map_pow, hy2]
  · apply Subtype.ext
    change T uX * T uY = T (-1) * (T uY * T uX)
    rw [← map_mul, hxy, map_mul, map_mul]
  · refine not_mem_scalars_of_ne_smul fun c hc => ?_
    change embT E F ((-1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      c • 1 at hc
    rw [Units.val_neg, Units.val_one] at hc
    exact embT_neg_one_ne_smul h2 hFE (by simp; omega) c hc

end CFSG.ComponentClassification.Burgoyne.Cl
