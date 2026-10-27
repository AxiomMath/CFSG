module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpDbl
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LInner3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section LinAlg

variable {ι : Type} [Fintype ι] {K : Type} [Field K]

theorem exists_triple_ker_of {m : ℕ} (hmn : m + 3 ≤ Fintype.card ι) (Φ : Fin m → ι → K) :
    ∃ z : Fin 3 → ι → K, (∀ i j, Φ i ⬝ᵥ z j = 0) ∧ LinearIndependent K z := by
  set W := LinearMap.ker (Matrix.of Φ).mulVecLin with hW
  have hmem : ∀ x : ι → K, x ∈ W ↔ ∀ i, Φ i ⬝ᵥ x = 0 := by
    intro x
    rw [hW, LinearMap.mem_ker, mulVecLin_apply, funext_iff]
    simp [mulVec, Matrix.of_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.of Φ).mulVecLin
  have hle : Module.finrank K (LinearMap.range (Matrix.of Φ).mulVecLin) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.of Φ).mulVecLin)
    simpa using this
  rw [Module.finrank_fintype_fun_eq_card, ← hW] at hrk
  have h3 : 3 ≤ Module.finrank K W := by omega
  set b := Module.finBasis K W
  refine ⟨fun j => (b (Fin.castLE h3 j) : ι → K), fun i j => (hmem _).mp (b _).2 i, ?_⟩
  exact (b.linearIndependent.comp _ (Fin.castLE_injective h3)).map' W.subtype
    (Submodule.ker_subtype W)

theorem exists_notMem_span_pair {z : Fin 3 → ι → K} (hz : LinearIndependent K z)
    (u₁ u₂ : ι → K) : ∃ j, z j ∉ Submodule.span K {u₁, u₂} := by
  classical
  by_contra hc
  push Not at hc
  set S := Submodule.span K ({u₁, u₂} : Set (ι → K)) with hS
  have hz' : LinearIndependent K (fun j => (⟨z j, hc j⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hz
  have h3 := hz'.fintype_card_le_finrank
  have h2 : Module.finrank K S ≤ 2 := by
    have := finrank_span_finset_le_card (R := K) ({u₁, u₂} : Finset (ι → K))
    rw [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans Finset.card_le_two
  rw [Fintype.card_fin] at h3
  omega

end LinAlg

variable {r : ℕ} {K : Type} [Field K]

theorem vecMul_formJ {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hNJ : Nᵀ * formJ r K = formJ r K * N) (q : Fin r ⊕ Fin r → K) :
    (formJ r K *ᵥ q) ᵥ* N = formJ r K *ᵥ (N *ᵥ q) := by
  rw [← mulVec_transpose, mulVec_mulVec, hNJ, ← mulVec_mulVec]

theorem vecMulVec_comm_of_ker {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hNJ : Nᵀ * formJ r K = formJ r K * N) {p q : Fin r ⊕ Fin r → K} (hp : N *ᵥ p = 0)
    (hq : N *ᵥ q = 0) : vecMulVec p (formJ r K *ᵥ q) * N = N * vecMulVec p (formJ r K *ᵥ q) := by
  rw [vecMulVec_mul, vecMul_formJ hNJ, hq, mulVec_zero, vecMulVec_zero, mul_vecMulVec, hp,
    zero_vecMulVec]

theorem one_add_comm_N {N X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : X * N = N * X) :
    (1 + X) * N = N * (1 + X) := by
  rw [add_mul, mul_add, h, one_mul, mul_one]

theorem hasWit_inner_sp [Finite K] [CharP K 2] (hr : 3 ≤ r) {g : StatedSp r K}
    (hgg : g * g = 1) (hg1 : g ≠ 1) : HasWit (spInner r K g) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : NeZero r := ⟨by omega⟩
  have : Fintype K := Fintype.ofFinite K
  have hJ := formJ_transpose (r := r) h2
  have hJJ := formJ_mul_self (r := r) h2
  have hJJv : ∀ u, formJ r K *ᵥ (formJ r K *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hJJ, one_mulVec]
  set G := spMat g with hG
  obtain ⟨N, hN⟩ : ∃ N, N = G + 1 := ⟨_, rfl⟩
  have hGG : G * G = 1 := by rw [hG, ← spMat_mul, hgg, spMat_one]
  have hGN : G = N + 1 := by rw [hN, add_assoc, mat_add_self h2, add_zero]
  have hNN : N * N = 0 := by
    rw [hN, show (G + 1) * (G + 1) = G * G + (G + G) + 1 by noncomm_ring, hGG,
      mat_add_self h2, add_zero, mat_add_self h2]
  have hGT : Gᵀ * formJ r K = formJ r K * G := by
    calc Gᵀ * formJ r K = Gᵀ * formJ r K * (G * G) := by rw [hGG, Matrix.mul_one]
      _ = (Gᵀ * formJ r K * G) * G := by simp only [Matrix.mul_assoc]
      _ = formJ r K * G := by rw [hG, spMat_iso]
  have hNJ : Nᵀ * formJ r K = formJ r K * N := by
    rw [hN, transpose_add, transpose_one, add_mul, mul_add, hGT, Matrix.one_mul, Matrix.mul_one]
  have hNNv : ∀ w, N *ᵥ (N *ᵥ w) = 0 := fun w => by rw [mulVec_mulVec, hNN, zero_mulVec]
  have hN0 : N ≠ 0 := by
    intro h0
    apply hg1
    apply spMat_injective
    rw [spMat_one, ← hG, hGN, h0, zero_add]
  have hsa := form_mulVec_left hNJ
  have hfix : ∀ g' : StatedSp r K, spMat g' * N = N * spMat g' →
      spInner r K g (proj r K g') = proj r K g' := by
    intro g' hg'
    have hc : g * g' = g' * g := by
      apply spMat_injective
      rw [spMat_mul, spMat_mul, ← hG, hGN, add_mul, mul_add, hg', Matrix.one_mul, Matrix.mul_one]
    rw [spInner_eq_conj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hc,
      mul_inv_cancel_right]
  set Rb := formJ r K * N with hRb
  have hRbT : Rbᵀ = Rb := by rw [hRb, transpose_mul, hJ, hNJ]
  have hRbv : ∀ u w, (Rb *ᵥ u) ⬝ᵥ w = (formJ r K *ᵥ u) ⬝ᵥ (N *ᵥ w) := fun u w => by
    rw [hRb, ← mulVec_mulVec, hsa]
  choose δ hδ using fun i => FiniteField.isSquare_of_char_two (ringChar_eq_two h2) (Rb i i)
  have hb := form_self_eq h2 hRbT (d := δ) fun i => (hδ i).symm
  by_cases hex : ∃ y, δ ⬝ᵥ y = 0 ∧ Rb *ᵥ y ∉ Submodule.span K {δ}
  ·
    obtain ⟨y, hyδ, hyR⟩ := hex
    obtain ⟨x, hx1, hxW⟩ := exists_dual_of_notMem hyR
    have hxδ : δ ⬝ᵥ x = 0 := by
      rw [dotProduct_comm]
      exact hxW δ (Submodule.mem_span_singleton_self δ)
    have hbxx : (formJ r K *ᵥ x) ⬝ᵥ (N *ᵥ x) = 0 := by rw [← hRbv, hb, hxδ, mul_zero]
    have hbyy : (formJ r K *ᵥ y) ⬝ᵥ (N *ᵥ y) = 0 := by rw [← hRbv, hb, hyδ, mul_zero]
    have hbxy : (formJ r K *ᵥ x) ⬝ᵥ (N *ᵥ y) = 1 := by
      rw [← hRbv, form_comm hRbT, dotProduct_comm]
      exact hx1
    set c := (formJ r K *ᵥ x) ⬝ᵥ y with hc
    obtain ⟨y', hy'⟩ : ∃ y', y' = y + c • (N *ᵥ y) := ⟨_, rfl⟩
    have hNy' : N *ᵥ y' = N *ᵥ y := by rw [hy', mulVec_add, mulVec_smul, hNNv, smul_zero, add_zero]
    have hbyy' : (formJ r K *ᵥ y') ⬝ᵥ (N *ᵥ y') = 0 := by
      rw [hNy', hy', mulVec_add, add_dotProduct, hbyy, mulVec_smul, smul_dotProduct, hsa, hNNv,
        dotProduct_zero, smul_zero, zero_add]
    have hbxy' : (formJ r K *ᵥ x) ⬝ᵥ (N *ᵥ y') = 1 := by rw [hNy', hbxy]
    have hxy' : (formJ r K *ᵥ x) ⬝ᵥ y' = 0 := by
      rw [hy', dotProduct_add, dotProduct_smul, hbxy, smul_eq_mul, mul_one, ← hc,
        ← two_mul, h2, zero_mul]
    refine hasWit_sp_dbl (Q := fun M => M * N = N * M) hfix hNJ hNN hbxx hbyy' hbxy' hxy' ?_ ?_ ?_
    · refine one_add_comm_N ?_
      rw [spX, add_mul, mul_add, vecMulVec_mul, vecMulVec_mul, vecMul_formJ hNJ,
        vecMul_formJ hNJ, hNNv, mulVec_zero, vecMulVec_zero, mul_vecMulVec, mul_vecMulVec, hNNv,
        zero_vecMulVec, add_zero, zero_add]
    · refine one_add_comm_N ?_
      rw [spX, add_mul, mul_add, vecMulVec_mul, vecMulVec_mul, vecMul_formJ hNJ,
        vecMul_formJ hNJ, hNNv, mulVec_zero, vecMulVec_zero, mul_vecMulVec, mul_vecMulVec, hNNv,
        zero_vecMulVec, add_zero, zero_add]
    · exact one_add_comm_N (vecMulVec_comm_of_ker hNJ (hNNv x) (hNNv x))
  ·
    push Not at hex
    have hRbN : ∀ u, N *ᵥ u = formJ r K *ᵥ (Rb *ᵥ u) := fun u => by
      rw [hRb, ← mulVec_mulVec, hJJv]
    obtain ⟨i, hi⟩ : ∃ i, δ i ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hN0
      ext a b
      have hNb : N *ᵥ Pi.single b 1 = 0 := by
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
          (hex (Pi.single b 1) (by simp [show δ = 0 from funext hc]))
        rw [hRbN, ← ht, show δ = 0 from funext hc, smul_zero, mulVec_zero]
      have := congrFun hNb a
      rw [mulVec_single_one] at this
      simpa using this
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin r ⊕ Fin r → K, w₀ = (δ i)⁻¹ • Pi.single i 1 := ⟨_, rfl⟩
    have hδw₀ : δ ⬝ᵥ w₀ = 1 := by
      rw [hw₀, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, inv_mul_cancel₀ hi]
    have hIm : ∀ v, N *ᵥ v ∈ Submodule.span K {formJ r K *ᵥ δ, N *ᵥ w₀} := by
      intro v
      have hv : δ ⬝ᵥ (v - (δ ⬝ᵥ v) • w₀) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, hδw₀, smul_eq_mul, mul_one, sub_self]
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hex _ hv)
      have hsplit : N *ᵥ v = t • (formJ r K *ᵥ δ) + (δ ⬝ᵥ v) • (N *ᵥ w₀) := by
        rw [← mulVec_smul, ht, ← hRbN, ← mulVec_smul, ← mulVec_add, sub_add_cancel]
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hker : ∀ v, δ ⬝ᵥ v = 0 → (formJ r K *ᵥ (N *ᵥ w₀)) ⬝ᵥ v = 0 → N *ᵥ v = 0 := by
      intro v h₁ h₂
      have hJN : ∀ w, (formJ r K *ᵥ (N *ᵥ w)) ⬝ᵥ v = 0 := by
        intro w
        obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hIm w)
        rw [← hab, mulVec_add, mulVec_smul, mulVec_smul, hJJv, add_dotProduct, smul_dotProduct,
          smul_dotProduct, h₁, h₂, smul_zero, smul_zero, add_zero]
      ext k
      have := hJN (formJ r K *ᵥ Pi.single k 1)
      rw [hsa, hJJv, single_dotProduct, one_mul] at this
      exact this
    obtain ⟨z, hzΦ, hzind⟩ := exists_triple_ker_of (m := 2)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
      ![δ, formJ r K *ᵥ (N *ᵥ w₀)]
    obtain ⟨j, hj⟩ := exists_notMem_span_pair hzind (formJ r K *ᵥ δ) (N *ᵥ w₀)
    set x := z j with hx
    have hx₁ : δ ⬝ᵥ x = 0 := hzΦ 0 j
    have hx₂ : (formJ r K *ᵥ (N *ᵥ w₀)) ⬝ᵥ x = 0 := hzΦ 1 j
    have hJx : formJ r K *ᵥ x ∉ Submodule.span K {δ, formJ r K *ᵥ (N *ᵥ w₀)} := by
      intro hmem
      apply hj
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
      rw [← hJJv x, ← hab, mulVec_add, mulVec_smul, mulVec_smul, hJJv]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    obtain ⟨y, hy1, hyW⟩ := exists_dual_of_notMem hJx
    have hy₁ : δ ⬝ᵥ y = 0 := by
      rw [dotProduct_comm]
      exact hyW _ (Submodule.subset_span (by simp))
    have hy₂ : (formJ r K *ᵥ (N *ᵥ w₀)) ⬝ᵥ y = 0 := by
      rw [dotProduct_comm]
      exact hyW _ (Submodule.subset_span (by simp))
    have hNx := hker x hx₁ hx₂
    have hNy := hker y hy₁ hy₂
    obtain ⟨f₀, hf₀⟩ : ∃ f₀, N *ᵥ f₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hN0
      ext a b
      have := congrFun (hc (Pi.single b 1)) a
      rw [mulVec_single_one] at this
      simpa using this
    have hxm : (formJ r K *ᵥ x) ⬝ᵥ (N *ᵥ f₀) = 0 := by
      rw [← hsa, hNx, mulVec_zero, zero_dotProduct]
    have hym : (formJ r K *ᵥ y) ⬝ᵥ (N *ᵥ f₀) = 0 := by
      rw [← hsa, hNy, mulVec_zero, zero_dotProduct]
    refine hasWit_sp_comm (Q := fun M => M * N = N * M) hfix (x := x) (y := y)
      (m := N *ᵥ f₀) (by rw [dotProduct_comm]; exact hy1) hxm hym hf₀ ?_ ?_ ?_
    · exact one_add_comm_N (vecMulVec_comm_of_ker hNJ hNx hNx)
    · exact one_add_comm_N (vecMulVec_comm_of_ker hNJ hNy hNy)
    · refine one_add_comm_N ?_
      rw [spX, add_mul, mul_add, vecMulVec_comm_of_ker hNJ (hNNv f₀) hNx,
        vecMulVec_comm_of_ker hNJ hNx (hNNv f₀)]

end CFSG.ComponentClassification.HarrisLit.L33.C2
