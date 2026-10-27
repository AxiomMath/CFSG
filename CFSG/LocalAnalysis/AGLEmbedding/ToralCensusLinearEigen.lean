module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open Matrix CFSG.AGLEmbedding.LinearThreeKit

variable {K : Type*} [Field K] {n : ℕ}

theorem one_add_rankOne_mulVec (w φ x : Fin n → K) :
    (1 + replicateCol Unit w * replicateRow Unit φ) *ᵥ x = x + (φ ⬝ᵥ x) • w := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, replicateCol, replicateRow, Finset.mul_sum, mul_comm]

theorem commute_one_add_rankOne {T : Matrix (Fin n) (Fin n) K} {c : K} {w φ : Fin n → K}
    (hw : T *ᵥ w = c • w) (hφ : ∀ x, φ ⬝ᵥ (T *ᵥ x) = c * (φ ⬝ᵥ x)) :
    T * (1 + replicateCol Unit w * replicateRow Unit φ) =
      (1 + replicateCol Unit w * replicateRow Unit φ) * T := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, one_add_rankOne_mulVec,
    one_add_rankOne_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hw, hφ, smul_smul, mul_comm]

theorem apply_eq_dotProduct_single (f : (Fin n → K) →ₗ[K] K) (x : Fin n → K) :
    f x = (fun j => f (Pi.single j 1)) ⬝ᵥ x := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  simp only [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (Pi.single j (x j) : Fin n → K) = x j • Pi.single j 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

theorem linearIndependent_pair_swap {V : Type*} [AddCommGroup V] [Module K V] {x y : V}
    (h : LinearIndependent K ![x, y]) : LinearIndependent K ![y, x] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h t s (by rw [add_comm]; exact hst)
  exact ⟨h2, h1⟩

theorem exists_det_one_commute_mulVec_eq {m : ℕ} (hm : (m : K) ≠ 0)
    {U : Matrix (Fin n) (Fin n) K} (hU : U ^ m = 1) {a b : Fin n → K}
    (hab : LinearIndependent K ![a, b]) (ha : U *ᵥ a = a) (hb : U *ᵥ b = b) :
    ∃ G : Matrix (Fin n) (Fin n) K, G.det = 1 ∧ U * G = G * U ∧ G *ᵥ a = b := by
  set R := LinearMap.range (mulVecLin (U - 1)) with hR
  have haM : a ∉ R ⊔ K ∙ (b - a) := by
    intro h
    obtain ⟨r, ⟨y, rfl⟩, z, hz, hrz⟩ := Submodule.mem_sup.mp h
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [mulVecLin_apply] at hrz
    have hr : (U - 1) *ᵥ y = (1 + μ) • a + (-μ) • b := by
      rw [eq_sub_iff_add_eq.mpr hrz]
      module
    have hUr : U *ᵥ ((U - 1) *ᵥ y) = (U - 1) *ᵥ y := by
      rw [hr, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb]
    have h0 := sub_one_mulVec_eq_zero hm hU y hUr
    rw [hr] at h0
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hab _ _ h0
    rw [neg_eq_zero] at h2
    rw [h2, add_zero] at h1
    exact one_ne_zero h1
  obtain ⟨f, hfa, hle⟩ := Submodule.exists_le_ker_of_notMem haM
  set φ : Fin n → K := (f a)⁻¹ • fun j => f (Pi.single j 1) with hφdef
  have hφ : ∀ x, φ ⬝ᵥ x = (f a)⁻¹ * f x := fun x => by
    rw [hφdef, smul_dotProduct, smul_eq_mul, ← apply_eq_dotProduct_single]
  have hfR : ∀ y, f ((U - 1) *ᵥ y) = 0 := fun y =>
    LinearMap.mem_ker.mp (hle (Submodule.mem_sup_left ⟨y, rfl⟩))
  have hfba : f (b - a) = 0 :=
    LinearMap.mem_ker.mp (hle (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  refine ⟨1 + replicateCol Unit (b - a) * replicateRow Unit φ, ?_, ?_, ?_⟩
  · rw [det_one_add_replicateCol_mul_replicateRow, hφ, hfba, mul_zero, add_zero]
  · refine commute_one_add_rankOne (c := 1) ?_ fun x => ?_
    · rw [Matrix.mulVec_sub, ha, hb, one_smul]
    · have h := hfR x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero] at h
      rw [hφ, hφ, h, one_mul]
  · rw [one_add_rankOne_mulVec, hφ, inv_mul_cancel₀ hfa, one_smul, add_sub_cancel]

theorem mem_ker_sub_smul_iff {T : Matrix (Fin n) (Fin n) K} {c : K} {v : Fin n → K} :
    v ∈ LinearMap.ker (mulVecLin T - c • LinearMap.id) ↔ T *ᵥ v = c • v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, mulVecLin_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem scalarMatrix_mulVec (ζ : K) (v : Fin n → K) : scalar (Fin n) ζ *ᵥ v = ζ • v := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_mem_centralizer_mulVec_eq_of_eigen {m : ℕ} (hm : (m : K) ≠ 0)
    {t : SpecialLinearGroup (Fin n) K} {ζ c : K}
    (ht : (t : Matrix (Fin n) (Fin n) K) ^ m = scalar (Fin n) ζ)
    (hdim : 2 ≤ Module.finrank K
      (LinearMap.ker (mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id)))
    {a b : Fin n → K}
    (ha : a ∈ LinearMap.ker (mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id))
    (hb : b ∈ LinearMap.ker (mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id))
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin n) K)),
      (g : Matrix (Fin n) (Fin n) K) *ᵥ a = b := by
  set T : Matrix (Fin n) (Fin n) K := (t : Matrix (Fin n) (Fin n) K) with hT
  set E := LinearMap.ker (mulVecLin T - c • LinearMap.id) with hE
  rw [mem_ker_sub_smul_iff] at ha hb
  have hc : c ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← inv_mulVec_mulVec t a, ← hT, ha, zero_smul, Matrix.mulVec_zero]
  have hcm : c ^ m = ζ := by
    have h1 := pow_mulVec_of_mulVec_eq_smul ha m
    rw [ht, scalarMatrix_mulVec] at h1
    exact (smul_left_injective K ha0 h1).symm
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin n) (Fin n) K, U = c⁻¹ • T := ⟨_, rfl⟩
  have hUm : U ^ m = 1 := by
    rw [hU, smul_pow, ht, scalar_apply, ← smul_one_eq_diagonal, smul_smul, ← hcm, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero m hc), one_smul]
  have hfix : ∀ v, T *ᵥ v = c • v → U *ᵥ v = v := fun v hv => by
    rw [hU, Matrix.smul_mulVec, hv, inv_smul_smul₀ hc]
  have hTU : T = c • U := by rw [hU, smul_inv_smul₀ hc]
  have key : ∀ x y : Fin n → K, T *ᵥ x = c • x → T *ᵥ y = c • y →
      LinearIndependent K ![x, y] →
      ∃ g ∈ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin n) K)),
        (g : Matrix (Fin n) (Fin n) K) *ᵥ x = y := by
    intro x y hx hy hxy
    obtain ⟨G, hdet, hcomm, hGx⟩ :=
      exists_det_one_commute_mulVec_eq hm hUm hxy (hfix x hx) (hfix y hy)
    refine ⟨⟨G, hdet⟩, mem_centralizer_of_coe_mul_comm ?_, hGx⟩
    change T * G = G * T
    rw [hTU, Matrix.smul_mul, Matrix.mul_smul, hcomm]
  by_cases hab : b ∈ K ∙ a
  ·
    have hnot : ¬ E ≤ K ∙ a := fun hle => by
      have := Submodule.finrank_mono hle
      rw [finrank_span_singleton ha0] at this
      omega
    obtain ⟨d, hdE, hda⟩ := Set.not_subset.mp hnot
    have hd : T *ᵥ d = c • d := mem_ker_sub_smul_iff.mp hdE
    have hspan : K ∙ b = K ∙ a := by
      obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hab
      have hμ : μ ≠ 0 := by
        rintro rfl
        exact hb0 (zero_smul K a)
      exact Submodule.span_singleton_smul_eq (IsUnit.mk0 μ hμ) a
    obtain ⟨g₁, hg₁, h₁⟩ := key a d ha hd
      (linearIndependent_pair_of_notMem (Submodule.mem_span_singleton_self a) ha0 hda)
    obtain ⟨g₂, hg₂, h₂⟩ := key d b hd hb (linearIndependent_pair_swap
      (linearIndependent_pair_of_notMem (Submodule.mem_span_singleton_self b) hb0
        (hspan ▸ hda)))
    refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂ hg₁, ?_⟩
    rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h₁, h₂]
  · exact key a b ha hb
      (linearIndependent_pair_of_notMem (Submodule.mem_span_singleton_self a) ha0 hab)

end ToralCensus

open Matrix

theorem eigenSpaceRigid_holds :
    ∀ (K : Type) [Field K] [CharP K 2] (n m : ℕ), Odd m →
      ∀ (t : Matrix.SpecialLinearGroup (Fin n) K) (ζ c : K),
        (t : Matrix (Fin n) (Fin n) K) ^ m = Matrix.scalar (Fin n) ζ →
        2 ≤ Module.finrank K (LinearMap.ker
          (Matrix.mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id)) →
        ∀ W : Submodule K (Fin n → K),
          (∀ g ∈ Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin n) K)),
            ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) →
          W ⊓ LinearMap.ker
              (Matrix.mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id) = ⊥ ∨
            LinearMap.ker (Matrix.mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id) ≤ W := by
  intro K _ _ n m hm t ζ c ht hdim W hW
  have hmK : (m : K) ≠ 0 := by
    obtain ⟨k, rfl⟩ := hm
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
      Nat.cast_one]
    exact one_ne_zero
  by_cases hWE : W ⊓ LinearMap.ker (mulVecLin (t : Matrix (Fin n) (Fin n) K) - c • LinearMap.id)
    = ⊥
  · exact Or.inl hWE
  · right
    obtain ⟨a, haWE, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWE
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact W.zero_mem
    obtain ⟨g, hg, hga⟩ :=
      ToralCensus.exists_mem_centralizer_mulVec_eq_of_eigen hmK ht hdim haWE.2 hv ha0 hv0
    rw [← hga]
    exact hW g hg a haWE.1

end CFSG.AGLEmbedding
