module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.PSL (isCompl_ker_of_sq_one)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

section Pairing

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : V →ₛₗ[h.bar] V →ₗ[K] K) {W₁ W₂ : Submodule K V}

omit [FiniteDimensional K V] in
theorem pairing_injective (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) :
    Function.Injective (fun w : W₂ => (B (w : V)).comp W₁.subtype) := by
  intro w w' hww'
  have h1 : ∀ v ∈ W₁, B ((w : V) - w') v = 0 := fun v hv => by
    have := congrArg (fun φ : W₁ →ₗ[K] K => φ ⟨v, hv⟩) hww'
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [map_sub, LinearMap.sub_apply, this, sub_self]
  exact Subtype.ext (sub_eq_zero.mp (hpair _ (sub_mem w.2 w'.2) h1))

theorem finrank_le_of_pairing (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) :
    finrank K W₂ ≤ finrank K W₁ := by
  have := h.finite
  have : Finite W₂ := Module.finite_of_finite K
  have : Finite (W₁ →ₗ[K] K) := Module.finite_of_finite K
  have hle := Nat.card_le_card_of_injective _ (pairing_injective h B hpair)
  rw [Module.natCard_eq_pow_finrank (K := K) (V := W₂),
    Module.natCard_eq_pow_finrank (K := K) (V := W₁ →ₗ[K] K), Subspace.dual_finrank_eq] at hle
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  exact (Nat.pow_le_pow_iff_right h1).1 hle

theorem exists_of_pairing (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0)
    (hdim : finrank K W₂ = finrank K W₁) (φ : W₁ →ₗ[K] K) :
    ∃ w ∈ W₂, ∀ v : W₁, B w v = φ v := by
  have := h.finite
  have : Finite W₂ := Module.finite_of_finite K
  have : Finite (W₁ →ₗ[K] K) := Module.finite_of_finite K
  have hcard : Nat.card W₂ = Nat.card (W₁ →ₗ[K] K) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := W₂),
      Module.natCard_eq_pow_finrank (K := K) (V := W₁ →ₗ[K] K), Subspace.dual_finrank_eq, hdim]
  obtain ⟨w, hw⟩ := ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨pairing_injective h B hpair, hcard⟩).2 φ
  exact ⟨w, w.2, fun v => by rw [← hw]; rfl⟩

end Pairing

theorem stdHermForm_mulVec_neg {A : Matrix (Fin n) (Fin n) K} (hA : (A.map h.bar)ᵀ * A = -1)
    (x y : Fin n → K) : stdHermForm h n (A *ᵥ x) (A *ᵥ y) = -stdHermForm h n x y := by
  rw [stdHermForm_eq_dotProduct, stdHermForm_eq_dotProduct]
  have e : (fun i => h.bar ((A *ᵥ x) i)) = (A.map h.bar) *ᵥ (fun i => h.bar (x i)) := by
    funext i
    simp only [mulVec, dotProduct, map_sum, map_mul, map_apply]
  rw [e, ← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, hA, vecMul_neg, vecMul_one,
    neg_dotProduct]

theorem antiunitary_eigen (h2 : (2 : K) ≠ 0) {A : Matrix (Fin n) (Fin n) K}
    (hA : (A.map h.bar)ᵀ * A = -1) (hAA : A * A = 1) :
    IsCompl (LinearMap.ker (Matrix.toLin' A - 1)) (LinearMap.ker (Matrix.toLin' A + 1)) ∧
    (∀ v ∈ LinearMap.ker (Matrix.toLin' A - 1), A *ᵥ v = v) ∧
    (∀ v ∈ LinearMap.ker (Matrix.toLin' A + 1), A *ᵥ v = -v) ∧
    (∀ v ∈ LinearMap.ker (Matrix.toLin' A - 1), ∀ w ∈ LinearMap.ker (Matrix.toLin' A - 1),
      stdHermForm h n v w = 0) ∧
    (∀ v ∈ LinearMap.ker (Matrix.toLin' A + 1), ∀ w ∈ LinearMap.ker (Matrix.toLin' A + 1),
      stdHermForm h n v w = 0) ∧
    (∀ w ∈ LinearMap.ker (Matrix.toLin' A + 1),
      (∀ v ∈ LinearMap.ker (Matrix.toLin' A - 1), stdHermForm h n w v = 0) → w = 0) ∧
    (∀ w ∈ LinearMap.ker (Matrix.toLin' A - 1),
      (∀ v ∈ LinearMap.ker (Matrix.toLin' A + 1), stdHermForm h n w v = 0) → w = 0) := by
  set T := Matrix.toLin' A with hT
  have hTT : T * T = 1 := by
    rw [hT, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, Matrix.toLin'_one]
    rfl
  set Vp := LinearMap.ker (T - 1) with hVp
  set Vm := LinearMap.ker (T + 1) with hVm
  have hc : IsCompl Vp Vm := isCompl_ker_of_sq_one h2 hTT
  have hp : ∀ v ∈ Vp, A *ᵥ v = v := by
    intro v hv
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have hm : ∀ v ∈ Vm, A *ᵥ v = -v := by
    intro v hv
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hv
    exact eq_neg_of_add_eq_zero_left hv
  set B := stdHermForm h n with hB
  have hiso : ∀ (s : K), (s = 1 ∨ s = -1) → ∀ v w : Fin n → K, A *ᵥ v = s • v →
      A *ᵥ w = s • w → B v w = 0 := by
    intro s hs v w hv hw
    have e := stdHermForm_mulVec_neg h hA v w
    rw [hv, hw, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul] at e
    have hss : h.bar s * s = 1 := by rcases hs with rfl | rfl <;> simp
    rw [← mul_assoc, hss, one_mul] at e
    have : (2 : K) * B v w = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_left h2
  have hisoP : ∀ v ∈ Vp, ∀ w ∈ Vp, B v w = 0 := fun v hv w hw =>
    hiso 1 (Or.inl rfl) v w (by rw [hp v hv, one_smul]) (by rw [hp w hw, one_smul])
  have hisoM : ∀ v ∈ Vm, ∀ w ∈ Vm, B v w = 0 := fun v hv w hw =>
    hiso (-1) (Or.inr rfl) v w (by rw [hm v hv, neg_one_smul]) (by rw [hm w hw, neg_one_smul])
  have hpair : ∀ (W W' : Submodule K (Fin n → K)), IsCompl W W' →
      (∀ v ∈ W, ∀ w ∈ W, B v w = 0) → ∀ w ∈ W, (∀ v ∈ W', B w v = 0) → w = 0 := by
    intro W W' hWW' hWiso w hw h0
    apply stdHermForm_separatingLeft h n
    intro x
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hWW'.sup_eq_top ▸ Submodule.mem_top :
      x ∈ W ⊔ W')
    rw [map_add, hWiso w hw y hy, h0 z hz, add_zero]
  exact ⟨hc, hp, hm, hisoP, hisoM, hpair Vm Vp hc.symm hisoM, hpair Vp Vm hc hisoP⟩

theorem exists_half_of_antiunitary (h2 : (2 : K) ≠ 0) {A : Matrix (Fin n) (Fin n) K}
    (hA : (A.map h.bar)ᵀ * A = -1) (hAA : A * A = 1) : ∃ m, n = m + m := by
  obtain ⟨hc, -, -, -, -, hpM, hpP⟩ := antiunitary_eigen h h2 hA hAA
  have e1 := finrank_le_of_pairing h (stdHermForm h n) hpM
  have e2 := finrank_le_of_pairing h (stdHermForm h n) hpP
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at hsum
  exact ⟨finrank K (LinearMap.ker (Matrix.toLin' A - 1)), by omega⟩

theorem exists_paired_unitary_normal_form (h2 : (2 : K) ≠ 0) {m : ℕ}
    {A : Matrix (Fin (m + m)) (Fin (m + m)) K}
    (hA : (A.map h.bar)ᵀ * A = -1) (hAA : A * A = 1) {l : K} (hl : l ≠ 0)
    (hN : h.norm l = -1) :
    ∃ H : Matrix (Fin (m + m)) (Fin (m + m)) K, (H.map h.bar)ᵀ * H = 1 ∧
      A * H = H * prFin K m (fromBlocks 0 (l⁻¹ • 1) (l • 1) 0) := by
  obtain ⟨hc, hp, hm, hisoP, hisoM, hpM, hpP⟩ := antiunitary_eigen h h2 hA hAA
  set Vp := LinearMap.ker (Matrix.toLin' A - 1) with hVp
  set Vm := LinearMap.ker (Matrix.toLin' A + 1) with hVm
  set B := stdHermForm h (m + m) with hB
  have e1 := finrank_le_of_pairing h B hpM
  have e2 := finrank_le_of_pairing h B hpP
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at hsum
  have hdP : finrank K Vp = m := by omega
  have hdM : finrank K Vm = finrank K Vp := by omega
  set b := Module.finBasisOfFinrankEq K Vp hdP with hb
  have hex : ∀ j : Fin m, ∃ w ∈ Vm, ∀ v : Vp, B w v = b.coord j v := fun j =>
    exists_of_pairing h B hpM hdM (b.coord j)
  choose d hdmem hdB using hex
  have hbb : ∀ i j, B (b i : Fin (m + m) → K) (b j) = 0 := fun i j =>
    hisoP _ (b i).2 _ (b j).2
  have hdd : ∀ i j, B (d i) (d j) = 0 := fun i j => hisoM _ (hdmem i) _ (hdmem j)
  have hdb : ∀ i j, B (d i) (b j : Fin (m + m) → K) = if i = j then 1 else 0 := fun i j => by
    rw [hdB i (b j), Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  have hbd : ∀ i j, B (b i : Fin (m + m) → K) (d j) = if i = j then 1 else 0 := fun i j => by
    rw [← (stdHermForm_isSymm h _).eq, hdb j i]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hb2 : h.bar ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hNl : h.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN, inv_neg, inv_one]
  set f₁ : Fin m → (Fin (m + m) → K) := fun i => (b i : Fin (m + m) → K) + (2 : K)⁻¹ • d i
    with hf₁
  set f₂ : Fin m → (Fin (m + m) → K) := fun i =>
    l⁻¹ • ((b i : Fin (m + m) → K) - (2 : K)⁻¹ • d i) with hf₂
  set fv : Fin m ⊕ Fin m → (Fin (m + m) → K) := Sum.elim f₁ f₂ with hfv
  have hgram : ∀ x y, B (fv x) (fv y) = if x = y then 1 else 0 := by
    rintro (i | i) (j | j)
    · simp only [hfv, Sum.elim_inl, hf₁, map_add, LinearMap.map_smulₛₗ₂, map_smul,
        LinearMap.add_apply, smul_eq_mul, hbb, hdd, hdb, hbd, hb2,
        Sum.inl.injEq]
      split_ifs <;> field_simp <;> ring
    · simp only [hfv, Sum.elim_inl, Sum.elim_inr, hf₁, hf₂, map_add, map_sub,
        LinearMap.map_smulₛₗ₂, map_smul, LinearMap.add_apply,
        smul_eq_mul, hbb, hdd, hdb, hbd, hb2, reduceCtorEq, ↓reduceIte]
      split_ifs <;> ring
    · simp only [hfv, Sum.elim_inl, Sum.elim_inr, hf₁, hf₂, map_add, map_sub,
        LinearMap.map_smulₛₗ₂, map_smul, LinearMap.sub_apply,
        smul_eq_mul, hbb, hdd, hdb, hbd, hb2, reduceCtorEq, ↓reduceIte]
      split_ifs <;> ring
    · simp only [hfv, Sum.elim_inr, hf₂, map_sub, LinearMap.map_smulₛₗ₂, map_smul,
        LinearMap.sub_apply, smul_eq_mul, hbb, hdd, hdb, hbd, hb2,
        Sum.inr.injEq]
      split_ifs
      · have h2i : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
        linear_combination (-1 : K) * hNl - l⁻¹ * h.bar l⁻¹ * h2i
      · ring
  have hAb : ∀ i, A *ᵥ (b i : Fin (m + m) → K) = b i := fun i => hp _ (b i).2
  have hAd : ∀ i, A *ᵥ d i = -d i := fun i => hm _ (hdmem i)
  have hAf₁ : ∀ i, A *ᵥ f₁ i = l • f₂ i := by
    intro i
    simp only [hf₁, hf₂, mulVec_add, mulVec_smul, hAb, hAd, smul_smul, mul_inv_cancel₀ hl,
      one_smul, smul_neg, ← sub_eq_add_neg]
  have hAf₂ : ∀ i, A *ᵥ f₂ i = l⁻¹ • f₁ i := by
    intro i
    simp only [hf₁, hf₂, mulVec_smul, mulVec_sub, hAb, hAd, smul_neg, sub_neg_eq_add]
  set H : Matrix (Fin (m + m)) (Fin (m + m)) K :=
    Matrix.of fun r c => fv (finSumFinEquiv.symm c) r with hH
  refine ⟨H, ?_, ?_⟩
  · ext c c'
    have e := hgram (finSumFinEquiv.symm c) (finSumFinEquiv.symm c')
    rw [hB, stdHermForm_apply] at e
    rw [Matrix.mul_apply, one_apply]
    simp only [transpose_apply, map_apply, hH, of_apply]
    rw [e]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  · ext r c
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective c
    have e2 : (A * H) r (finSumFinEquiv x) = (A *ᵥ fv x) r := by
      rw [Matrix.mul_apply, mulVec, dotProduct]
      simp only [hH, of_apply, Equiv.symm_apply_apply]
    rw [e2, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv]
    simp only [prFin_apply, hH, of_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type]
    rcases x with j | j
    · simp only [hfv, Sum.elim_inl, Sum.elim_inr, hAf₁, fromBlocks_apply₁₁, fromBlocks_apply₂₁,
        Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.smul_apply,
        one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Pi.smul_apply]
      ring
    · simp only [hfv, Sum.elim_inl, Sum.elim_inr, hAf₂, fromBlocks_apply₁₂, fromBlocks_apply₂₂,
        Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, Matrix.smul_apply,
        one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Pi.smul_apply]
      ring

end CFSG.ComponentClassification.Burgoyne.U
