module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag Module
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem exists_conj_eq_toMatrix (b : Basis (Fin n) K (Fin n → K)) (B : GL (Fin n) K) :
    ∃ H : GL (Fin n) K, (H : Matrix (Fin n) (Fin n) K) * B * ((H⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix b b (Matrix.toLin' (B : Matrix _ _ K)) := by
  set e := Pi.basisFun K (Fin n)
  refine ⟨⟨b.toMatrix e, e.toMatrix b, b.toMatrix_mul_toMatrix_flip e,
    e.toMatrix_mul_toMatrix_flip b⟩, ?_⟩
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b
    (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h
  set Mb := LinearMap.toMatrix b b (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))
  change b.toMatrix e * (B : Matrix (Fin n) (Fin n) K) * e.toMatrix b = Mb
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, b.toMatrix_mul_toMatrix_flip, Matrix.one_mul,
    Matrix.mul_assoc, b.toMatrix_mul_toMatrix_flip, Matrix.mul_one]

theorem isCompl_ker_of_sq_one {V : Type*} [AddCommGroup V] [Module K V] (h2 : (2 : K) ≠ 0)
    {f : Module.End K V} (hf : f * f = 1) :
    IsCompl (LinearMap.ker (f - 1)) (LinearMap.ker (f + 1)) := by
  have hf' : ∀ v, f (f v) = v := fun v => by
    have := congrArg (fun g : Module.End K V => g v) hf
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at h2'
    rw [h1] at h2'
    have : (2 : K) • v = 0 := by rw [two_smul]; exact h2'
    exact (smul_eq_zero.1 this).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (2 : K)⁻¹ • (v + f v) + (2 : K)⁻¹ • (v - f v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hf',
        sub_eq_zero, add_comm]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hf',
        ← smul_add]
      simp

theorem exists_split_normal_form (hK : ringChar K ≠ 2) {A : GL (Fin n) K} {μ : Kˣ}
    (hA : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ))
    (hns : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin n) c) :
    ∃ (H : GL (Fin n) K) (J : Finset (Fin n)) (a b : Fin n), a ∈ J ∧ b ∉ J ∧
      H * A * H⁻¹ = GeneralLinearGroup.scalar (Fin n) μ * signGL K J := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsc : ∀ (c : Kˣ) (Z : GL (Fin n) K), Commute (GeneralLinearGroup.scalar (Fin n) c) Z :=
    fun c Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
  set B := GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A with hBdef
  have hBB : B * B = 1 := by
    rw [hBdef, mul_assoc, ← mul_assoc A, ← (hsc μ⁻¹ A).eq, mul_assoc, hA, ← mul_assoc,
      ← map_mul, ← map_mul]
    rw [show μ⁻¹ * μ⁻¹ * (μ * μ) = 1 by group, map_one]
  set f := Matrix.toLin' (B : Matrix (Fin n) (Fin n) K) with hf
  have hff : f * f = 1 := by
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Units.val_mul, hBB, Units.val_one,
      Matrix.toLin'_one]
    rfl
  set Vp := LinearMap.ker (f - 1) with hVp
  set Vm := LinearMap.ker (f + 1) with hVm
  have hc : IsCompl Vp Vm := isCompl_ker_of_sq_one h2 hff
  set bp := ((Module.finBasis K Vp).prod (Module.finBasis K Vm)).map
    (Submodule.prodEquivOfIsCompl Vp Vm hc) with hbp
  set e := bp.indexEquiv (Pi.basisFun K (Fin n)) with he
  set bb := bp.reindex e with hbb
  set J : Finset (Fin n) := Finset.univ.filter fun l => (e.symm l).isRight with hJ
  have hinl : ∀ i, bp (Sum.inl i) = ((Module.finBasis K Vp) i : Fin n → K) := fun i => by
    simp [hbp, Basis.prod_apply]
  have hinr : ∀ i, bp (Sum.inr i) = ((Module.finBasis K Vm) i : Fin n → K) := fun i => by
    simp [hbp, Basis.prod_apply]
  have hfb : ∀ l, f (bb l) = (if l ∈ J then (-1 : K) else 1) • bb l := by
    intro l
    rw [hbb, Basis.reindex_apply]
    rcases hl : e.symm l with i | i
    · have hlJ : l ∉ J := by simp [hJ, hl]
      simp only [hlJ, ↓reduceIte, one_smul, hinl]
      have := ((Module.finBasis K Vp) i).2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    · have hlJ : l ∈ J := by simp [hJ, hl]
      simp only [hlJ, ↓reduceIte, neg_one_smul, hinr]
      have := ((Module.finBasis K Vm) i).2
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at this
      exact eq_neg_of_add_eq_zero_left this
  have hD : LinearMap.toMatrix bb bb f = signMat K J := by
    ext k l
    rw [LinearMap.toMatrix_apply, hfb, map_smul, Basis.repr_self, signMat, diagonal_apply]
    by_cases hkl : k = l
    · subst hkl
      split_ifs <;> simp_all
    · split_ifs <;> simp [hkl]
  obtain ⟨H, hH⟩ := exists_conj_eq_toMatrix bb B
  rw [← hf, hD] at hH
  have hHB : H * B * H⁻¹ = signGL K J := Units.ext hH
  have hAB : A = GeneralLinearGroup.scalar (Fin n) μ * B := by
    rw [hBdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hfA : ∀ c : Kˣ, (∀ v, f v = (c : K) • v) → False := by
    intro c hc
    apply hns (μ * c)
    have hBc : B = GeneralLinearGroup.scalar (Fin n) c := by
      apply Units.ext
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [← hf, hc v, Matrix.toLin'_apply]
      ext i
      simp [GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct, Matrix.scalar_apply,
        diagonal_apply]
    rw [hAB, hBc, ← map_mul]
  have hrk : 0 < Module.finrank K Vm ∧ 0 < Module.finrank K Vp := by
    constructor
    · by_contra h0
      push Not at h0
      have hbot : Vm = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
      have htop : Vp = ⊤ := by
        have := hc.sup_eq_top
        rwa [hbot, sup_bot_eq] at this
      refine hfA 1 fun v => ?_
      have hv : v ∈ Vp := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      rw [hv, Units.val_one, one_smul]
    · by_contra h0
      push Not at h0
      have hbot : Vp = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
      have htop : Vm = ⊤ := by
        have := hc.sup_eq_top
        rwa [hbot, bot_sup_eq] at this
      refine hfA (-1) fun v => ?_
      have hv : v ∈ Vm := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hv
      rw [eq_neg_of_add_eq_zero_left hv, Units.val_neg, Units.val_one, neg_one_smul]
  refine ⟨H, J, e (Sum.inr ⟨0, hrk.1⟩), e (Sum.inl ⟨0, hrk.2⟩), by simp [hJ], by simp [hJ], ?_⟩
  rw [hAB, ← mul_assoc, ← (hsc μ H).eq, mul_assoc, mul_assoc, ← mul_assoc H, ← hHB]

end CFSG.ComponentClassification.Burgoyne.PSL