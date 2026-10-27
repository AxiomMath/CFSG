module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem mem_statedSU_three (h : UnitaryFieldData p f K) {x : GL (Fin 3) K}
    (hx : x ∈ StatedSU 3 (p ^ f) K) :
    (x : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      ((x : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (x : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3] at hx
  obtain ⟨hdet, hiso⟩ := hx
  refine ⟨hdet, ?_⟩
  have hfun : ((CFSG.LieType.BorelTits.unitaryInvolution K p f : K ≃+* K) : K → K) =
      (h.bar : K → K) := funext fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  simpa only [CFSG.LieType.Universal.Unitary.conjTr, hfun] using hiso

theorem eq_one_of_suppMat_scalar {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {E : Matrix ι κ K} {F : Matrix κ ι K} (hFE : F * E = 1)
    (hu : ∃ u : ι → K, u ≠ 0 ∧ F *ᵥ u = 0) {M : Matrix κ κ K} {c : K}
    (hM : suppMat E F M = c • 1) : M = 1 := by
  obtain ⟨u, hu0, hFu⟩ := hu
  have h1 : M = c • 1 := eq_smul_one_of_suppMat hFE hM
  have h2 : suppMat E F M *ᵥ u = u := by
    simp only [suppMat, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hFu,
      Matrix.mulVec_zero, add_zero]
  rw [hM, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  have hc : c = 1 := by
    by_contra hc1
    apply hu0
    have : (c - 1) • u = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
  rw [h1, hc, one_smul]

theorem not_paired_of_odd (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hodd : Odd (2 * r + ε))
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = -1) : False := by
  have hAA' := mulVecLin_mul_self hAA
  rw [← coe_unitaryOfHyp h hA] at hAA'
  obtain ⟨-, -, -, h2dim, -⟩ := exists_paired_centralizer_equiv hp
    (hypForm_isSymm h) (hypForm_separatingLeft h) hl0 hAA' hN
  rw [finrank_hypIndex_fun] at h2dim
  obtain ⟨k, hk⟩ := hodd
  omega

theorem exists_su3Hom_of_triple (h : UnitaryFieldData p f K) (hn : 4 ≤ 2 * r + ε)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {d : K}
    (v : Fin 3 → HypIndex r ε → K)
    (hAv : ∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v i = d • v i)
    (hvv : ∀ i j, hypForm h r ε (v i) (v j) = if i = j then 1 else 0) :
    ∃ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ x, hypProj h r ε (ψ x) = 1 → x = 1 := by
  classical
  set E : Matrix (HypIndex r ε) (Fin 3) K := colMat v with hE
  have hG : (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    rw [hE, gram_colMat_eq_hypForm]
    ext i j
    rw [of_apply, one_apply, hvv]
  have hGiG : (1 : Matrix (Fin 3) (Fin 3) K) * ((E.map h.bar)ᵀ * hypGram r ε K * E) = 1 := by
    rw [hG, Matrix.one_mul]
  have hGGi : ((E.map h.bar)ᵀ * hypGram r ε K * E) * (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hG, Matrix.one_mul]
  let Y : ↥(StatedSU 3 (p ^ f) K) →* Matrix (Fin 3) (Fin 3) K :=
    (Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp (StatedSU 3 (p ^ f) K).subtype
  have hY : ∀ x, ((Y x).map h.bar)ᵀ * ((E.map h.bar)ᵀ * hypGram r ε K * E) * Y x =
      (E.map h.bar)ᵀ * hypGram r ε K * E := fun x => by
    rw [hG, Matrix.mul_one]
    exact (mem_statedSU_three h x.2).2
  have hYd : ∀ x, (Y x).det = 1 := fun x => (mem_statedSU_three h x.2).1
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h hGiG hGGi Y hY hYd
  have hFE : (1 : Matrix (Fin 3) (Fin 3) K) * (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    calc (1 : Matrix (Fin 3) (Fin 3) K) * (E.map h.bar)ᵀ * hypGram r ε K * E =
        (E.map h.bar)ᵀ * hypGram r ε K * E := by simp only [Matrix.one_mul]
      _ = 1 := hG
  have hAE : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * E =
      E * (d • (1 : Matrix (Fin 3) (Fin 3) K)) := by
    rw [hE, mul_colMat, colMat_mul_smul_one]
    congr 1
    funext i
    exact hAv i
  have hFA := suppF_mul_of_isometry (mem_hypUnitary.mp hA) hAE hGiG hGGi
  refine ⟨ψ, fun x => ?_, fun x hx => ?_⟩
  · rw [hψ]
    refine mul_suppMat hAE hFA ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  ·
    rw [← MonoidHom.mem_ker, ker_hypProj] at hx
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_mem_hypScalars hx
    rw [hψ] at hc
    have hF1 : (1 : Matrix (Fin 3) (Fin 3) K) * (E.map h.bar)ᵀ * hypGram r ε K = (E.map h.bar)ᵀ * hypGram r ε K := by
      rw [Matrix.one_mul]
    have hker : ∃ u : HypIndex r ε → K, u ≠ 0 ∧
        ((1 : Matrix (Fin 3) (Fin 3) K) * (E.map h.bar)ᵀ * hypGram r ε K) *ᵥ u = 0 := by
      set F : Matrix (Fin 3) (HypIndex r ε) K := (1 : Matrix (Fin 3) (Fin 3) K) * (E.map h.bar)ᵀ * hypGram r ε K
      have hlt : finrank K (Fin 3 → K) < finrank K (HypIndex r ε → K) := by
        rw [Module.finrank_fin_fun, finrank_hypIndex_fun]
        omega
      have hne := (toLin' F).ker_ne_bot_of_finrank_lt hlt
      obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hne
      exact ⟨u, hu0, by simpa using hu⟩
    have hM1 : Y x = 1 := eq_one_of_suppMat_scalar hFE hker hc
    apply Subtype.ext
    apply Units.ext
    exact hM1

theorem exists_comm_su3Hom (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 5 ≤ 2 * r + ε)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = 1) :
    ∃ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ x, hypProj h r ε (ψ x) = 1 → x = 1 := by
  classical
  obtain ⟨d, v, hAv, hvv⟩ : ∃ (d : K) (v : Fin 3 → HypIndex r ε → K),
      (∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v i = d • v i) ∧
      ∀ i j, hypForm h r ε (v i) (v j) = if i = j then 1 else 0 := by
    have hAA' := mulVecLin_mul_self hAA
    rw [← coe_unitaryOfHyp h hA] at hAA'
    obtain ⟨-, hsepP, hsepM, -⟩ := exists_split_centralizer_equiv hp (hypForm_isSymm h)
      (hypForm_separatingLeft h) hl0 hAA' hN
    rw [coe_unitaryOfHyp] at hsepP hsepM hAA'
    have hc : IsCompl (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K)))
        (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :=
      isCompl_ker_sub_one_ker_add_one (two_ne_zero_of_odd h hp) (invSMulOp_mul_self hl0 hAA')
    have hdim := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_hypIndex_fun] at hdim
    by_cases hP : 3 ≤ finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
      (HypIndex r ε) K)))
    · have hBW := (⟨fun x y => (hypForm_isSymm h).eq x.1 y.1⟩ :
        ((hypForm h r ε).domRestrict₁₂ (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
          (HypIndex r ε) K))) (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
            (HypIndex r ε) K)))).IsSymm)
      obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBW hsepP
      refine ⟨l, fun i => (e ⟨i, by omega⟩ : HypIndex r ε → K), fun i =>
        mulVec_eq_of_mem_eigenPlus hl0 (e ⟨i, by omega⟩).2, fun i j => ?_⟩
      have := he ⟨i, by omega⟩ ⟨j, by omega⟩
      simp only [LinearMap.domRestrict₁₂_apply, Fin.mk.injEq] at this
      simpa [Fin.ext_iff] using this
    · have hM : 3 ≤ finrank K (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
          (HypIndex r ε) K))) := by omega
      have hBW := (⟨fun x y => (hypForm_isSymm h).eq x.1 y.1⟩ :
        ((hypForm h r ε).domRestrict₁₂ (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
          (HypIndex r ε) K))) (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
            (HypIndex r ε) K)))).IsSymm)
      obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBW hsepM
      refine ⟨-l, fun i => (e ⟨i, by omega⟩ : HypIndex r ε → K), fun i =>
        mulVec_eq_of_mem_eigenMinus hl0 (e ⟨i, by omega⟩).2, fun i j => ?_⟩
      have := he ⟨i, by omega⟩ ⟨j, by omega⟩
      simp only [LinearMap.domRestrict₁₂_apply, Fin.mk.injEq] at this
      simpa [Fin.ext_iff] using this
  exact exists_su3Hom_of_triple h (by omega) hA v hAv hvv

theorem exists_su3Hom_hypSU (h : UnitaryFieldData p f K) (hn : 4 ≤ 2 * r + ε) :
    ∃ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h r ε, ∀ x, hypProj h r ε (ψ x) = 1 → x = 1 := by
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hypForm_isSymm h) (hypForm_separatingLeft h)
  have hn' : 3 ≤ finrank K (HypIndex r ε → K) := by
    rw [finrank_hypIndex_fun]
    omega
  obtain ⟨ψ, -, hψ⟩ := exists_su3Hom_of_triple h hn (A := 1) (one_mem (hypUnitary h r ε)) (d := 1)
    (fun i => (e ⟨i, by omega⟩ : HypIndex r ε → K)) (fun i => by simp) (fun i j => by
      have := he ⟨i, by omega⟩ ⟨j, by omega⟩
      simpa [Fin.ext_iff] using this)
  exact ⟨ψ, hψ⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
