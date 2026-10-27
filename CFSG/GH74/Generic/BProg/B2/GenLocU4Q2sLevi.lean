module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2sSL2
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2sPsi
public import CFSG.Sporadic.ThSchreier.GlobalData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open GenLocU4Basic GenLocU4Q2sPsi

namespace GenLocU4Q2sLevi

variable {K : Type} [Field K]

@[expose] def astar (bar : K →+* K) (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![bar (A 1 1), -bar (A 1 0); -bar (A 0 1), bar (A 0 0)]

section Astar

variable (bar : K →+* K)

theorem astar_one : astar bar (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [astar]

theorem astar_mul (A B : Matrix (Fin 2) (Fin 2) K) : astar bar (A * B) = astar bar A * astar bar B := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [astar, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem astar_smul (c : K) (A : Matrix (Fin 2) (Fin 2) K) : astar bar (c • A) = bar c • astar bar A := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [astar]

theorem det_astar (A : Matrix (Fin 2) (Fin 2) K) : (astar bar A).det = bar A.det := by
  simp [astar, Matrix.det_fin_two]
  ring

theorem star_mul_astar (A : Matrix (Fin 2) (Fin 2) K) : (A.map bar)ᵀ * astar bar A = bar A.det • 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [astar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem astar_star_mul (hbb : ∀ c, bar (bar c) = c) (A : Matrix (Fin 2) (Fin 2) K) :
    ((astar bar A).map bar)ᵀ * A = A.det • 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [astar, hbb, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem astar_real (A : Matrix (Fin 2) (Fin 2) K) (hA : A.map bar = A) :
    A * X2 = X2 * astar bar A ∧ astar bar A * X2 = X2 * A := by
  have e00 : bar (A 0 0) = A 0 0 := congrFun (congrFun hA 0) 0
  have e01 : bar (A 0 1) = A 0 1 := congrFun (congrFun hA 0) 1
  have e10 : bar (A 1 0) = A 1 0 := congrFun (congrFun hA 1) 0
  have e11 : bar (A 1 1) = A 1 1 := congrFun (congrFun hA 1) 1
  constructor <;>
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [astar, X2, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]

theorem map_X2 : (X2 : Matrix (Fin 2) (Fin 2) K).map bar = X2 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [X2]

theorem transpose_X2 : (X2 : Matrix (Fin 2) (Fin 2) K)ᵀ = -X2 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [X2]

end Astar

theorem X2_mul_X2 : (X2 : Matrix (Fin 2) (Fin 2) K) * X2 = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [X2, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_of_mul_X2 {M N : Matrix (Fin 2) (Fin 2) K} (h : M * X2 = N * X2) : M = N := by
  have := congrArg (· * X2) h
  simpa [Matrix.mul_assoc, X2_mul_X2] using this

theorem eq_of_X2_mul {M N : Matrix (Fin 2) (Fin 2) K} (h : X2 * M = X2 * N) : M = N := by
  have := congrArg (X2 * ·) h
  simpa [← Matrix.mul_assoc, X2_mul_X2] using this

theorem astar_eq_smul (bar : K →+* K) (A B : Matrix (Fin 2) (Fin 2) K) (h : (A.map bar)ᵀ * B = 1) :
    astar bar A = bar A.det • B := by
  have hBA : B * (A.map bar)ᵀ = 1 := mul_eq_one_comm.1 h
  calc astar bar A = (B * (A.map bar)ᵀ) * astar bar A := by rw [hBA, Matrix.one_mul]
    _ = B * ((A.map bar)ᵀ * astar bar A) := by rw [Matrix.mul_assoc]
    _ = bar A.det • B := by rw [star_mul_astar, Matrix.mul_smul, Matrix.mul_one]

theorem smul_one_star (bar : K →+* K) (c : K) :
    (((c • (1 : Matrix (Fin 2) (Fin 2) K)).map bar)ᵀ) = bar c • 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp

abbrev gMat {q : ℕ} (g : ↥(StatedSU 4 q K)) : Matrix (Fin 4) (Fin 4) K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

section Elements

variable {p f : ℕ}

@[expose] noncomputable def suOf (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) (hdet : M.det = 1) :
    ↥(StatedSU 4 q K) :=
  ⟨⟨M, (M.map (· ^ q))ᵀ, mul_eq_one_comm.1 hM, hM⟩, Subgroup.subset_closure ⟨hdet, hM⟩⟩

theorem gMat_suOf (q : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) (hdet : M.det = 1) :
    gMat (suOf q M hM hdet) = M := rfl

theorem unitary_det_of_mem [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (g : ↥(StatedSU 4 (p ^ f) K)) :
    IsUnitaryU (p ^ f) (gMat g) ∧ (gMat g).det = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hmem : ((g : GL (Fin 4) K)) ∈ SUid (unitaryInvolution K p f) 4 := by
    rw [SUid_eq_statedSU hK 4]
    exact g.2
  have hσ : (⇑(unitaryInvolution K p f) : K → K) = fun x => x ^ (p ^ f) :=
    funext (unitaryInvolution_apply K p f)
  have h2 := (mem_SUid.1 hmem).2
  unfold conjTr at h2
  rw [hσ] at h2
  exact ⟨h2, (mem_SUid.1 hmem).1⟩

theorem exists_sq_of_fixed [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {d : K} (hd0 : d ≠ 0) (hd : d ^ (p ^ f) = d) : ∃ l : K, l * l = d := by
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hring : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
  have hc : Fintype.card K / 2 = 4 * k * (2 * k + 1) := by
    rw [← Nat.card_eq_fintype_card, hK, hk]
    have : (4 * k + 1) ^ 2 = 2 * (4 * k * (2 * k + 1)) + 1 := by ring
    rw [this]
    omega
  have hd1 : d ^ (4 * k) = 1 := by
    have h1 : d ^ (4 * k + 1) = d := by rw [← hk]; exact hd
    have h' : d * d ^ (4 * k) = d * 1 := by rw [mul_one, ← pow_succ']; exact h1
    exact mul_left_cancel₀ hd0 h'
  obtain ⟨l, hl⟩ := (FiniteField.isSquare_iff hring hd0).2 (by rw [hc, pow_mul, hd1, one_pow])
  exact ⟨l, hl.symm⟩

end Elements

section Phi

variable {q : ℕ} (bar : K →+* K) {i : K}

theorem isUnitaryU_iff_bar (hbar : ∀ c, bar c = c ^ q) (M : Matrix (Fin 4) (Fin 4) K) :
    IsUnitaryU q M ↔ (M.map bar)ᵀ * M = 1 := by
  have hf : (fun x : K => x ^ q) = ⇑bar := funext fun c => (hbar c).symm
  unfold IsUnitaryU
  rw [hf]

theorem psi_astar_unitary (hbar : ∀ c, bar c = c ^ q) (hbb : ∀ c, bar (bar c) = c) (hi : i * i = -1)
    (hbi : bar i = i) (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    IsUnitaryU q (psi i A (astar bar A)) := by
  rw [isUnitaryU_iff_bar bar hbar, psi_unitary_iff hi h2 bar hbi]
  refine ⟨?_, ?_⟩
  · rw [star_mul_astar, hA, map_one, one_smul]
  · rw [astar_star_mul bar hbb, hA, one_smul]

theorem det_psi_astar (hi : i * i = -1) (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    (psi i A (astar bar A)).det = 1 := by
  rw [psi_det hi h2, det_astar, hA, map_one, mul_one]

@[expose] noncomputable def phi (hbar : ∀ c, bar c = c ^ q) (hbb : ∀ c, bar (bar c) = c) (hi : i * i = -1)
    (hbi : bar i = i) (h2 : (2 : K) ≠ 0) : SL(2, K) →* ↥(StatedSU 4 q K) where
  toFun A := suOf q (psi i (A : Matrix (Fin 2) (Fin 2) K) (astar bar (A : Matrix (Fin 2) (Fin 2) K)))
    (psi_astar_unitary bar hbar hbb hi hbi h2 A.2) (det_psi_astar bar hi h2 A.2)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp only [gMat_suOf, Matrix.SpecialLinearGroup.coe_one, astar_one, psi_one hi h2]
    rfl
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, astar_mul, ← psi_mul hi h2]
    rfl

end Phi

theorem z_blocks {i : K} (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (bar : K →+* K) (hbi : bar i = i)
    {z : Matrix (Fin 4) (Fin 4) K} (hzU : (z.map bar)ᵀ * z = 1) (hz : z * z = 1)
    (hzx : z * (GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) = GenLocU4Out.xi * z) (hzy : z * yM = yM * z)
    (hzn : ∀ c : K, z ≠ c • 1) :
    ∃ Az Bz : Matrix (Fin 2) (Fin 2) K, z = psi i Az Bz ∧ (Az.map bar)ᵀ * Bz = 1 ∧ (Bz.map bar)ᵀ * Az = 1 ∧
      Az * Az = 1 ∧ Bz * Bz = 1 ∧ Az * X2 = X2 * Bz ∧ Bz * X2 = X2 * Az ∧ ∀ c : K, Az ≠ c • 1 := by
  obtain ⟨Az, Bz, rfl⟩ := exists_psi_of_comm hi h2 hzx
  obtain ⟨u1, u2⟩ := (psi_unitary_iff hi h2 bar hbi Az Bz).1 hzU
  rw [psi_mul hi h2, ← psi_one hi h2] at hz
  obtain ⟨s1, s2⟩ := psi_inj hi h2 hz
  rw [yM_eq hi h2, psi_mul_psiO hi h2, psiO_mul_psi hi h2] at hzy
  obtain ⟨c1, c2⟩ := psiO_inj hi h2 hzy
  refine ⟨Az, Bz, rfl, u1, u2, s1, s2, c1, c2, fun c hc => hzn c ?_⟩
  have hB : Bz = c • 1 := by
    apply eq_of_mul_X2
    rw [c2, hc]
    simp
  rw [hc, hB]
  exact psi_smul_one hi h2 c

theorem five_le_of_mod_four' [Finite K] {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    5 ≤ p ^ f := by
  have hne : p ^ f ≠ 1 := by
    intro h1
    rw [h1] at hK
    have : Nat.card K = 1 := by simpa using hK
    exact (not_subsingleton K) (Nat.card_eq_one_iff_unique.1 this).1
  omega

end GenLocU4Q2sLevi

namespace GenLocU4Q2s

open GenLocU4Q2sLevi

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem cx_le_of_hyp_yM (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (z : Matrix (Fin 4) (Fin 4) K) (hzU : IsUnitaryU (p ^ f) z)
    (hz : z * z = 1) (hzx : z * GenLocU4Out.xi = GenLocU4Out.xi * z) (hzy : z * yM = yM * z)
    (hzn : ∀ c : K, z ≠ c • 1)
    (hxy : ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * GenLocU4Out.xi = GenLocU4Out.xi * gMat g →
      gMat g * yM = yM * gMat g → g ∈ Γ)
    (hxz : ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * GenLocU4Out.xi = GenLocU4Out.xi * gMat g →
      gMat g * z = z * gMat g → g ∈ Γ)
    (hxyz : ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * GenLocU4Out.xi = GenLocU4Out.xi * gMat g →
      gMat g * (yM * z) = (yM * z) * gMat g → g ∈ Γ) :
    ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * GenLocU4Out.xi = GenLocU4Out.xi * gMat g → g ∈ Γ := by
  have hdata := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨bar, hbar, hbb⟩ : ∃ bar : K →+* K, (∀ c, bar c = c ^ (p ^ f)) ∧ ∀ c, bar (bar c) = c :=
    ⟨hdata.bar, fun c => rfl, hdata.bar_bar⟩
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have h5 : 5 ≤ p ^ f := five_le_of_mod_four' hK hq
  obtain ⟨i, hi⟩ : ∃ i : K, i * i = -1 := by
    have := Fintype.ofFinite K
    have h4 : Fintype.card K % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hK, Nat.pow_mod, hq]
      norm_num
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨r, hr.symm⟩
  have hbi : bar i = i := by
    rw [hbar]
    exact GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hi
  have hfun : (fun x : K => x ^ (p ^ f)) = ⇑bar := funext fun c => (hbar c).symm
  have hzU' : (z.map bar)ᵀ * z = 1 := (isUnitaryU_iff_bar bar hbar z).1 hzU
  obtain ⟨Az, Bz, hzAB, u1, u2, s1, s2, c1, c2, hAn⟩ := z_blocks hi h2 bar hbi hzU' hz hzx hzy hzn
  have hAs : (Az.map bar)ᵀ = Bz := by
    calc (Az.map bar)ᵀ = (Az.map bar)ᵀ * (Bz * Bz) := by rw [s2, Matrix.mul_one]
      _ = ((Az.map bar)ᵀ * Bz) * Bz := by rw [Matrix.mul_assoc]
      _ = Bz := by rw [u1, Matrix.one_mul]
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin 2) (Fin 2) K, S = X2 * Az := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin 2) (Fin 2) K, T = Az * X2 := ⟨_, rfl⟩
  have hSbar : (S.map bar)ᵀ = -S := by
    rw [hSdef, Matrix.map_mul, Matrix.transpose_mul, hAs, map_X2, transpose_X2, Matrix.mul_neg, c2]
  have hSX : ∀ c : K, S ≠ c • X2 := by
    intro c hc
    apply hAn c
    apply eq_of_X2_mul
    rw [← hSdef, hc]
    simp
  have hST : S * T = -1 := by
    rw [hSdef, hTdef]
    calc X2 * Az * (Az * X2) = X2 * (Az * Az) * X2 := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [s1, Matrix.mul_one, X2_mul_X2]
  have hTS : T * S = -1 := by
    rw [hSdef, hTdef]
    calc Az * X2 * (X2 * Az) = Az * (X2 * X2) * Az := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [X2_mul_X2]; simp [s1]
  let φ := phi bar hbar hbb hi hbi h2
  have hφ : ∀ A : SL(2, K), gMat (φ A) =
      psi i (A : Matrix (Fin 2) (Fin 2) K) (astar bar (A : Matrix (Fin 2) (Fin 2) K)) := fun A => rfl
  have hreal : ∀ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)) = A → A ∈ Γ.comap φ := by
    intro A hA
    rw [hfun] at hA
    obtain ⟨r1, r2⟩ := astar_real bar (A : Matrix (Fin 2) (Fin 2) K) hA
    rw [Subgroup.mem_comap]
    apply hxy (φ A)
    · rw [hφ]
      exact (psi_xi hi h2 _ _).symm
    · rw [hφ, yM_eq hi h2, psi_mul_psiO hi h2, psiO_mul_psi hi h2, r1, r2]
  have hSU : ∀ A : SL(2, K), ((A : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * S * A = S → A ∈ Γ.comap φ := by
    intro A hA
    rw [hfun] at hA
    have hAB : ((A : Matrix (Fin 2) (Fin 2) K).map bar)ᵀ * astar bar (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [star_mul_astar, A.2, map_one, one_smul]
    have hBA : astar bar (A : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K).map bar)ᵀ = 1 :=
      mul_eq_one_comm.1 hAB
    have cond2 : astar bar (A : Matrix (Fin 2) (Fin 2) K) * S = S * A := by
      calc astar bar (A : Matrix (Fin 2) (Fin 2) K) * S
          = astar bar (A : Matrix (Fin 2) (Fin 2) K) *
              (((A : Matrix (Fin 2) (Fin 2) K).map bar)ᵀ * S * A) := by rw [hA]
        _ = (astar bar (A : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K).map bar)ᵀ) * S * A := by
            simp only [Matrix.mul_assoc]
        _ = S * A := by rw [hBA, Matrix.one_mul]
    have cond1 : (A : Matrix (Fin 2) (Fin 2) K) * T = T * astar bar (A : Matrix (Fin 2) (Fin 2) K) := by
      symm
      calc T * astar bar (A : Matrix (Fin 2) (Fin 2) K)
          = -(T * astar bar (A : Matrix (Fin 2) (Fin 2) K) * (S * T)) := by rw [hST]; simp
        _ = -(T * (astar bar (A : Matrix (Fin 2) (Fin 2) K) * S) * T) := by simp only [Matrix.mul_assoc]
        _ = -(T * (S * A) * T) := by rw [cond2]
        _ = -((T * S) * A * T) := by simp only [Matrix.mul_assoc]
        _ = A * T := by rw [hTS]; simp
    rw [Subgroup.mem_comap]
    apply hxyz (φ A)
    · rw [hφ]
      exact (psi_xi hi h2 _ _).symm
    · rw [hφ, yM_eq hi h2, hzAB, psiO_mul_psi hi h2, psi_mul_psiO hi h2, psiO_mul_psi hi h2, ← c1, ← hTdef,
        ← hSdef, cond1, cond2]
  have hS' : (S.map (· ^ (p ^ f)))ᵀ = -S := by rw [hfun]; exact hSbar
  have hH : Γ.comap φ = ⊤ :=
    sl2_eq_top_of_two_forms_of_five_le hp hK h5 (Γ.comap φ) hreal S hS' hSX hSU
  have hall : ∀ A : SL(2, K), φ A ∈ Γ := fun A => by
    have : A ∈ Γ.comap φ := by rw [hH]; trivial
    exact this
  intro g hg
  obtain ⟨hgU, hgdet⟩ := unitary_det_of_mem hp hK g
  obtain ⟨A, B, hgAB⟩ := exists_psi_of_comm hi h2 hg
  have hgU' : ((gMat g).map bar)ᵀ * gMat g = 1 := (isUnitaryU_iff_bar bar hbar _).1 hgU
  rw [hgAB] at hgU' hgdet
  obtain ⟨v1, v2⟩ := (psi_unitary_iff hi h2 bar hbi A B).1 hgU'
  rw [psi_det hi h2] at hgdet
  have hd0 : A.det ≠ 0 := left_ne_zero_of_mul_eq_one hgdet
  have hB0 : B.det ≠ 0 := right_ne_zero_of_mul_eq_one hgdet
  have hdet_star : ((A.map bar)ᵀ).det = bar A.det := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hbd : bar A.det * B.det = 1 := by
    have := congrArg Matrix.det v1
    rwa [Matrix.det_mul, hdet_star, Matrix.det_one] at this
  have hdfix : bar A.det = A.det := mul_right_cancel₀ hB0 (by rw [hbd, hgdet])
  obtain ⟨l, hl⟩ := exists_sq_of_fixed hp hp2 hK hq hd0 (by rw [← hbar]; exact hdfix)
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hd0
    rw [← hl]
    simp
  have hbl0 : bar l ≠ 0 := (map_ne_zero bar).2 hl0
  have hbl2 : bar l * bar l = A.det := by rw [← map_mul, hl, hdfix]
  have hbμ : bar (bar l)⁻¹ = l⁻¹ := by rw [map_inv₀, hbb]
  have hTu : IsUnitaryU (p ^ f) (psi i (l • (1 : Matrix (Fin 2) (Fin 2) K)) ((bar l)⁻¹ • 1)) := by
    rw [isUnitaryU_iff_bar bar hbar, psi_unitary_iff hi h2 bar hbi, smul_one_star, smul_one_star]
    constructor
    · simp [smul_smul, inv_mul_cancel₀ hbl0]
    · rw [hbμ]
      simp [smul_smul, mul_inv_cancel₀ hl0]
  have hTdet : (psi i (l • (1 : Matrix (Fin 2) (Fin 2) K)) ((bar l)⁻¹ • 1)).det = 1 := by
    rw [psi_det hi h2, Matrix.det_smul, Matrix.det_smul, Matrix.det_one]
    simp only [Fintype.card_fin, mul_one]
    have : l ^ 2 = bar l ^ 2 := by rw [sq, sq, hl, hbl2]
    rw [this]
    field_simp
  have hT : suOf (p ^ f) _ hTu hTdet ∈ Γ := by
    apply hxz
    · rw [gMat_suOf]
      exact (psi_xi hi h2 _ _).symm
    · rw [gMat_suOf, hzAB, psi_mul hi h2, psi_mul hi h2]
      congr 1 <;> simp
  have hA''det : (l⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul, ← hl]
    simp only [Fintype.card_fin]
    field_simp
  let A'' : SL(2, K) := ⟨l⁻¹ • A, hA''det⟩
  have hmat : gMat g = gMat (suOf (p ^ f) _ hTu hTdet) * gMat (φ A'') := by
    rw [gMat_suOf, hφ, hgAB, psi_mul hi h2]
    have hcoe : (A'' : Matrix (Fin 2) (Fin 2) K) = l⁻¹ • A := rfl
    rw [hcoe, astar_smul, map_inv₀, astar_eq_smul bar A B v1]
    congr 1
    · symm
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · symm
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_smul, hdfix, ← hbl2]
      have : (bar l)⁻¹ * (bar l)⁻¹ * (bar l * bar l) = 1 := by field_simp
      rw [this, one_smul]
  have hg_eq : g = suOf (p ^ f) _ hTu hTdet * φ A'' := Subtype.ext (Units.ext hmat)
  rw [hg_eq]
  exact mul_mem hT (hall A'')

end GenLocU4Q2s

end CFSG.GH74.Generic.BProg.B2
