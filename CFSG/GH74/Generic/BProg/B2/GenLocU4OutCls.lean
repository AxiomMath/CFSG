module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutE16
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMu
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank Matrix Subgroup
  CFSG.GH74.Generic.S1.Uni CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace GenLocU4OutCls

open GenLocU4Basic GenLocU4Out

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem graph_sq_scalar (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {φ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    (hφ : φ * φ = 1) {B : GL (Fin 4) K} (hB : IsGraphU4 B φ) :
    ∃ c : K, (B : Matrix (Fin 4) (Fin 4) K) * (B : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = c • 1 := by
  obtain ⟨hBU, hBg⟩ := hB
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  set Bm : Matrix (Fin 4) (Fin 4) K := (B : Matrix (Fin 4) (Fin 4) K) with hBm
  have hBc : cT h Bm * Bm = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h Bm).1 hBU
  have hBinv : ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = cT h Bm := by
    rw [inv_coe_of_isUnitaryU hBU, cT, hbar]
  have h1 : Bm * cT h Bm = 1 := mul_eq_one_comm.mp hBc
  have h2 : Bm.map h.bar * Bmᵀ = 1 := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) h1
    simp only [Matrix.map_mul, cT, Matrix.transpose_map, map_bar_bar h] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  set S : Matrix (Fin 4) (Fin 4) K := Bm * Bm.map h.bar with hS
  set T : Matrix (Fin 4) (Fin 4) K := Bmᵀ * cT h Bm with hT
  have hST : S * T = 1 := by
    calc S * T = Bm * (Bm.map h.bar * Bmᵀ) * cT h Bm := by rw [hS, hT]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one]; exact h1
  have hTS : T * S = 1 := mul_eq_one_comm.mp hST
  have hcomm : ∀ m : GL (Fin 4) K, m ∈ StatedSU 4 (p ^ f) K →
      S * (m : Matrix (Fin 4) (Fin 4) K) = (m : Matrix (Fin 4) (Fin 4) K) * S := by
    intro m hm
    set g : ↥(StatedSU 4 (p ^ f) K) := ⟨m, hm⟩ with hg
    have e1 : ((φ g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K).val =
        Bm * (m : Matrix (Fin 4) (Fin 4) K).map h.bar * cT h Bm := by
      rw [hBg g, hBinv, hbar]
    have e2 := congrArg (fun u : MulAut ↥(StatedSU 4 (p ^ f) K) => ((u g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K).val) hφ
    simp only [MulAut.mul_apply, MulAut.one_apply] at e2
    rw [hBg (φ g), hBinv] at e2
    rw [← hbar] at e2
    rw [e1] at e2
    simp only [Matrix.map_mul, map_bar_bar h, GenLocU4OutE16.map_cT h] at e2
    have e3 : S * (m : Matrix (Fin 4) (Fin 4) K) * T = m := by
      calc S * (m : Matrix (Fin 4) (Fin 4) K) * T
          = Bm * (Bm.map h.bar * (m : Matrix (Fin 4) (Fin 4) K) * Bmᵀ) * cT h Bm := by
            simp only [hS, hT, Matrix.mul_assoc]
        _ = m := e2
    calc S * (m : Matrix (Fin 4) (Fin 4) K) = ((S * (m : Matrix (Fin 4) (Fin 4) K) * T) * S) := by
          rw [Matrix.mul_assoc _ T S, hTS, Matrix.mul_one]
      _ = m * S := by rw [e3]
  obtain ⟨c, hc⟩ := commutant_scalar h hp2 hcomm
  exact ⟨c, by rw [← hbar]; exact hc⟩

theorem graph_transpose_pm (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {φ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    (hφ : φ * φ = 1) {B : GL (Fin 4) K} (hB : IsGraphU4 B φ) :
    (B : Matrix (Fin 4) (Fin 4) K)ᵀ = B ∨ (B : Matrix (Fin 4) (Fin 4) K)ᵀ = -(B : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨c, hc⟩ := graph_sq_scalar h hp2 hφ hB
  exact transpose_eq_of_graph h hB.1 hc

omit [Finite K] in
theorem isUnitaryU_mul (h : UnitaryFieldData p f K) {M N : Matrix (Fin 4) (Fin 4) K}
    (hM : IsUnitaryU (p ^ f) M) (hN : IsUnitaryU (p ^ f) N) : IsUnitaryU (p ^ f) (M * N) := by
  rw [GenLocU4OutFrame.isUnitaryU_iff_cT h] at hM hN ⊢
  rw [cT_mul]
  calc cT h N * cT h M * (M * N) = cT h N * (cT h M * M) * N := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hM, Matrix.mul_one]; exact hN

omit [Finite K] in
theorem isUnitaryU_map (h : UnitaryFieldData p f K) {M : Matrix (Fin 4) (Fin 4) K}
    (hM : IsUnitaryU (p ^ f) M) : IsUnitaryU (p ^ f) (M.map h.bar) := by
  rw [GenLocU4OutFrame.isUnitaryU_iff_cT h] at hM ⊢
  have := GenLocU4OutE16.Pt_Pbar h hM
  rw [cT, map_bar_bar h]
  exact this

section Aut

@[expose] def unitaryGL {q : ℕ} (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) : GL (Fin 4) K :=
  ⟨M, cstar q M, mul_eq_one_comm.mp hM, hM⟩

omit [Finite K] in
theorem isGraphAut_of_isGraphU4 {q : ℕ} {φ : MulAut ↥(StatedSU 4 q K)} {B : GL (Fin 4) K} (hB : IsGraphU4 B φ) :
    IsGraphAut q (B : Matrix (Fin 4) (Fin 4) K) φ :=
  ⟨hB.1, fun g => by rw [hB.2 g, inv_coe_of_isUnitaryU hB.1]; rfl⟩

theorem isGraphU4_of_isGraphAut {q : ℕ} {φ : MulAut ↥(StatedSU 4 q K)} {M : Matrix (Fin 4) (Fin 4) K}
    (hM : IsGraphAut q M φ) : IsGraphU4 (unitaryGL M hM.1) φ :=
  ⟨hM.1, fun g => by rw [hM.2 g]; rfl⟩

omit [Finite K] in
theorem isInnerAut_of_isInnerDiagU4 {q : ℕ} {φ : MulAut ↥(StatedSU 4 q K)} (hφ : IsInnerDiagU4 φ) :
    ∃ y : Matrix (Fin 4) (Fin 4) K, IsInnerAut q y φ := by
  obtain ⟨x, hx, hxg⟩ := hφ
  exact ⟨x, hx, fun g => by rw [hxg g, inv_coe_of_isUnitaryU hx]; rfl⟩

theorem isInnerDiagU4_of_isInnerAut {q : ℕ} {φ : MulAut ↥(StatedSU 4 q K)} {y : Matrix (Fin 4) (Fin 4) K}
    (hy : IsInnerAut q y φ) : IsInnerDiagU4 φ :=
  ⟨unitaryGL y hy.1, hy.1, fun g => by rw [hy.2 g]; rfl⟩

omit [Finite K] in
theorem graphAut_mul_innerAut (h : UnitaryFieldData p f K) {φ ψ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    {B y : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B φ) (hy : IsInnerAut (p ^ f) y ψ) :
    IsGraphAut (p ^ f) (B * y.map (· ^ (p ^ f))) (φ * ψ) := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  refine ⟨?_, fun g => ?_⟩
  · rw [← hbar]
    exact isUnitaryU_mul h hB.1 (isUnitaryU_map h hy.1)
  · rw [MulAut.mul_apply, hB.2, hy.2 g]
    simp only [cstar]
    rw [← hbar]
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, map_bar_bar h, Matrix.mul_assoc]

omit [Finite K] in
theorem lift_rel' (h : UnitaryFieldData p f K) {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hmin : ∀ (a' : A) (M : Matrix (Fin 4) (Fin 4) K), IsGraphAut (p ^ f) M (α a') → IsMinusU (p ^ f) M)
    {a b : A} {B y : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B (α a)) (hy : IsInnerAut (p ^ f) y (α b)) :
    cstar (p ^ f) y * B = B * y.map (· ^ (p ^ f)) ∧ IsMinusU (p ^ f) (B * y.map (· ^ (p ^ f))) := by
  have hM : IsMinusU (p ^ f) (B * y.map (· ^ (p ^ f))) :=
    hmin (a * b) _ (by rw [map_mul]; exact graphAut_mul_innerAut h hB hy)
  have hBs := (hmin a B hB).1
  refine ⟨?_, hM⟩
  have := hM.1
  rw [Matrix.transpose_mul, hBs] at this
  exact this

end Aut

section Types

open GenLocU4ExtMu

omit [Finite K] in
theorem det_pow_norm_one (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U) :
    U.det ^ (p ^ f) * U.det = 1 := by
  have hUc := (GenLocU4OutFrame.isUnitaryU_iff_cT h _).1 hU
  have hdetcT : (cT h U).det = h.bar U.det := by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : K →+* K) U).symm
  have := congrArg Matrix.det hUc
  rw [Matrix.det_mul, hdetcT, Matrix.det_one, UnitaryFieldData.bar_apply] at this
  exact this

omit [Finite K] in
theorem det_ne_zero_of_unitary (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) : U.det ≠ 0 := by
  intro h0
  have := det_pow_norm_one h hU
  rw [h0, mul_zero] at this
  exact zero_ne_one this

omit [Finite K] in
theorem det_norm_one (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U) :
    U.det ^ (p ^ f + 1) = 1 := by
  rw [pow_succ]
  exact det_pow_norm_one h hU

theorem isSqM_det_of_minus (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (h : UnitaryFieldData p f K) {B y : Matrix (Fin 4) (Fin 4) K}
    (hB : IsUnitaryU (p ^ f) B) (hy : IsUnitaryU (p ^ f) y)
    (hBm : IsMinusU (p ^ f) B) (hBy : IsMinusU (p ^ f) (B * y.map (· ^ (p ^ f)))) :
    IsSqM (p ^ f) y.det := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  by_contra hns
  have hdB := det_norm_one h hB
  have hdy := det_pow_norm_one h hy
  have hdetBy : (B * y.map (· ^ (p ^ f))).det = B.det * h.bar y.det := by
    rw [Matrix.det_mul, ← hbar]
    congr 1
    exact (RingHom.map_det (h.bar : K →+* K) y).symm
  have hnB : ¬ IsSqM (p ^ f) B.det := fun ⟨μ, hμ, hμ2⟩ => hBm.2 μ hμ hμ2
  have hnBy : ¬ IsSqM (p ^ f) (B * y.map (· ^ (p ^ f))).det := fun ⟨μ, hμ, hμ2⟩ => hBy.2 μ hμ hμ2
  have hne : ¬ IsSqM (p ^ f) (h.bar y.det) := by
    rintro ⟨μ, hμ, hμ2⟩
    apply hns
    refine ⟨h.bar μ, ?_, ?_⟩
    · rw [UnitaryFieldData.bar_apply, ← pow_mul, mul_comm, pow_mul, hμ, one_pow]
    · rw [← map_mul, hμ2, h.bar_bar]
  have he : (h.bar y.det) ^ (p ^ f + 1) = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_mul, mul_comm, pow_mul, det_norm_one h hy, one_pow]
  have := isSqM_mul hp hp2 hK hdB he hnB hne
  rw [← hdetBy] at this
  exact hnBy this

omit [Finite K] in
theorem isInnerAut_smul {y : Matrix (Fin 4) (Fin 4) K} {φ : MulAut ↥(StatedSU 4 (p ^ f) K)} {ω : K}
    (hω : ω ^ (p ^ f) * ω = 1) (hy : IsInnerAut (p ^ f) y φ) : IsInnerAut (p ^ f) (ω • y) φ := by
  have hc : cstar (p ^ f) (ω • y) = ω ^ (p ^ f) • cstar (p ^ f) y := by
    unfold cstar
    rw [map_smul_pow, Matrix.transpose_smul]
  refine ⟨?_, fun g => ?_⟩
  · unfold IsUnitaryU
    rw [map_smul_pow, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hω]
    have := hy.1
    unfold IsUnitaryU at this
    rw [this, one_smul]
  · rw [hy.2 g, hc]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hω, one_smul]

omit [Finite K] in
theorem rel_smul {y B : Matrix (Fin 4) (Fin 4) K} {q : ℕ} (ω : K)
    (hR : cstar q y * B = B * y.map (· ^ q)) : cstar q (ω • y) * B = B * (ω • y).map (· ^ q) := by
  unfold cstar at *
  rw [map_smul_pow, Matrix.transpose_smul, Matrix.smul_mul, hR, Matrix.mul_smul]

omit [Finite K] in
theorem isSqM_det_smul {y : Matrix (Fin 4) (Fin 4) K} {ω : K} (hω : ω ^ (p ^ f + 1) = 1)
    (hy : IsSqM (p ^ f) y.det) : IsSqM (p ^ f) (ω • y).det := by
  obtain ⟨μ, hμ, hμ2⟩ := hy
  refine ⟨ω * ω * μ, ?_, ?_⟩
  · rw [mul_pow, mul_pow, hω, hμ]
    norm_num
  · rw [Matrix.det_smul, Fintype.card_fin, ← hμ2]
    ring

omit [Finite K] in
theorem eq_one_of_scalar (hq0 : p ^ f ≠ 0) {y : Matrix (Fin 4) (Fin 4) K} {φ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    (hy : IsInnerAut (p ^ f) y φ) {c : K} (hc : y = c • 1) : φ = 1 := by
  have hu := hy.1
  rw [hc] at hu
  have hcc : c ^ (p ^ f) * c = 1 := by
    have := congrFun (congrFun hu 0) 0
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four] using this
  refine MulEquiv.ext fun g => Subtype.ext (Units.ext ?_)
  rw [hy.2 g, hc]
  unfold cstar
  rw [map_smul_pow]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.one_mul, smul_smul]
  rw [Matrix.map_one (fun x : K => x ^ (p ^ f)) (zero_pow hq0) (one_pow _), Matrix.transpose_one, Matrix.mul_one,
    hcc, one_smul]
  rfl

omit [Finite K] in
theorem innerAut_sq_scalar (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {φ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    (hφ : φ * φ = 1) {y : Matrix (Fin 4) (Fin 4) K} (hy : IsInnerAut (p ^ f) y φ) :
    ∃ c : K, y * y = c • 1 := by
  have hyy : cstar (p ^ f) y * y = 1 := hy.1
  set S : Matrix (Fin 4) (Fin 4) K := y * y with hS
  set T : Matrix (Fin 4) (Fin 4) K := cstar (p ^ f) y * cstar (p ^ f) y with hT
  have hTS : T * S = 1 := by
    calc T * S = cstar (p ^ f) y * (cstar (p ^ f) y * y) * y := by simp only [hT, hS, Matrix.mul_assoc]
      _ = 1 := by rw [hyy, Matrix.mul_one]; exact hyy
  obtain ⟨c, hc⟩ := commutant_scalar h hp2 (S := S) (fun m hm => by
    set g : ↥(StatedSU 4 (p ^ f) K) := ⟨m, hm⟩ with hg
    have e := congrArg (fun u : MulAut ↥(StatedSU 4 (p ^ f) K) => ((u g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K).val) hφ
    simp only [MulAut.mul_apply, MulAut.one_apply] at e
    rw [hy.2 (φ g), hy.2 g] at e
    have e3 : S * (m : Matrix (Fin 4) (Fin 4) K) * T = m := by
      calc S * (m : Matrix (Fin 4) (Fin 4) K) * T
          = y * (y * (m : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) y) * cstar (p ^ f) y := by
            simp only [hS, hT, Matrix.mul_assoc]
        _ = m := e
    calc S * (m : Matrix (Fin 4) (Fin 4) K) = (S * (m : Matrix (Fin 4) (Fin 4) K) * T) * S := by
          rw [Matrix.mul_assoc _ T S, hTS, Matrix.mul_one]
      _ = m * S := by rw [e3])
  exact ⟨c, hc⟩

omit [Finite K] in
theorem scalar_norm_one {c : K} (hu : IsUnitaryU (p ^ f) (c • (1 : Matrix (Fin 4) (Fin 4) K))) :
    c ^ (p ^ f) * c = 1 := by
  have := congrFun (congrFun hu 0) 0
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four] using this

omit [Finite K] in
theorem normalize_lift [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (h : UnitaryFieldData p f K) {φ : MulAut ↥(StatedSU 4 (p ^ f) K)} (hφ : φ * φ = 1)
    {y : Matrix (Fin 4) (Fin 4) K} (hy : IsInnerAut (p ^ f) y φ) :
    ∃ ω : K, ω ^ (p ^ f + 1) = 1 ∧ ((ω • y) * (ω • y) = 1 ∨ (ω • y) * (ω • y) = -1) := by
  obtain ⟨c, hc⟩ := innerAut_sq_scalar h hp2 hφ hy
  have hyy := isUnitaryU_mul h hy.1 hy.1
  rw [hc] at hyy
  have hcn := scalar_norm_one hyy
  have hc1 : c ^ (p ^ f + 1) = 1 := by rw [pow_succ]; exact hcn
  by_cases hs : IsSqM (p ^ f) c
  · obtain ⟨ω, hω, hω2⟩ := hs
    refine ⟨ω ^ (p ^ f), ?_, Or.inl ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, smul_smul]
      have : ω ^ (p ^ f) * ω ^ (p ^ f) * c = 1 := by
        rw [← hω2]
        calc ω ^ (p ^ f) * ω ^ (p ^ f) * (ω * ω) = (ω ^ (p ^ f + 1)) ^ 2 := by ring
          _ = 1 := by rw [hω]; norm_num
      rw [this, one_smul]
  · obtain ⟨ω, hω, hωc⟩ := exists_omega hp hp2 hK hq hc1 hs
    refine ⟨ω, hω, Or.inr ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, smul_smul, hωc, neg_smul, one_smul]

theorem split_trace_zero (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {y : Matrix (Fin 4) (Fin 4) K} (hy : IsUnitaryU (p ^ f) y) (hy2 : y * y = 1)
    (hdet : IsSqM (p ^ f) y.det) (hns : ∀ c : K, y ≠ c • 1) : y.trace = 0 := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨P, ε, hP, hε, hyP⟩ := GenLocU4ExtFrame.exists_frame_diag hp hp2 hK (unitaryGL y hy) hy
    (Units.ext (by rw [Units.val_mul]; exact hy2))
  have hyP' : y * (P : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ε := hyP
  set Pm : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K) with hPm
  have hPc : cstar (p ^ f) Pm * Pm = 1 := hP
  have hPc' : Pm * cstar (p ^ f) Pm = 1 := mul_eq_one_comm.mp hPc
  have hyD : y = Pm * Matrix.diagonal ε * cstar (p ^ f) Pm := by
    calc y = y * (Pm * cstar (p ^ f) Pm) := by rw [hPc', Matrix.mul_one]
      _ = (y * Pm) * cstar (p ^ f) Pm := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hyP']
  have htr : y.trace = ε 0 + ε 1 + ε 2 + ε 3 := by
    rw [hyD, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPc, Matrix.one_mul,
      Matrix.trace_diagonal, Fin.sum_univ_four]
  have hdetD : y.det = ε 0 * ε 1 * ε 2 * ε 3 := by
    have hd1 : Pm.det * (cstar (p ^ f) Pm).det = 1 := by
      rw [← Matrix.det_mul, hPc', Matrix.det_one]
    calc y.det = Pm.det * (Matrix.diagonal ε).det * (cstar (p ^ f) Pm).det := by
          conv_lhs => rw [hyD]
          rw [Matrix.det_mul, Matrix.det_mul]
      _ = (Pm.det * (cstar (p ^ f) Pm).det) * (Matrix.diagonal ε).det := by ring
      _ = _ := by rw [hd1, one_mul, Matrix.det_diagonal, Fin.prod_univ_four]
  have hnsq : ¬ IsSqM (p ^ f) (-1 : K) := not_isSqM_neg_one hq h2
  have hdiag : ∀ c : K, (∀ i, ε i = c) → y = c • 1 := fun c hc => by
    have : Matrix.diagonal ε = c • (1 : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hc]
      · simp [hij]
    rw [hyD, this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPc', ]
  rw [htr]
  rw [hdetD] at hdet
  have hprod : ε 0 * ε 1 * ε 2 * ε 3 = 1 := by
    rcases GenLocU4OutE16.prod_sigma hε with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hdet
      exact hnsq hdet
  have hneq1 : ¬ ∀ i, ε i = 1 := fun hh => hns 1 (hdiag 1 hh)
  have hneqm1 : ¬ ∀ i, ε i = -1 := fun hh => hns (-1) (hdiag (-1) hh)
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2' | h2' <;>
    rcases hε 3 with h3 | h3 <;> simp only [h0, h1, h2', h3] at hprod ⊢ <;>
    first
    | (exfalso; apply h2; linear_combination -hprod)
    | (exfalso; apply hneq1; intro i; fin_cases i <;> simp [h0, h1, h2', h3]; done)
    | (exfalso; apply hneqm1; intro i; fin_cases i <;> simp [h0, h1, h2', h3]; done)
    | norm_num

end Types

end GenLocU4OutCls

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K] [Finite K]

theorem outer_survivors {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hA : IsRank23 A) (_hout : ∃ a : A, ¬ IsInnerDiagU4 (α a)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4)
    (a : A) (B : GL (Fin 4) K) (hB : IsGraphU4 B (α a)) : IsMinusU (p ^ f) (B : Matrix (Fin 4) (Fin 4) K) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have haa : α a * α a = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a, map_one]
  have hsym : (B : Matrix (Fin 4) (Fin 4) K)ᵀ = B := by
    rcases GenLocU4OutCls.graph_transpose_pm h hp2 haa hB with h1 | h1
    · exact h1
    · exact absurd hsect (not_sectional_su4_sp_or_plus hp hp2 hK hq α a B hB haa (Or.inl h1))
  refine ⟨hsym, fun μ hμ hμ2 => ?_⟩
  exact not_sectional_su4_sp_or_plus hp hp2 hK hq α a B hB haa (Or.inr ⟨hsym, μ, hμ, hμ2⟩) hsect

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
