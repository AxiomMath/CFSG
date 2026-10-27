module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineSL2

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.LieType.Steinberg
open scoped MatrixGroups

namespace GenLocU3Good

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

abbrev ym (y : Su F p f 2) : Matrix (Fin 2) (Fin 2) F := ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)

theorem su2_mem (h : UnitaryFieldData p f F) (y : Su F p f 2) :
    (ym y).det = 1 ∧ ((ym y).map h.bar)ᵀ * ym y = 1 :=
  (mem_unitarySU_iff h).1 (suEquiv h 2 y).2

theorem exists_su2 (h : UnitaryFieldData p f F) (g : GL (Fin 2) F)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hu : ((g : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) F) = 1) :
    ∃ y : Su F p f 2, ym y = (g : Matrix (Fin 2) (Fin 2) F) := by
  refine ⟨(suEquiv h 2).symm ⟨g, (mem_unitarySU_iff h).2 ⟨hdet, hu⟩⟩, ?_⟩
  have := coe_suEquiv h 2 ((suEquiv h 2).symm ⟨g, (mem_unitarySU_iff h).2 ⟨hdet, hu⟩⟩)
  rw [MulEquiv.apply_symm_apply] at this
  simp only [ym]
  rw [← this]

theorem su2_bar (h : UnitaryFieldData p f F) (y : Su F p f 2) :
    (ym y).map h.bar = !![0, 1; -1, 0] * ym y * !![0, -1; 1, 0] := by
  obtain ⟨hdet, hu⟩ := su2_mem h y
  have h1 : ((ym y).map h.bar)ᵀ = Matrix.adjugate (ym y) := by
    calc ((ym y).map h.bar)ᵀ = ((ym y).map h.bar)ᵀ * (ym y * Matrix.adjugate (ym y)) := by
          rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]
      _ = (((ym y).map h.bar)ᵀ * ym y) * Matrix.adjugate (ym y) := by rw [Matrix.mul_assoc]
      _ = Matrix.adjugate (ym y) := by rw [hu, Matrix.one_mul]
  have h2 : (ym y).map h.bar = (Matrix.adjugate (ym y))ᵀ := by
    rw [← h1, Matrix.transpose_transpose]
  rw [h2, Matrix.adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]


theorem ym_mul (s t : Su F p f 2) : ym (s * t) = ym s * ym t := by
  simp [ym]

theorem ym_one : ym (1 : Su F p f 2) = 1 := by
  simp [ym]

theorem ym_inv_mul (s : Su F p f 2) : ym s⁻¹ * ym s = 1 := by
  rw [← ym_mul, inv_mul_cancel, ym_one]

theorem ym_mul_inv (s : Su F p f 2) : ym s * ym s⁻¹ = 1 := by
  rw [← ym_mul, mul_inv_cancel, ym_one]

omit [Fact p.Prime] [CharP F p] in
theorem exists_unit_sq_ne_one (hK : Nat.card F = (p ^ f) ^ 2) (h3 : 3 ≤ p ^ f) :
    ∃ ε : F, ε ^ (p ^ f) * ε = 1 ∧ ε * ε ≠ 1 := by
  have := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hq1 : 1 ≤ p ^ f := by omega
  have hprod : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring
  have hu1 : (g ^ (p ^ f - 1)) ^ (p ^ f + 1) = 1 := by
    rw [← pow_mul, hprod, ← hord, pow_orderOf_eq_one]
  have hu2 : (g ^ (p ^ f - 1)) ^ 2 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by omega) hd
    have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := hprod.symm
    rw [this] at hle
    have h4 : 0 < p ^ f - 1 := by omega
    nlinarith
  refine ⟨((g ^ (p ^ f - 1) : Fˣ) : F), ?_, ?_⟩
  · have := congrArg (fun w : Fˣ => (w : F)) hu1
    simpa [Units.val_pow_eq_pow_val, pow_succ] using this
  · intro h
    apply hu2
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val, pow_two] using h

def dgl (ε : F) (hε : ε ≠ 0) : GL (Fin 2) F :=
  ⟨!![ε, 0; 0, ε⁻¹], !![ε⁻¹, 0; 0, ε], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hε],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hε]⟩

def jgl : GL (Fin 2) F :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem exists_su2_diag (h : UnitaryFieldData p f F) {ε : F} (hε : h.bar ε * ε = 1) :
    ∃ y : Su F p f 2, ym y = !![ε, 0; 0, ε⁻¹] := by
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  obtain ⟨y, hy⟩ := exists_su2 h (dgl ε hε0) (by simp [dgl, Matrix.det_fin_two, hε0]) (by
    have hb : (h.bar ε)⁻¹ * ε⁻¹ = 1 := by
      rw [← mul_inv, hε, inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dgl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hε, hb])
  exact ⟨y, hy⟩

theorem exists_su2_J (h : UnitaryFieldData p f F) :
    ∃ y : Su F p f 2, ym y = !![0, 1; -1, 0] := by
  obtain ⟨y, hy⟩ := exists_su2 h (jgl (F := F)) (by simp [jgl, Matrix.det_fin_two]) (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jgl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply])
  exact ⟨y, hy⟩

theorem eq_smul_one_of_comm_su2 (h : UnitaryFieldData p f F) (h3 : 3 ≤ p ^ f)
    (N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ y : Su F p f 2, N * ym y = ym y * N) :
    ∃ n : F, N = n • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨ε, hε1, hε2⟩ := exists_unit_sq_ne_one h.card_eq_sq h3
  have hε : h.bar ε * ε = 1 := by rw [h.bar_apply]; exact hε1
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  obtain ⟨yd, hyd⟩ := exists_su2_diag h hε
  obtain ⟨yj, hyj⟩ := exists_su2_J h
  have c1 := hN yd
  have c2 := hN yj
  rw [hyd] at c1
  rw [hyj] at c2
  have hne : ε⁻¹ - ε ≠ 0 := by
    intro h0
    apply hε2
    have : ε⁻¹ = ε := by linear_combination h0
    field_simp at this
    linear_combination -this
  have e01 := congrFun (congrFun c1 0) 1
  have e10 := congrFun (congrFun c1 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have n01 : N 0 1 = 0 := by
    have : N 0 1 * (ε⁻¹ - ε) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right hne
  have n10 : N 1 0 = 0 := by
    have : N 1 0 * (ε⁻¹ - ε) = 0 := by linear_combination -e10
    exact (mul_eq_zero.1 this).resolve_right hne
  have e00 := congrFun (congrFun c2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00
  refine ⟨N 0 0, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [n01, n10]
  linear_combination -e00


theorem exists_block_conj_explicit (h : UnitaryFieldData p f F) {Δ : GL (Fin 3) F}
    (hΔ : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hΔu : (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1)
    (ψ : F ≃+* F) (i : Fin 2) (y : Su F p f 2) :
    ∃ y' : Su F p f 2, (∀ u v : Fin 2, ym y' u v =
        ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i u) (idx3 i u) * ψ (ym y u v) *
          (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i v) (idx3 i v))⁻¹) ∧
      Δ * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * Δ⁻¹ =
        ((blockEmb2 F p f 2 i y' : Su F p f 3) : GL (Fin 3) F) := by
  classical
  obtain ⟨d, hDd⟩ : ∃ d : Fin 3 → F, Matrix.diagonal d = (Δ : Matrix (Fin 3) (Fin 3) F) :=
    ⟨_, hΔ.diagonal_diag⟩
  have hdn : ∀ k, h.bar (d k) * d k = 1 := by
    intro k
    have h1 := hΔu
    rw [← hDd, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at h1
    have := congrFun (congrFun h1 k) k
    simpa using this
  have hd0 : ∀ k, d k ≠ 0 := by
    intro k h0
    have := hdn k
    rw [h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  set d2 : Fin 2 → F := fun x => d (idx3 i x) with hd2
  let D2 : GL (Fin 2) F := ⟨Matrix.diagonal d2, Matrix.diagonal (fun x => (d2 x)⁻¹),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact mul_inv_cancel₀ (hd0 _),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact inv_mul_cancel₀ (hd0 _)⟩
  have hY : (y : GL (Fin 2) F) ∈ unitarySU p f F 2 := (suEquiv h 2 y).2
  have hY1 : glAut ψ (y : GL (Fin 2) F) ∈ unitarySU p f F 2 := by
    rw [unitarySU_eq_gramSU h 2] at hY ⊢
    exact glAut_mem_gramSU h (isPrimeFormGram_one (n := 2)) ψ (by simpa using hY)
  have hD2u : D2 ∈ primeFormUnitary h (idGram F 2) := by
    rw [mem_primeFormUnitary]
    change ((Matrix.diagonal d2).map h.bar)ᵀ * idGram F 2 * Matrix.diagonal d2 = idGram F 2
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1; ext x
    exact hdn _
  have hY2 := KFU.conj_mem_unitarySU h hD2u hY1
  refine ⟨(suEquiv h 2).symm ⟨D2 * glAut ψ (y : GL (Fin 2) F) * D2⁻¹, hY2⟩, ?_, ?_⟩
  · intro u v
    have hy' : ym ((suEquiv h 2).symm ⟨D2 * glAut ψ (y : GL (Fin 2) F) * D2⁻¹, hY2⟩) =
        Matrix.diagonal d2 * (ym y).map ψ * Matrix.diagonal (fun x => (d2 x)⁻¹) := by
      have := coe_suEquiv h 2 ((suEquiv h 2).symm ⟨D2 * glAut ψ (y : GL (Fin 2) F) * D2⁻¹, hY2⟩)
      rw [MulEquiv.apply_symm_apply] at this
      simp only [ym]
      rw [← this, Units.val_mul, Units.val_mul, coe_glAut]
      rfl
    rw [hy', Matrix.mul_diagonal, Matrix.diagonal_mul, ← hDd]
    simp [hd2, Matrix.map_apply]
  · rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut]
    rw [← hDd]
    change Matrix.diagonal d * ((blockMat 3 i.val (((y : Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).map ψ) =
      blockMat 3 i.val ((D2 * glAut ψ (y : GL (Fin 2) F) * D2⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal d
    rw [map_blockMat, diag_mul_blockMat d hd0 i]
    congr 2


theorem sq_of_conj_eq (h : UnitaryFieldData p f F) (h3 : 3 ≤ p ^ f) (M M' : Matrix (Fin 2) (Fin 2) F)
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hMu : (M.map h.bar)ᵀ * M = 1) (s : Su F p f 2)
    (hs : ∀ y : Su F p f 2, M * ym y * M' = ym s * ym y * ym s⁻¹) :
    ∃ n : F, h.bar n * n = 1 ∧ n * n = M.det := by
  set N : Matrix (Fin 2) (Fin 2) F := ym s⁻¹ * M with hN
  set N' : Matrix (Fin 2) (Fin 2) F := M' * ym s with hN'
  have hNN' : N * N' = 1 := by
    calc N * N' = ym s⁻¹ * (M * M') * ym s := by simp only [hN, hN', Matrix.mul_assoc]
      _ = 1 := by rw [hMM', Matrix.mul_one, ym_inv_mul]
  have hN'N : N' * N = 1 := by
    calc N' * N = M' * (ym s * ym s⁻¹) * M := by simp only [hN, hN', Matrix.mul_assoc]
      _ = 1 := by rw [ym_mul_inv, Matrix.mul_one, hM'M]
  have hcomm : ∀ y : Su F p f 2, N * ym y = ym y * N := by
    intro y
    have h1 : N * ym y * N' = ym y := by
      calc N * ym y * N' = ym s⁻¹ * (M * ym y * M') * ym s := by
            simp only [hN, hN', Matrix.mul_assoc]
        _ = ym s⁻¹ * (ym s * ym y * ym s⁻¹) * ym s := by rw [hs y]
        _ = (ym s⁻¹ * ym s) * ym y * (ym s⁻¹ * ym s) := by simp only [Matrix.mul_assoc]
        _ = ym y := by rw [ym_inv_mul, Matrix.one_mul, Matrix.mul_one]
    calc N * ym y = N * ym y * (N' * N) := by rw [hN'N, Matrix.mul_one]
      _ = (N * ym y * N') * N := by simp only [Matrix.mul_assoc]
      _ = ym y * N := by rw [h1]
  obtain ⟨n, hn⟩ := eq_smul_one_of_comm_su2 h h3 N hcomm
  have hM : M = n • ym s := by
    calc M = (ym s * ym s⁻¹) * M := by rw [ym_mul_inv, Matrix.one_mul]
      _ = ym s * N := by simp only [hN, Matrix.mul_assoc]
      _ = n • ym s := by rw [hn, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨hdet, hu⟩ := su2_mem h s
  refine ⟨n, ?_, ?_⟩
  · have := hMu
    rw [hM, Matrix.map_smul' h.bar n (ym s) (map_mul h.bar), Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul] at this
    have h00 := congrFun (congrFun this 0) 0
    simpa using h00
  · rw [hM, Matrix.det_smul, hdet]
    simp [Fintype.card_fin, sq]

theorem not_inner_of_entries (h : UnitaryFieldData p f F) (h3 : 3 ≤ p ^ f) {φ : MulAut (Su F p f 2)}
    (e : Fin 2 → F) (he : ∀ u, h.bar (e u) * e u = 1) {ψ : F ≃+* F}
    (hψ : ψ = 1 ∨ ∀ c, ψ c = h.bar c)
    (hφ : ∀ (y : Su F p f 2) (u v : Fin 2), ym (φ y) u v = e u * ψ (ym y u v) * (e v)⁻¹)
    (hns : ¬ ∃ n : F, h.bar n * n = 1 ∧ n * n = e 0 * e 1) :
    φ ∉ (MulAut.conj : Su F p f 2 →* MulAut (Su F p f 2)).range := by
  rintro ⟨s, hs⟩
  have HE0 := he 0
  have HE1 := he 1
  have h00 : e 0 ≠ 0 := by
    intro h0
    rw [h0] at HE0
    simp at HE0
  have h11 : e 1 ≠ 0 := by
    intro h0
    rw [h0] at HE1
    simp at HE1
  have hsy : ∀ y : Su F p f 2, ym (φ y) = ym s * ym y * ym s⁻¹ := by
    intro y
    rw [← hs, MulAut.conj_apply, ym_mul, ym_mul]
  rcases hψ with rfl | hbar
  · have hMM' : !![(e 0), 0; 0, (e 1)] * !![(e 0)⁻¹, 0; 0, (e 1)⁻¹] = (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11]
    have hM'M : !![(e 0)⁻¹, 0; 0, (e 1)⁻¹] * !![(e 0), 0; 0, (e 1)] = (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11]
    have hMu : ((!![(e 0), 0; 0, (e 1)] : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * !![(e 0), 0; 0, (e 1)] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, HE0, HE1]
    have hkey : ∀ y : Su F p f 2, !![(e 0), 0; 0, (e 1)] * ym y * !![(e 0)⁻¹, 0; 0, (e 1)⁻¹] =
        ym s * ym y * ym s⁻¹ := by
      intro y
      rw [← hsy y]
      ext u v
      have := hφ y u v
      fin_cases u <;> fin_cases v <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at this ⊢ <;>
          linear_combination -this
    obtain ⟨n, hn1, hn2⟩ := sq_of_conj_eq h h3 _ _ hMM' hM'M hMu s hkey
    exact hns ⟨n, hn1, by rw [hn2, Matrix.det_fin_two_of]; ring⟩
  · have hMM' : !![0, (e 0); -(e 1), 0] * !![0, -(e 1)⁻¹; (e 0)⁻¹, 0] = (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11]
    have hM'M : !![0, -(e 1)⁻¹; (e 0)⁻¹, 0] * !![0, (e 0); -(e 1), 0] = (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11]
    have hMu : ((!![0, (e 0); -(e 1), 0] : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * !![0, (e 0); -(e 1), 0] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, HE0, HE1]
    have hkey : ∀ y : Su F p f 2, !![0, (e 0); -(e 1), 0] * ym y * !![0, -(e 1)⁻¹; (e 0)⁻¹, 0] =
        ym s * ym y * ym s⁻¹ := by
      intro y
      rw [← hsy y]
      have hb := su2_bar h y
      have b00 := congrFun (congrFun hb 0) 0
      have b01 := congrFun (congrFun hb 0) 1
      have b10 := congrFun (congrFun hb 1) 0
      have b11 := congrFun (congrFun hb 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.vecMul, dotProduct] at b00 b01 b10 b11
      ext u v
      have := hφ y u v
      fin_cases u <;> fin_cases v <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hbar] at this ⊢
      · rw [this, b00]
      · rw [this, b01]; ring
      · rw [this, b10]; ring
      · rw [this, b11]
    obtain ⟨n, hn1, hn2⟩ := sq_of_conj_eq h h3 _ _ hMM' hM'M hMu s hkey
    exact hns ⟨n, hn1, by rw [hn2, Matrix.det_fin_two_of]; ring⟩

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem mem_pfu_of_unitary (h : UnitaryFieldData p f F) {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1) :
    C ∈ primeFormUnitary h (idGram F 3) := by
  rw [mem_primeFormUnitary]; simpa [idGram] using hCu

@[expose] noncomputable def frameBlock (h : UnitaryFieldData p f F) {J : Type} [Group J]
    (θ : ↥(unitarySU p f F 3) →* J) (C : GL (Fin 3) F)
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    (i : Fin 2) : Su F p f 2 →* J :=
  (θ.comp ((KFU.conjSU h ⟨C, mem_pfu_of_unitary h hCu⟩).toMonoidHom.comp
    (suEquiv h 3).toMonoidHom)).comp (blockEmb2 F p f 2 i)

theorem frameBlock_injective (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    (i : Fin 2) : Function.Injective (frameBlock h θ C hCu i) :=
  blockHom_injective h hθ (mem_pfu_of_unitary h hCu) i

theorem frameBlock_apply (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {x : MulAut J} {A' Δ : GL (Fin 3) F} {ψ : F ≃+* F} (hl : IsLift θ A' ψ x)
    (hA'u : ((A' : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A' : Matrix (Fin 3) (Fin 3) F) = 1)
    (hΔd : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) (hAC : A' * glAut ψ C = C * Δ)
    (i : Fin 2) (y : Su F p f 2) :
    ∃ y' : Su F p f 2, (∀ u v : Fin 2, ym y' u v =
        ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i u) (idx3 i u) * ψ (ym y u v) *
          (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (idx3 i v) (idx3 i v))⁻¹) ∧
      x (frameBlock h θ C hCu i y) = frameBlock h θ C hCu i y' := by
  classical
  have hC := mem_pfu_of_unitary h hCu
  have hΔmem : Δ ∈ unitaryIsom3 h := by
    have : Δ = C⁻¹ * (A' * glAut ψ C) := by rw [hAC]; group
    rw [this]
    exact mul_mem (inv_mem ((mem_unitaryIsom3 (h := h)).2 hCu))
      (mul_mem ((mem_unitaryIsom3 (h := h)).2 hA'u)
        (glAut_mem_unitaryIsom3 ψ ((mem_unitaryIsom3 (h := h)).2 hCu)))
  obtain ⟨y', hy1, hy'⟩ := exists_block_conj_explicit h hΔd ((mem_unitaryIsom3 (h := h)).1 hΔmem) ψ i y
  refine ⟨y', hy1, ?_⟩
  obtain ⟨g', hg'1, hg'2⟩ := hl (KFU.conjSU h ⟨C, hC⟩ (suEquiv h 3 (blockEmb2 F p f 2 i y)))
  have hgg : KFU.conjSU h ⟨C, hC⟩ (suEquiv h 3 (blockEmb2 F p f 2 i y')) = g' := by
    apply Subtype.ext
    rw [hg'1]
    change C * ((blockEmb2 F p f 2 i y' : Su F p f 3) : GL (Fin 3) F) * C⁻¹ =
      A' * glAut ψ (C * ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * C⁻¹) * A'⁻¹
    calc C * ((blockEmb2 F p f 2 i y' : Su F p f 3) : GL (Fin 3) F) * C⁻¹
        = C * (Δ * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * Δ⁻¹) * C⁻¹ := by
          rw [hy']
      _ = (C * Δ) * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * (C * Δ)⁻¹ := by
          group
      _ = (A' * glAut ψ C) * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) *
          (A' * glAut ψ C)⁻¹ := by rw [hAC]
      _ = A' * glAut ψ (C * ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * C⁻¹) * A'⁻¹ := by
          simp only [map_mul, map_inv]; group
  show x (θ (KFU.conjSU h ⟨C, hC⟩ (suEquiv h 3 (blockEmb2 F p f 2 i y)))) =
    θ (KFU.conjSU h ⟨C, hC⟩ (suEquiv h 3 (blockEmb2 F p f 2 i y')))
  rw [hgg, hg'2]

theorem gammaAct_eq_top_of_blocks_frame (h : UnitaryFieldData p f F) (hq : p ^ f ≠ 2)
    {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {A : Type} [Group A] (α : A →* MulAut J) (hα : ∀ a, FrameForm h θ C (α a))
    (hblk : ∀ (i : Fin 2) (β : A →* MulAut (Su F p f 2)),
      (∀ a y, α a (frameBlock h θ C hCu i y) = frameBlock h θ C hCu i (β a y)) →
        gammaAct β = ⊤) : gammaAct α = ⊤ := by
  classical
  have hC := mem_pfu_of_unitary h hCu
  let cC : ↥(unitarySU p f F 3) ≃* ↥(unitarySU p f F 3) := KFU.conjSU h ⟨C, hC⟩
  let Ψ : Su F p f 3 →* J := θ.comp (cC.toMonoidHom.comp (suEquiv h 3).toMonoidHom)
  let φ : Fin 2 → (Su F p f 2 →* J) := fun i => frameBlock h θ C hCu i
  have hpres : ∀ (i : Fin 2) (a : A) (y : Su F p f 2), ∃ z : Su F p f 2, φ i z = α a (φ i y) := by
    intro i a y
    obtain ⟨A', Δ, ψ, hl, -, hA'u, hΔd, hAC⟩ := hα a
    obtain ⟨y', -, hy'⟩ := frameBlock_apply h hCu hl hA'u hΔd hAC i y
    exact ⟨y', hy'.symm⟩
  choose β hβ using fun i => exists_restrict_action (φ i) (frameBlock_injective h hθ hCu i) α (hpres i)
  have htop : ⨆ i, (φ i).range = ⊤ := by
    have hsurj : Function.Surjective Ψ :=
      hθ.surj.comp (cC.surjective.comp (suEquiv h 3).surjective)
    have h1 := iSup_range_blockEmb2 (K := F) (p := p) (f := f) h.card_eq_sq hq 2
    simp only [φ, frameBlock, MonoidHom.range_comp]
    rw [← Subgroup.map_iSup, h1, Subgroup.map_top_of_surjective _ hsurj]
  exact gammaAct_eq_top_of_equivariant α (fun _ => Su F p f 2) φ β
    (fun i a y => hβ i a y) htop (fun i => hblk i (β i) (hβ i))

@[expose] def pmat (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun a b => if a = σ b then 1 else 0

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pmat_mul_apply (σ : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) F) (a b : Fin 3) :
    (M * (pmat σ : Matrix (Fin 3) (Fin 3) F)) a b = M a (σ b) := by
  simp [pmat, Matrix.mul_apply]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pmatT_mul_apply (σ : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) F) (a b : Fin 3) :
    ((pmat σ : Matrix (Fin 3) (Fin 3) F)ᵀ * M) a b = M (σ a) b := by
  simp [pmat, Matrix.mul_apply, Matrix.transpose_apply]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pmatT_mul_pmat (σ : Equiv.Perm (Fin 3)) :
    (pmat σ : Matrix (Fin 3) (Fin 3) F)ᵀ * pmat σ = 1 := by
  ext a b
  rw [pmatT_mul_apply, pmat]
  simp [Matrix.one_apply]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pmat_mul_pmatT (σ : Equiv.Perm (Fin 3)) :
    (pmat σ : Matrix (Fin 3) (Fin 3) F) * (pmat σ)ᵀ = 1 := by
  exact mul_eq_one_comm.1 (pmatT_mul_pmat σ)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pmat_map (σ : Equiv.Perm (Fin 3)) (g : F → F) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    (pmat σ : Matrix (Fin 3) (Fin 3) F).map g = pmat σ := by
  ext a b
  simp only [pmat, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [h0, h1]

@[expose] def pgl (σ : Equiv.Perm (Fin 3)) : GL (Fin 3) F :=
  ⟨pmat σ, (pmat σ)ᵀ, pmat_mul_pmatT σ, pmatT_mul_pmat σ⟩

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_pgl (σ : Equiv.Perm (Fin 3)) :
    ((pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = pmat σ := rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_pgl_inv (σ : Equiv.Perm (Fin 3)) :
    (((pgl σ)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (pmat σ)ᵀ := rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem glAut_pgl (ψ : F ≃+* F) (σ : Equiv.Perm (Fin 3)) :
    glAut ψ (pgl σ : GL (Fin 3) F) = pgl σ := by
  apply Units.ext
  rw [coe_glAut, coe_pgl]
  exact pmat_map σ _ (map_zero ψ) (map_one ψ)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem pgl_unitary (h : UnitaryFieldData p f F) (σ : Equiv.Perm (Fin 3)) :
    (((pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [coe_pgl, pmat_map σ _ (map_zero h.bar) (map_one h.bar)]
  exact pmatT_mul_pmat σ

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem coe_conj_pgl (σ : Equiv.Perm (Fin 3)) (Δ : GL (Fin 3) F) (a b : Fin 3) :
    (((pgl σ)⁻¹ * Δ * pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) a b =
      (Δ : Matrix (Fin 3) (Fin 3) F) (σ a) (σ b) := by
  rw [Units.val_mul, Units.val_mul, coe_pgl_inv, coe_pgl, pmat_mul_apply, pmatT_mul_apply]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem isDiag_conj_pgl (σ : Equiv.Perm (Fin 3)) {Δ : GL (Fin 3) F}
    (hΔ : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) :
    (((pgl σ)⁻¹ * Δ * pgl σ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
  intro a b hab
  rw [coe_conj_pgl]
  exact hΔ (fun e => hab (σ.injective e))

@[expose] def DiagLift (h : UnitaryFieldData p f F) {J : Type} [Group J]
    (θ : ↥(unitarySU p f F 3) →* J) (x : MulAut J) : Prop :=
  ∃ (Δ : GL (Fin 3) F) (ψ : F ≃+* F), IsLift θ Δ ψ x ∧ (ψ = 1 ∨ ∀ c, ψ c = h.bar c) ∧
    ((Δ : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Δ : Matrix (Fin 3) (Fin 3) F) = 1 ∧
    ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem frameForm_perm (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (σ : Equiv.Perm (Fin 3)) {x : MulAut J}
    (hx : DiagLift h θ x) : FrameForm h θ (pgl σ) x := by
  obtain ⟨Δ, ψ, hl, hψ, hΔu, hΔd⟩ := hx
  exact ⟨Δ, (pgl σ)⁻¹ * Δ * pgl σ, ψ, hl, hψ, hΔu, isDiag_conj_pgl σ hΔd,
    by rw [glAut_pgl]; group⟩

theorem frameBlock_apply_perm (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (σ : Equiv.Perm (Fin 3)) {x : MulAut J} {Δ : GL (Fin 3) F}
    {ψ : F ≃+* F} (hl : IsLift θ Δ ψ x)
    (hΔu : ((Δ : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Δ : Matrix (Fin 3) (Fin 3) F) = 1)
    (hΔd : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) (i : Fin 2) (y : Su F p f 2) :
    ∃ y' : Su F p f 2, (∀ u v : Fin 2, ym y' u v =
        ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i u)) (σ (idx3 i u)) * ψ (ym y u v) *
          (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i v)) (σ (idx3 i v)))⁻¹) ∧
      x (frameBlock h θ (pgl σ) (pgl_unitary h σ) i y) =
        frameBlock h θ (pgl σ) (pgl_unitary h σ) i y' := by
  obtain ⟨y', hy1, hy2⟩ := frameBlock_apply h (pgl_unitary h σ) hl hΔu (isDiag_conj_pgl σ hΔd)
    (show Δ * glAut ψ (pgl σ) = pgl σ * ((pgl σ)⁻¹ * Δ * pgl σ) by rw [glAut_pgl]; group) i y
  refine ⟨y', fun u v => ?_, hy2⟩
  rw [hy1, coe_conj_pgl, coe_conj_pgl]

theorem block_entries_of_spec (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) (σ : Equiv.Perm (Fin 3))
    {A : Type} [Group A] (α : A →* MulAut J) (i : Fin 2) (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ (pgl σ) (pgl_unitary h σ) i y) =
      frameBlock h θ (pgl σ) (pgl_unitary h σ) i (β a y))
    {a : A} {Δ : GL (Fin 3) F} {ψ : F ≃+* F} (hl : IsLift θ Δ ψ (α a))
    (hΔu : ((Δ : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Δ : Matrix (Fin 3) (Fin 3) F) = 1)
    (hΔd : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) (y : Su F p f 2) (u v : Fin 2) :
    ym (β a y) u v =
      ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i u)) (σ (idx3 i u)) * ψ (ym y u v) *
        (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i v)) (σ (idx3 i v)))⁻¹ := by
  obtain ⟨y', hy1, hy2⟩ := frameBlock_apply_perm h σ hl hΔu hΔd i y
  have : β a y = y' :=
    frameBlock_injective h hθ (pgl_unitary h σ) i (by rw [← hβ, hy2])
  rw [this]
  exact hy1 u v

@[expose] def DU (h : UnitaryFieldData p f F) (Δ : GL (Fin 3) F) : Prop :=
  ((Δ : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Δ : Matrix (Fin 3) (Fin 3) F) = 1 ∧
    ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem DU.one (h : UnitaryFieldData p f F) : DU h (1 : GL (Fin 3) F) := by
  refine ⟨?_, ?_⟩
  · exact (mem_unitaryIsom3 (h := h)).1 (one_mem _)
  · rw [Units.val_one]; exact Matrix.isDiag_one

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem DU.mul {h : UnitaryFieldData p f F} {Δ Δ' : GL (Fin 3) F} (hΔ : DU h Δ) (hΔ' : DU h Δ') :
    DU h (Δ * Δ') := by
  refine ⟨(mem_unitaryIsom3 (h := h)).1 (mul_mem ((mem_unitaryIsom3 (h := h)).2 hΔ.1)
    ((mem_unitaryIsom3 (h := h)).2 hΔ'.1)), ?_⟩
  rw [Units.val_mul]
  exact isDiag_mul' hΔ.2 hΔ'.2

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem DU.glAut {h : UnitaryFieldData p f F} {Δ : GL (Fin 3) F} (hΔ : DU h Δ) (ψ : F ≃+* F) :
    DU h (glAut ψ Δ) := by
  refine ⟨(mem_unitaryIsom3 (h := h)).1 (glAut_mem_unitaryIsom3 ψ ((mem_unitaryIsom3 (h := h)).2 hΔ.1)), ?_⟩
  rw [coe_glAut]
  exact hΔ.2.map (map_zero ψ)

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem glAut_one_apply (Δ : GL (Fin 3) F) : glAut (1 : F ≃+* F) Δ = Δ := by
  rw [map_one]; rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem isLift_one {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J} :
    IsLift θ (1 : GL (Fin 3) F) 1 (1 : MulAut J) := fun g => by
  refine ⟨g, ?_, ?_⟩
  · rw [glAut_one_apply]; simp
  · rfl

@[expose] def A0 (h : UnitaryFieldData p f F) {J : Type} [Group J] (θ : ↥(unitarySU p f F 3) →* J)
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1) : Subgroup A where
  carrier := {a | ∃ Δ : GL (Fin 3) F, IsLift θ Δ 1 (α a) ∧ DU h Δ}
  mul_mem' := by
    rintro a b ⟨Δ, hl, hD⟩ ⟨Δ', hl', hD'⟩
    refine ⟨Δ * Δ', ?_, hD.mul hD'⟩
    have := hl.mul hl'
    rwa [glAut_one_apply, mul_one, ← map_mul] at this
  one_mem' := ⟨1, by rw [map_one]; exact isLift_one, DU.one h⟩
  inv_mem' := by
    intro a ha
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
    rw [this]; exact ha

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem mem_A0 {h : UnitaryFieldData p f F} {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    {A : Type} [Group A] {α : A →* MulAut J} {hsq : ∀ a : A, a * a = 1} {a : A} :
    a ∈ A0 h θ α hsq ↔ ∃ Δ : GL (Fin 3) F, IsLift θ Δ 1 (α a) ∧ DU h Δ := Iff.rfl

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem isLift_mul_bar (h : UnitaryFieldData p f F) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    {x y : MulAut J} {Δ Δ' : GL (Fin 3) F} {ψ ψ' : F ≃+* F} (hψ : ∀ c, ψ c = h.bar c)
    (hψ' : ∀ c, ψ' c = h.bar c) (hl : IsLift θ Δ ψ x) (hl' : IsLift θ Δ' ψ' y) :
    IsLift θ (Δ * glAut ψ Δ') 1 (x * y) := by
  have hψψ : ψ * ψ' = 1 := RingEquiv.ext fun c => by
    change ψ (ψ' c) = c
    rw [hψ', hψ, h.bar_bar]
  have := hl.mul hl'
  rwa [hψψ] at this

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem mul_mem_A0 (h : UnitaryFieldData p f F) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1)
    (hα : ∀ a, DiagLift h θ (α a)) {a b : A} (ha : a ∉ A0 h θ α hsq) (hb : b ∉ A0 h θ α hsq) :
    a * b ∈ A0 h θ α hsq := by
  obtain ⟨Δ, ψ, hl, hψ, hΔu, hΔd⟩ := hα a
  obtain ⟨Δ', ψ', hl', hψ', hΔu', hΔd'⟩ := hα b
  rcases hψ with rfl | hψ
  · exact absurd ⟨Δ, hl, hΔu, hΔd⟩ ha
  rcases hψ' with rfl | hψ'
  · exact absurd ⟨Δ', hl', hΔu', hΔd'⟩ hb
  refine ⟨Δ * glAut ψ Δ', ?_, (DU.mul ⟨hΔu, hΔd⟩ (DU.glAut ⟨hΔu', hΔd'⟩ ψ))⟩
  rw [map_mul]
  exact isLift_mul_bar h hψ hψ' hl hl'

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem A0_index_le_two (h : UnitaryFieldData p f F) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1)
    (hα : ∀ a, DiagLift h θ (α a)) : (A0 h θ α hsq).index ≤ 2 := by
  by_cases htop : A0 h θ α hsq = ⊤
  · rw [htop, Subgroup.index_top]; norm_num
  · obtain ⟨a, ha⟩ : ∃ a, a ∉ A0 h θ α hsq := by
      by_contra hc
      push Not at hc
      exact htop (eq_top_iff.2 fun a _ => hc a)
    have : (A0 h θ α hsq).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨a, fun b => ?_⟩
      by_cases hb : b ∈ A0 h θ α hsq
      · right
        refine ⟨hb, fun hba => ha ?_⟩
        have := (A0 h θ α hsq).mul_mem ((A0 h θ α hsq).inv_mem hb) hba
        simpa using this
      · left
        exact ⟨mul_mem_A0 h α hsq hα hb ha, hb⟩
    rw [this]

theorem gammaAct_su2_of_not_inner_small (h : UnitaryFieldData p f F)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {A : Type} [Group A] [Finite A] (hA : IsRank23 A)
    (β : A →* MulAut (Su F p f 2))
    (hni : ¬ β.range ≤ (MulAut.conj : Su F p f 2 →* MulAut (Su F p f 2)).range)
    (hsmall : Nat.card β.range ≤ 4) : gammaAct β = ⊤ := by
  obtain ⟨e0⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p)
    (f := f) h.card_eq_sq
  let E : SL(2, fixedSubfield F p f) ≃* Su F p f 2 := e0.trans (suEquiv h 2).symm
  let β' : A →* MulAut SL(2, fixedSubfield F p f) := (MulAut.congr E.symm).toMonoidHom.comp β
  have hc : ∀ a x, β a (E x) = E (β' a x) := by
    intro a x
    simp [β', MulAut.congr_apply]
  have hni' : ¬ β'.range ≤
      (MulAut.conj : SL(2, fixedSubfield F p f) →* MulAut SL(2, fixedSubfield F p f)).range := by
    intro hle
    apply hni
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := hle ⟨a, rfl⟩
    refine ⟨E s, MulEquiv.ext fun y => ?_⟩
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [hc, ← hs]
    simp [MulAut.conj_apply]
  have hsmall' : Nat.card β'.range ≤ 4 := by
    have : β'.range = β.range.map (MulAut.congr E.symm).toMonoidHom := by
      rw [MonoidHom.range_comp]
    rw [this, Subgroup.card_map_of_injective (MulAut.congr E.symm).injective]
    exact hsmall
  have hK' : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield h.card_eq_sq
  have h1 : gammaAct β' = ⊤ :=
    GenLocL3Nine.gammaAct_sl2_of_not_inner_small h.prime hp2 hK' h5 β' hA hni' hsmall'
  have := GenLocBasic.gammaAct_map_equiv E β' β hc
  rw [this, h1, Subgroup.map_top_of_surjective _ E.surjective]

theorem card_le_two_of_A0 {A B : Type} [Group A] [Group B] (A0 : Subgroup A) (hall : ∀ a : A, a ∈ A0)
    (β : A →* B) (hβ : ∀ a ∈ A0, ∀ a' ∈ A0, β a = 1 ∨ β a' = 1 ∨ β a = β a') :
    Nat.card β.range ≤ 2 := by
  classical
  obtain ⟨τ, hτ⟩ : ∃ τ : B, ∀ a ∈ A0, β a = 1 ∨ β a = τ := by
    by_cases hex : ∃ a ∈ A0, β a ≠ 1
    · obtain ⟨a1, ha1, hne⟩ := hex
      refine ⟨β a1, fun a ha => ?_⟩
      rcases hβ a ha a1 ha1 with h | h | h
      · exact Or.inl h
      · exact absurd h hne
      · exact Or.inr h
    · push Not at hex
      exact ⟨1, fun a ha => Or.inl (hex a ha)⟩
  have hsub : (β.range : Set B) ⊆ {1, τ} := by
    rintro _ ⟨a, rfl⟩
    rcases hτ a (hall a) with h | h
    · simp [h]
    · simp [h]
  calc Nat.card β.range = (β.range : Set B).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, τ} : Set B).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp

theorem card_le_four_of_A0 {A B : Type} [Group A] [Group B] (hsq : ∀ a : A, a * a = 1)
    (A0 : Subgroup A) (hA0 : ∀ a b : A, a ∉ A0 → b ∉ A0 → a * b ∈ A0) (β : A →* B)
    (hβ : ∀ a ∈ A0, ∀ a' ∈ A0, β a = 1 ∨ β a' = 1 ∨ β a = β a') :
    Nat.card β.range ≤ 4 := by
  classical
  by_cases hall : ∀ a : A, a ∈ A0
  · have := card_le_two_of_A0 A0 hall β hβ
    omega
  obtain ⟨τ, hτ⟩ : ∃ τ : B, ∀ a ∈ A0, β a = 1 ∨ β a = τ := by
    by_cases hex : ∃ a ∈ A0, β a ≠ 1
    · obtain ⟨a1, ha1, hne⟩ := hex
      refine ⟨β a1, fun a ha => ?_⟩
      rcases hβ a ha a1 ha1 with h | h | h
      · exact Or.inl h
      · exact absurd h hne
      · exact Or.inr h
    · push Not at hex
      exact ⟨1, fun a ha => Or.inl (hex a ha)⟩
  push Not at hall
  obtain ⟨a2, ha2⟩ := hall
  have hsub : (β.range : Set B) ⊆ {1, τ, β a2, τ * β a2} := by
    rintro _ ⟨a, rfl⟩
    by_cases ha : a ∈ A0
    · rcases hτ a ha with h | h
      · simp [h]
      · simp [h]
    · have hm := hA0 a a2 ha ha2
      have hb : β a = β (a * a2) * β a2 := by
        have : a = (a * a2) * a2 := by
          rw [mul_assoc, hsq a2, mul_one]
        conv_lhs => rw [this]
        rw [map_mul]
      rcases hτ _ hm with h | h
      · rw [hb, h]; simp
      · rw [hb, h]; simp
  calc Nat.card β.range = (β.range : Set B).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, τ, β a2, τ * β a2} : Set B).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      simp

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem DU.entry_norm {h : UnitaryFieldData p f F} {Δ : GL (Fin 3) F} (hΔ : DU h Δ) (u : Fin 3) :
    h.bar ((Δ : Matrix (Fin 3) (Fin 3) F) u u) * (Δ : Matrix (Fin 3) (Fin 3) F) u u = 1 := by
  have := congrFun (congrFun hΔ.1 u) u
  rw [Matrix.mul_apply, Finset.sum_eq_single u] at this
  · simpa using this
  · intro k _ hk
    rw [hΔ.2 hk]
    simp
  · simp

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem DU.entry_ne_zero {h : UnitaryFieldData p f F} {Δ : GL (Fin 3) F} (hΔ : DU h Δ) (u : Fin 3) :
    (Δ : Matrix (Fin 3) (Fin 3) F) u u ≠ 0 := by
  intro h0
  have := hΔ.entry_norm u
  rw [h0, mul_zero] at this
  exact zero_ne_one this

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem diag_sq_eq {Δ : GL (Fin 3) F} (hΔ : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag) {c : F}
    (hc : (Δ : Matrix (Fin 3) (Fin 3) F) * (Δ : Matrix (Fin 3) (Fin 3) F) = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (u : Fin 3) : (Δ : Matrix (Fin 3) (Fin 3) F) u u * (Δ : Matrix (Fin 3) (Fin 3) F) u u = c := by
  have := congrFun (congrFun hc u) u
  rw [Matrix.mul_apply, Finset.sum_eq_single u] at this
  · simpa using this
  · intro k _ hk
    rw [hΔ hk.symm]
    simp
  · simp

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem sq_scalar_of_isLift (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) {x : MulAut J} (hx : x * x = 1)
    {Δ : GL (Fin 3) F} (hl : IsLift θ Δ 1 x) :
    ∃ c : F, (Δ : Matrix (Fin 3) (Fin 3) F) * (Δ : Matrix (Fin 3) (Fin 3) F) =
      c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := hl.mul hl
  rw [glAut_one_apply, mul_one, hx] at h1
  obtain ⟨c, hc⟩ := IsLift.unique h h2 hPerf hker h1 (isLift_one (θ := θ))
  exact ⟨c, by simpa [Units.val_mul] using hc⟩

theorem su2_ext {y y' : Su F p f 2} (hy : ∀ u v, ym y u v = ym y' u v) : y = y' :=
  Subtype.ext (Units.ext (Matrix.ext hy))

theorem blk_A0_form (h : UnitaryFieldData p f F) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) (σ : Equiv.Perm (Fin 3))
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1) (i : Fin 2)
    (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ (pgl σ) (pgl_unitary h σ) i y) =
      frameBlock h θ (pgl σ) (pgl_unitary h σ) i (β a y))
    {a : A} (ha : a ∈ A0 h θ α hsq) :
    ∃ s : F, (s = 1 ∨ s = -1) ∧ ∀ (y : Su F p f 2) (u v : Fin 2),
      ym (β a y) u v = (if u = v then 1 else s) * ym y u v := by
  obtain ⟨Δ, hl, hD⟩ := ha
  have hx : α a * α a = 1 := by rw [← map_mul, hsq a, map_one]
  obtain ⟨c, hc⟩ := sq_scalar_of_isLift h h2 hPerf hker hx hl
  set e : Fin 2 → F := fun u =>
    (Δ : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i u)) (σ (idx3 i u)) with he
  have he2 : ∀ u, e u * e u = c := fun u => diag_sq_eq hD.2 hc _
  have he0 : ∀ u, e u ≠ 0 := fun u => hD.entry_ne_zero _
  have hc0 : c ≠ 0 := by
    rw [← he2 0]
    exact mul_ne_zero (he0 0) (he0 0)
  set s : F := e 0 * (e 1)⁻¹ with hs
  have hss : s * s = 1 := by
    rw [hs]
    have h0 := he0 0
    have h1 := he0 1
    field_simp
    linear_combination he2 0 - he2 1
  have hs' : e 1 * (e 0)⁻¹ = s := by
    calc e 1 * (e 0)⁻¹ = (e 0 * (e 1)⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
      _ = s := inv_eq_of_mul_eq_one_right hss
  refine ⟨s, mul_self_eq_one_iff.1 hss, fun y u v => ?_⟩
  have := block_entries_of_spec h hθ σ α i β hβ hl hD.1 hD.2 y u v
  rw [this]
  have h0 := he0 0
  have h1 := he0 1
  have h1x : ∀ x : F, (1 : F ≃+* F) x = x := fun x => rfl
  simp only [h1x]
  fin_cases u <;> fin_cases v
  · simp
    change e 0 * ym y 0 0 * (e 0)⁻¹ = ym y 0 0
    field_simp
  · simp
    change e 0 * ym y 0 1 * (e 1)⁻¹ = s * ym y 0 1
    rw [hs]; ring
  · simp
    change e 1 * ym y 1 0 * (e 0)⁻¹ = s * ym y 1 0
    rw [← hs']; ring
  · simp
    change e 1 * ym y 1 1 * (e 1)⁻¹ = ym y 1 1
    field_simp

theorem blk_A0_eq (h : UnitaryFieldData p f F) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) (σ : Equiv.Perm (Fin 3))
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1) (i : Fin 2)
    (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ (pgl σ) (pgl_unitary h σ) i y) =
      frameBlock h θ (pgl σ) (pgl_unitary h σ) i (β a y))
    {a a' : A} (ha : a ∈ A0 h θ α hsq) (ha' : a' ∈ A0 h θ α hsq) :
    β a = 1 ∨ β a' = 1 ∨ β a = β a' := by
  obtain ⟨s, hs, hform⟩ := blk_A0_form h hθ h2 hPerf hker σ α hsq i β hβ ha
  obtain ⟨s', hs', hform'⟩ := blk_A0_form h hθ h2 hPerf hker σ α hsq i β hβ ha'
  have key : ∀ (b : A) (t : F), t = 1 →
      (∀ (y : Su F p f 2) (u v : Fin 2), ym (β b y) u v = (if u = v then 1 else t) * ym y u v) →
      β b = 1 := by
    intro b t ht hf
    refine MulEquiv.ext fun y => su2_ext fun u v => ?_
    rw [hf y u v, ht]
    simp [MulAut.one_apply]
  rcases hs with rfl | hs1
  · exact Or.inl (key a 1 rfl hform)
  · rcases hs' with rfl | hs1'
    · exact Or.inr (Or.inl (key a' 1 rfl hform'))
    · refine Or.inr (Or.inr (MulEquiv.ext fun y => su2_ext fun u v => ?_))
      rw [hform y u v, hform' y u v, hs1, hs1']

theorem card_block_le_four (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0)
    (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) (σ : Equiv.Perm (Fin 3))
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1)
    (hα : ∀ a, DiagLift h θ (α a)) (i : Fin 2) (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ (pgl σ) (pgl_unitary h σ) i y) =
      frameBlock h θ (pgl σ) (pgl_unitary h σ) i (β a y)) :
    Nat.card β.range ≤ 4 :=
  card_le_four_of_A0 hsq (A0 h θ α hsq) (fun _ _ ha hb => mul_mem_A0 h α hsq hα ha hb) β
    (fun _ ha _ ha' => blk_A0_eq h hθ h2 hPerf hker σ α hsq i β hβ ha ha')

theorem card_block_le_two (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0)
    (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) (σ : Equiv.Perm (Fin 3))
    {A : Type} [Group A] (α : A →* MulAut J) (hsq : ∀ a : A, a * a = 1)
    (hall : ∀ a, a ∈ A0 h θ α hsq) (i : Fin 2) (β : A →* MulAut (Su F p f 2))
    (hβ : ∀ a y, α a (frameBlock h θ (pgl σ) (pgl_unitary h σ) i y) =
      frameBlock h θ (pgl σ) (pgl_unitary h σ) i (β a y)) :
    Nat.card β.range ≤ 2 :=
  card_le_two_of_A0 (A0 h θ α hsq) hall β (fun _ ha _ ha' => blk_A0_eq h hθ h2 hPerf hker σ α hsq i β hβ ha ha')

theorem gammaAct_eq_top_of_card_le_two {J : Type} [Group J] {A : Type} [Group A] [Finite A]
    (hA : IsRank23 A) (β : A →* MulAut J) (h2 : Nat.card β.range ≤ 2) : gammaAct β = ⊤ :=
  gammaAct_eq_top_of_le_ker β (rank_ker_ge hA.1 β h2) le_rfl

theorem gammaAct_eq_top_of_nonInner (h : UnitaryFieldData p f F)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) {A : Type} [Group A] [Finite A]
    (hA : IsRank23 A) (α : A →* MulAut J) (hα : ∀ a, DiagLift h θ (α a)) (σ : Equiv.Perm (Fin 3))
    (hns : ∀ i : Fin 2, ∃ (a : A) (Δ : GL (Fin 3) F) (ψ : F ≃+* F), IsLift θ Δ ψ (α a) ∧
      (ψ = 1 ∨ ∀ c, ψ c = h.bar c) ∧ DU h Δ ∧
      ¬ ∃ n : F, h.bar n * n = 1 ∧ n * n =
        ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i 0)) (σ (idx3 i 0)) *
          ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i 1)) (σ (idx3 i 1))) :
    gammaAct α = ⊤ := by
  have hsq : ∀ a : A, a * a = 1 := fun a =>
    WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have hq : p ^ f ≠ 2 := by omega
  refine gammaAct_eq_top_of_blocks_frame h hq hθ (pgl_unitary h σ) α
    (fun a => frameForm_perm h σ (hα a)) fun i β hβ => ?_
  obtain ⟨a, Δ, ψ, hl, hψ, hD, hns'⟩ := hns i
  have hni : ¬ β.range ≤ (MulAut.conj : Su F p f 2 →* MulAut (Su F p f 2)).range := by
    intro hle
    refine not_inner_of_entries h (by omega)
      (fun u => ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (σ (idx3 i u)) (σ (idx3 i u)))
      (fun u => hD.entry_norm _) hψ
      (fun y u v => block_entries_of_spec h hθ σ α i β hβ hl hD.1 hD.2 y u v) hns'
      (hle ⟨a, rfl⟩)
  exact gammaAct_su2_of_not_inner_small h hp2 h5 hA β hni
    (card_block_le_four h hθ h2 hPerf hker σ α hsq hα i β hβ)

theorem gammaAct_eq_top_of_A0_top (h : UnitaryFieldData p f F) (hq : p ^ f ≠ 2) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0)
    (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3)) {A : Type} [Group A] [Finite A]
    (hA : IsRank23 A) (α : A →* MulAut J) (hα : ∀ a, DiagLift h θ (α a))
    (hsq : ∀ a : A, a * a = 1) (hall : ∀ a, a ∈ A0 h θ α hsq) : gammaAct α = ⊤ :=
  gammaAct_eq_top_of_blocks_frame h hq hθ (pgl_unitary h (1 : Equiv.Perm (Fin 3))) α
    (fun a => frameForm_perm h 1 (hα a)) fun i β hβ =>
      gammaAct_eq_top_of_card_le_two hA β (card_block_le_two h hθ h2 hPerf hker 1 α hsq hall i β hβ)

end GenLocU3Good

end CFSG.GH74.Generic.BProg.B2
