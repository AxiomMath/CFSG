module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrame
import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.S1.Uni Matrix

namespace GenLocU4OutFrDb

open GenLocU4Basic GenLocU4Out

variable {p f : ℕ} {K : Type} [Field K]


theorem conj_diag_aux (h : UnitaryFieldData p f K) {P X : primeFormUnitary h (idGram K 4)}
    (hX2 : X * X = 1)
    (hD : (((P⁻¹ * X * P : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).IsDiag) :
    ∃ σ : Fin 4 → K, (∀ k, σ k = 1 ∨ σ k = -1) ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal σ := by
  set D : Matrix (Fin 4) (Fin 4) K :=
    (((P⁻¹ * X * P : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hDdef
  have hDD : D * D = 1 := by
    have e : (P⁻¹ * X * P) * (P⁻¹ * X * P) = (1 : primeFormUnitary h (idGram K 4)) := by
      calc (P⁻¹ * X * P) * (P⁻¹ * X * P) = P⁻¹ * (X * X) * P := by group
        _ = 1 := by rw [hX2]; group
    have := congrArg (fun u : primeFormUnitary h (idGram K 4) => ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) e
    simpa [hDdef] using this
  have hDeq : D = Matrix.diagonal (fun k => D k k) := hD.diagonal_diag.symm
  refine ⟨fun k => D k k, fun k => ?_, ?_⟩
  · have := congrFun (congrFun hDD k) k
    rw [hDeq] at this
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact mul_self_eq_one_iff.1 this
  · rw [← hDeq]
    have e : ((P : GL (Fin 4) K)) * (((P⁻¹ * X * P : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K)) =
        (X : GL (Fin 4) K) * (P : GL (Fin 4) K) := by
      change (P : GL (Fin 4) K) * ((P : GL (Fin 4) K)⁻¹ * (X : GL (Fin 4) K) * (P : GL (Fin 4) K)) = (X : GL (Fin 4) K) * (P : GL (Fin 4) K)
      group
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) e
    simpa [hDdef] using this.symm


theorem exists_frame_diag2 [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {y z : Matrix (Fin 4) (Fin 4) K}
    (hy : GenLocU4Basic.IsUnitaryU (p ^ f) y) (hy2 : y * y = 1)
    (hz : GenLocU4Basic.IsUnitaryU (p ^ f) z) (hz2 : z * z = 1) (hyz : y * z = z * y) :
    ∃ (P : Matrix (Fin 4) (Fin 4) K) (σy σz : Fin 4 → K),
      GenLocU4Basic.IsUnitaryU (p ^ f) P ∧ (∀ i, σy i = 1 ∨ σy i = -1) ∧ (∀ i, σz i = 1 ∨ σz i = -1) ∧
      y * P = P * Matrix.diagonal σy ∧ z * P = P * Matrix.diagonal σz := by
  classical
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hpq : 2 ∣ p ^ f + 1 := even_iff_two_dvd.1 ((h.prime.odd_of_ne_two hp2).pow).add_one
  let Y : GL (Fin 4) K := ⟨y, y, hy2, hy2⟩
  let Z : GL (Fin 4) K := ⟨z, z, hz2, hz2⟩
  have hYm : Y ∈ primeFormUnitary h (idGram K 4) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [GenLocU4ExtFrame.map_bar_eq h]; exact hy
  have hZm : Z ∈ primeFormUnitary h (idGram K 4) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [GenLocU4ExtFrame.map_bar_eq h]; exact hz
  let Y' : primeFormUnitary h (idGram K 4) := ⟨Y, hYm⟩
  let Z' : primeFormUnitary h (idGram K 4) := ⟨Z, hZm⟩
  have hYZ : Y' * Z' = Z' * Y' := Subtype.ext (Units.ext hyz)
  have hY2 : Y' * Y' = 1 := Subtype.ext (Units.ext hy2)
  have hZ2 : Z' * Z' = 1 := Subtype.ext (Units.ext hz2)
  have hcs : ({Y', Z'} : Set (primeFormUnitary h (idGram K 4))).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hYZ
    · exact hYZ.symm
    · exact Commute.refl _
  have := Subgroup.isMulCommutative_closure hcs
  set G := Subgroup.closure ({Y', Z'} : Set (primeFormUnitary h (idGram K 4))) with hG
  have hcomm : ∀ x ∈ G, ∀ w ∈ G, x * w = w * x := fun x hx w hw =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : G) ⟨w, hw⟩)
  have hpow : ∀ x ∈ G, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [pow_two]; exact hY2
      · rw [pow_two]; exact hZ2
    | one => exact one_pow 2
    | mul x w hx hw ihx ihw =>
      rw [pow_two] at ihx ihw ⊢
      calc x * w * (x * w) = x * (w * x) * w := by group
        _ = x * (x * w) * w := by rw [hcomm w hw x hx]
        _ = (x * x) * (w * w) := by group
        _ = 1 := by rw [ihx, ihw, one_mul]
    | inv x hx ihx =>
      rw [inv_pow, ihx, inv_one]
  obtain ⟨P, hP⟩ := KFU.exists_unitary_conj_diag h Nat.prime_two hpq G hcomm hpow
  obtain ⟨σy, hσy, hyP⟩ := conj_diag_aux h hY2 (hP Y' (Subgroup.subset_closure (by simp)))
  obtain ⟨σz, hσz, hzP⟩ := conj_diag_aux h hZ2 (hP Z' (Subgroup.subset_closure (by simp)))
  refine ⟨((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), σy, σz, ?_, hσy, hσz, hyP, hzP⟩
  have hP1 := (mem_primeFormUnitary (h := h)).1 P.2
  simp only [idGram, Units.val_one, Matrix.mul_one] at hP1
  rw [GenLocU4ExtFrame.map_bar_eq h] at hP1
  exact hP1



theorem one_ne_neg_one (h2 : (2 : K) ≠ 0) : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)

theorem tpair_inj (h2 : (2 : K) ≠ 0) (k k' : Fin 4)
    (h1 : (![1, 1, -1, -1] : Fin 4 → K) k = (![1, 1, -1, -1] : Fin 4 → K) k')
    (h3 : (![1, -1, 1, -1] : Fin 4 → K) k = (![1, -1, 1, -1] : Fin 4 → K) k') : k = k' := by
  have hne : (1 : K) ≠ -1 := one_ne_neg_one h2
  have hne' : (-1 : K) ≠ 1 := fun h => hne h.symm
  fin_cases k <;> fin_cases k' <;> simp_all

theorem sign_prod_zero {a b x y : K} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) (hn : ¬ (x = a ∧ y = b)) : (1 + a * x) * (1 + b * y) = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;> first | exact absurd ⟨rfl, rfl⟩ hn | norm_num

theorem exists_col (h2 : (2 : K) ≠ 0) {u v : Fin 4 → K}
    (hu : ∀ i, u i = 1 ∨ u i = -1) (hv : ∀ i, v i = 1 ∨ v i = -1)
    (hsu : u 0 + u 1 + u 2 + u 3 = 0) (hsv : v 0 + v 1 + v 2 + v 3 = 0)
    (hsuv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) {a b : K}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : ∃ i, u i = a ∧ v i = b := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  by_contra hcon
  have key : ∀ i, (1 + a * u i) * (1 + b * v i) = 0 := fun i =>
    sign_prod_zero ha hb (hu i) (hv i) (fun hi => hcon ⟨i, hi⟩)
  have hsum : (1 + a * u 0) * (1 + b * v 0) + (1 + a * u 1) * (1 + b * v 1) +
      (1 + a * u 2) * (1 + b * v 2) + (1 + a * u 3) * (1 + b * v 3) = 0 := by
    rw [key 0, key 1, key 2, key 3]; ring
  exact h4 (by linear_combination hsum - a * hsu - b * hsv - a * b * hsuv)

theorem exists_bij (h2 : (2 : K) ≠ 0) {u v : Fin 4 → K}
    (hu : ∀ i, u i = 1 ∨ u i = -1) (hv : ∀ i, v i = 1 ∨ v i = -1)
    (hsu : u 0 + u 1 + u 2 + u 3 = 0) (hsv : v 0 + v 1 + v 2 + v 3 = 0)
    (hsuv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) {εy εz : K}
    (hεy : εy = 1 ∨ εy = -1) (hεz : εz = 1 ∨ εz = -1) :
    ∃ τ' : Fin 4 → Fin 4, Function.Bijective τ' ∧
      ∀ k, u (τ' k) = εy * (![1, 1, -1, -1] : Fin 4 → K) k ∧
        v (τ' k) = εz * (![1, -1, 1, -1] : Fin 4 → K) k := by
  have hT : ∀ k, (![1, 1, -1, -1] : Fin 4 → K) k = 1 ∨ (![1, 1, -1, -1] : Fin 4 → K) k = -1 := by
    intro k; fin_cases k <;> simp
  have hS : ∀ k, (![1, -1, 1, -1] : Fin 4 → K) k = 1 ∨ (![1, -1, 1, -1] : Fin 4 → K) k = -1 := by
    intro k; fin_cases k <;> simp
  have hmul : ∀ {a b : K}, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → (a * b = 1 ∨ a * b = -1) := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  choose τ' hτ' using fun k => exists_col h2 hu hv hsu hsv hsuv (hmul hεy (hT k)) (hmul hεz (hS k))
  have hinj : Function.Injective τ' := by
    intro k k' hkk
    have e1 := (hτ' k).1
    have e2 := (hτ' k').1
    have e3 := (hτ' k).2
    have e4 := (hτ' k').2
    rw [hkk] at e1 e3
    have hy0 : εy ≠ 0 := by rcases hεy with rfl | rfl <;> simp
    have hz0 : εz ≠ 0 := by rcases hεz with rfl | rfl <;> simp
    exact tpair_inj h2 k k' (mul_left_cancel₀ hy0 (e1.symm.trans e2)) (mul_left_cancel₀ hz0 (e3.symm.trans e4))
  exact ⟨τ', Finite.injective_iff_bijective.1 hinj, fun k => hτ' k⟩

theorem pairs_distinct (h2 : (2 : K) ≠ 0) {u v : Fin 4 → K}
    (hu : ∀ i, u i = 1 ∨ u i = -1) (hv : ∀ i, v i = 1 ∨ v i = -1)
    (hsu : u 0 + u 1 + u 2 + u 3 = 0) (hsv : v 0 + v 1 + v 2 + v 3 = 0)
    (hsuv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) :
    ∀ i j, i ≠ j → u i ≠ u j ∨ v i ≠ v j := by
  obtain ⟨τ', hbij, hτ'⟩ := exists_bij h2 hu hv hsu hsv hsuv (Or.inl rfl : (1 : K) = 1 ∨ (1 : K) = -1)
    (Or.inl rfl : (1 : K) = 1 ∨ (1 : K) = -1)
  intro i j hij
  obtain ⟨k, rfl⟩ := hbij.2 i
  obtain ⟨k', rfl⟩ := hbij.2 j
  by_contra hcon
  push Not at hcon
  have e1 := (hτ' k).1
  have e2 := (hτ' k').1
  have e3 := (hτ' k).2
  have e4 := (hτ' k').2
  rw [hcon.1] at e1
  rw [hcon.2] at e3
  exact hij (congrArg τ' (tpair_inj h2 k k' (by rw [one_mul] at e1 e2; exact e1.symm.trans e2)
    (by rw [one_mul] at e3 e4; exact e3.symm.trans e4)))

theorem prod_cases (h2 : (2 : K) ≠ 0) {t : Fin 4 → K} (ht : ∀ i, t i = 1 ∨ t i = -1)
    (htp : t 0 * t 1 * t 2 * t 3 = -1) :
    ∃ (ε : K) (j0 : Fin 4), (ε = 1 ∨ ε = -1) ∧ ∀ i, t i = ε * (if i = j0 then -1 else 1) := by
  rcases ht 0 with a0 | a0 <;> rcases ht 1 with a1 | a1 <;> rcases ht 2 with a2 | a2 <;>
    rcases ht 3 with a3 | a3 <;> rw [a0, a1, a2, a3] at htp <;>
    first
    | (exfalso; apply h2; linear_combination htp)
    | (refine ⟨1, 0, Or.inl rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨1, 1, Or.inl rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨1, 2, Or.inl rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨1, 3, Or.inl rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨-1, 0, Or.inr rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨-1, 1, Or.inr rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨-1, 2, Or.inr rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3]; done)
    | (refine ⟨-1, 3, Or.inr rfl, fun i => ?_⟩; fin_cases i <;> simp [a0, a1, a2, a3])

theorem sorted_cols (h2 : (2 : K) ≠ 0) {u v t : Fin 4 → K}
    (hu : ∀ i, u i = 1 ∨ u i = -1) (hv : ∀ i, v i = 1 ∨ v i = -1) (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hsu : u 0 + u 1 + u 2 + u 3 = 0) (hsv : v 0 + v 1 + v 2 + v 3 = 0)
    (hsuv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (htp : t 0 * t 1 * t 2 * t 3 = -1) :
    ∃ (τ' : Fin 4 → Fin 4) (εy εz ε : K), Function.Injective τ' ∧ (εy = 1 ∨ εy = -1) ∧
      (εz = 1 ∨ εz = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ k, u (τ' k) = εy * (![1, 1, -1, -1] : Fin 4 → K) k ∧
        v (τ' k) = εz * (![1, -1, 1, -1] : Fin 4 → K) k ∧
        t (τ' k) = ε * (![1, 1, 1, -1] : Fin 4 → K) k := by
  obtain ⟨ε, j0, hε, htj⟩ := prod_cases h2 ht htp
  have hεy : -u j0 = 1 ∨ -u j0 = -1 := by rcases hu j0 with h | h <;> simp [h]
  have hεz : -v j0 = 1 ∨ -v j0 = -1 := by rcases hv j0 with h | h <;> simp [h]
  obtain ⟨τ', hbij, hτ'⟩ := exists_bij h2 hu hv hsu hsv hsuv hεy hεz
  have hy0 : -u j0 ≠ 0 := by rcases hu j0 with h | h <;> simp [h]
  have hz0 : -v j0 ≠ 0 := by rcases hv j0 with h | h <;> simp [h]
  have hj0 : τ' 3 = j0 := by
    obtain ⟨k1, hk1⟩ := hbij.2 j0
    have e1 := (hτ' k1).1
    have e3 := (hτ' k1).2
    rw [hk1] at e1 e3
    have g1 : (-1 : K) = (![1, 1, -1, -1] : Fin 4 → K) k1 :=
      mul_left_cancel₀ hy0 (by linear_combination e1)
    have g3 : (-1 : K) = (![1, -1, 1, -1] : Fin 4 → K) k1 :=
      mul_left_cancel₀ hz0 (by linear_combination e3)
    have : k1 = 3 := tpair_inj h2 k1 3 (by rw [← g1]; simp) (by rw [← g3]; simp)
    rw [← hk1, this]
  have hne : ∀ k, k ≠ 3 → τ' k ≠ j0 := fun k hk h => hk (hbij.1 (h.trans hj0.symm))
  refine ⟨τ', -u j0, -v j0, ε, hbij.1, hεy, hεz, hε, fun k => ⟨(hτ' k).1, (hτ' k).2, ?_⟩⟩
  rw [htj (τ' k)]
  fin_cases k
  · simp [hne 0 (by decide)]
  · simp [hne 1 (by decide)]
  · simp [hne 2 (by decide)]
  · simp [hj0]



theorem Pt_Pbar (h : UnitaryFieldData p f K) {P : Matrix (Fin 4) (Fin 4) K} (hP : cT h P * P = 1) :
    Pᵀ * P.map h.bar = 1 := by
  have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) hP
  simp only [Matrix.map_mul, cT, Matrix.transpose_map, map_bar_bar h] at this
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem trace_eq_of_frame (h : UnitaryFieldData p f K) {X P D : Matrix (Fin 4) (Fin 4) K}
    (hP : cT h P * P = 1) (hX : X * P = P * D) : X.trace = D.trace := by
  have hP' : P * cT h P = 1 := mul_eq_one_comm.mp hP
  calc X.trace = (X * (P * cT h P)).trace := by rw [hP', Matrix.mul_one]
    _ = (P * D * cT h P).trace := by rw [← Matrix.mul_assoc, hX]
    _ = (cT h P * (P * D)).trace := Matrix.trace_mul_comm _ _
    _ = D.trace := by rw [← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem bar_diagonal (h : UnitaryFieldData p f K) {σ : Fin 4 → K} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    (Matrix.diagonal σ).map h.bar = Matrix.diagonal σ := by
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  rcases hσ i with e | e <;> simp [e]

theorem comm_aux (h : UnitaryFieldData p f K) {x B P : Matrix (Fin 4) (Fin 4) K} {σ : Fin 4 → K}
    (hP : cT h P * P = 1) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (hxP : x * P = P * Matrix.diagonal σ)
    (hxB : x * B = B * x.map h.bar) :
    Matrix.diagonal σ * (cT h P * B * P.map h.bar) = (cT h P * B * P.map h.bar) * Matrix.diagonal σ := by
  have hP' : P * cT h P = 1 := mul_eq_one_comm.mp hP
  have e1 : cT h P * x = Matrix.diagonal σ * cT h P := by
    calc cT h P * x = cT h P * x * (P * cT h P) := by rw [hP', Matrix.mul_one]
      _ = cT h P * (x * P) * cT h P := by simp only [Matrix.mul_assoc]
      _ = cT h P * (P * Matrix.diagonal σ) * cT h P := by rw [hxP]
      _ = (cT h P * P) * Matrix.diagonal σ * cT h P := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal σ * cT h P := by rw [hP, Matrix.one_mul]
  have e2 : x.map h.bar * P.map h.bar = P.map h.bar * Matrix.diagonal σ := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) hxP
    simp only [Matrix.map_mul] at this
    rw [bar_diagonal h hσ] at this
    exact this
  calc Matrix.diagonal σ * (cT h P * B * P.map h.bar)
      = (Matrix.diagonal σ * cT h P) * B * P.map h.bar := by simp only [Matrix.mul_assoc]
    _ = (cT h P * x) * B * P.map h.bar := by rw [e1]
    _ = cT h P * (x * B) * P.map h.bar := by simp only [Matrix.mul_assoc]
    _ = cT h P * (B * x.map h.bar) * P.map h.bar := by rw [hxB]
    _ = cT h P * B * (x.map h.bar * P.map h.bar) := by simp only [Matrix.mul_assoc]
    _ = cT h P * B * (P.map h.bar * Matrix.diagonal σ) := by rw [e2]
    _ = (cT h P * B * P.map h.bar) * Matrix.diagonal σ := by simp only [Matrix.mul_assoc]

theorem exists_B_diag (h : UnitaryFieldData p f K) {y z B P : Matrix (Fin 4) (Fin 4) K} {σy σz : Fin 4 → K}
    (hP : cT h P * P = 1) (hσy : ∀ i, σy i = 1 ∨ σy i = -1) (hσz : ∀ i, σz i = 1 ∨ σz i = -1)
    (hyP : y * P = P * Matrix.diagonal σy) (hzP : z * P = P * Matrix.diagonal σz)
    (hyB : y * B = B * y.map h.bar) (hzB : z * B = B * z.map h.bar)
    (hd : ∀ i j, i ≠ j → σy i ≠ σy j ∨ σz i ≠ σz j) :
    ∃ β : Fin 4 → K, B * P.map h.bar = P * Matrix.diagonal β := by
  have hP' : P * cT h P = 1 := mul_eq_one_comm.mp hP
  have hyc := comm_aux h hP hσy hyP hyB
  have hzc := comm_aux h hP hσz hzP hzB
  set B' := cT h P * B * P.map h.bar with hB'
  have hoff : ∀ i j, i ≠ j → B' i j = 0 := by
    intro i j hij
    have e1 := congrFun (congrFun hyc i) j
    have e2 := congrFun (congrFun hzc i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e1 e2
    rcases hd i j hij with hne | hne
    · have : B' i j * (σy i - σy j) = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
    · have : B' i j * (σz i - σz j) = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have hBeq : B * P.map h.bar = P * B' := by
    calc B * P.map h.bar = (P * cT h P) * B * P.map h.bar := by rw [hP', Matrix.one_mul]
      _ = P * B' := by simp only [hB', Matrix.mul_assoc]
  refine ⟨fun j => B' j j, ?_⟩
  rw [hBeq]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]; exact hoff i j hij


theorem diag_comm (d σ : Fin 4 → K) :
    Matrix.diagonal σ * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal σ := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem prod_sign {t : Fin 4 → K} (ht : ∀ i, t i = 1 ∨ t i = -1) :
    t 0 * t 1 * t 2 * t 3 = 1 ∨ t 0 * t 1 * t 2 * t 3 = -1 := by
  rcases ht 0 with h0 | h0 <;> rcases ht 1 with h1 | h1 <;> rcases ht 2 with h2 | h2 <;>
    rcases ht 3 with h3 | h3 <;> simp [h0, h1, h2, h3]

theorem beta_norm (h : UnitaryFieldData p f K) {B P : Matrix (Fin 4) (Fin 4) K} {β : Fin 4 → K}
    (hB : cT h B * B = 1) (hP : cT h P * P = 1) (hBP : B * P.map h.bar = P * Matrix.diagonal β)
    (j : Fin 4) : β j ^ (p ^ f + 1) = 1 := by
  have hL : cT h (B * P.map h.bar) * (B * P.map h.bar) = 1 := by
    have e : cT h (P.map h.bar) = Pᵀ := by rw [cT, map_bar_bar h]
    rw [cT_mul, e]
    calc Pᵀ * cT h B * (B * P.map h.bar) = Pᵀ * (cT h B * B) * P.map h.bar := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB, Matrix.mul_one]; exact Pt_Pbar h hP
  rw [hBP] at hL
  have hR : cT h (P * Matrix.diagonal β) * (P * Matrix.diagonal β) =
      Matrix.diagonal (fun i => h.bar (β i) * β i) := by
    rw [cT_mul, GenLocU4OutFrame.cT_diagonal]
    calc Matrix.diagonal (fun i => h.bar (β i)) * cT h P * (P * Matrix.diagonal β)
        = Matrix.diagonal (fun i => h.bar (β i)) * (cT h P * P) * Matrix.diagonal β := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  rw [hR] at hL
  have := congrFun (congrFun hL j) j
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
  rw [UnitaryFieldData.bar_apply] at this
  rw [pow_succ]
  exact this

theorem rescale_frame [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (h : UnitaryFieldData p f K) {y z B P : Matrix (Fin 4) (Fin 4) K}
    {σy σz β : Fin 4 → K} (hP : cT h P * P = 1)
    (hyP : y * P = P * Matrix.diagonal σy) (hzP : z * P = P * Matrix.diagonal σz)
    (hβ : ∀ j, β j ^ (p ^ f + 1) = 1) (hBP : B * P.map h.bar = P * Matrix.diagonal β) :
    ∃ (P' : Matrix (Fin 4) (Fin 4) K) (t : Fin 4 → K), cT h P' * P' = 1 ∧ (∀ i, t i = 1 ∨ t i = -1) ∧
      y * P' = P' * Matrix.diagonal σy ∧ z * P' = P' * Matrix.diagonal σz ∧
      B * P'.map h.bar = P' * Matrix.diagonal t := by
  choose ω t hω ht hβω using fun j => GenLocU4OutFrame.exists_pm_omega hp hp2 hK hq (hβ j)
  have hωb : ∀ i, h.bar (ω i) * ω i = 1 := fun i => by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, hω i]
  have hωb' : ∀ i, ω i * h.bar (ω i) = 1 := fun i => by rw [mul_comm]; exact hωb i
  refine ⟨P * Matrix.diagonal ω, t, ?_, ht, ?_, ?_, ?_⟩
  · rw [cT_mul, GenLocU4OutFrame.cT_diagonal]
    calc Matrix.diagonal (fun i => h.bar (ω i)) * cT h P * (P * Matrix.diagonal ω)
        = Matrix.diagonal (fun i => h.bar (ω i)) * (cT h P * P) * Matrix.diagonal ω := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hP, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          ext i j
          by_cases hij : i = j
          · subst hij; simp [hωb]
          · simp [hij]
  · rw [← Matrix.mul_assoc, hyP, Matrix.mul_assoc, Matrix.mul_assoc, diag_comm]
  · rw [← Matrix.mul_assoc, hzP, Matrix.mul_assoc, Matrix.mul_assoc, diag_comm]
  · have e : (P * Matrix.diagonal ω).map h.bar =
        P.map h.bar * Matrix.diagonal (fun i => h.bar (ω i)) := by
      rw [Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
    rw [e, ← Matrix.mul_assoc, hBP, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    rw [hβω j]
    linear_combination (ω j * t j) * hωb' j

theorem prod_t_eq_neg_one (h : UnitaryFieldData p f K) {B P : Matrix (Fin 4) (Fin 4) K} {t : Fin 4 → K}
    (hP : cT h P * P = 1) (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hmin : GenLocU4Out.IsMinusU (p ^ f) B)
    (hBP : B * P.map h.bar = P * Matrix.diagonal t) : t 0 * t 1 * t 2 * t 3 = -1 := by
  rcases prod_sign ht with h1 | h1
  · exfalso
    have hdet := congrArg Matrix.det hBP
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four, h1] at hdet
    have hdetmap : (P.map h.bar).det = h.bar P.det := (RingHom.map_det (h.bar : K →+* K) P).symm
    have hdetcT : (cT h P).det = h.bar P.det := by
      rw [cT, Matrix.det_transpose]
      exact hdetmap
    have hdU : h.bar P.det * P.det = 1 := by
      have := congrArg Matrix.det hP
      rwa [Matrix.det_mul, hdetcT, Matrix.det_one] at this
    have hdUq : P.det ^ (p ^ f + 1) = 1 := by
      rw [pow_succ]
      rw [UnitaryFieldData.bar_apply] at hdU
      exact hdU
    rw [hdetmap, mul_one] at hdet
    apply hmin.2 P.det hdUq
    calc P.det * P.det = (B.det * h.bar P.det) * P.det := by rw [hdet]
      _ = B.det * (h.bar P.det * P.det) := by ring
      _ = B.det := by rw [hdU, mul_one]
  · exact h1



theorem submatrix_diag {X Q P : Matrix (Fin 4) (Fin 4) K} {d : Fin 4 → K}
    (hX : X * Q = P * Matrix.diagonal d) (τ : Fin 4 → Fin 4) (e : Fin 4 → K)
    (he : ∀ k, d (τ k) = e k) :
    X * Q.submatrix id τ = P.submatrix id τ * Matrix.diagonal e := by
  ext r k
  have h1 := congrFun (congrFun hX r) (τ k)
  rw [Matrix.mul_diagonal] at h1
  rw [Matrix.mul_diagonal, Matrix.submatrix_apply, id, ← he k, ← h1]
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

theorem smul_tT (ε : K) : ε • (tT : Matrix (Fin 4) (Fin 4) K) =
    Matrix.diagonal (fun k => ε * (![1, 1, -1, -1] : Fin 4 → K) k) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [tT]
  · simp [tT, hij]

theorem smul_tS (ε : K) : ε • (tS : Matrix (Fin 4) (Fin 4) K) =
    Matrix.diagonal (fun k => ε * (![1, -1, 1, -1] : Fin 4 → K) k) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [tS]
  · simp [tS, hij]

theorem smul_mD (ε : K) : ε • (mD : Matrix (Fin 4) (Fin 4) K) =
    Matrix.diagonal (fun k => ε * (![1, 1, 1, -1] : Fin 4 → K) k) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [mD]
  · simp [mD, hij]

theorem exists_Db_frame {p f : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {y z B : Matrix (Fin 4) (Fin 4) K} (hy : IsUnitaryU (p ^ f) y) (hy2 : y * y = 1) (hytr : y.trace = 0)
    (hz : IsUnitaryU (p ^ f) z) (hz2 : z * z = 1) (hztr : z.trace = 0) (hyz : y * z = z * y)
    (hyztr : (y * z).trace = 0)
    (hB : IsUnitaryU (p ^ f) B) (hmin : IsMinusU (p ^ f) B)
    (hyB : y * B = B * y.map (· ^ (p ^ f))) (hzB : z * B = B * z.map (· ^ (p ^ f))) :
    ∃ (U : Matrix (Fin 4) (Fin 4) K) (εy εz : K), IsUnitaryU (p ^ f) U ∧ (εy = 1 ∨ εy = -1) ∧
      (εz = 1 ∨ εz = -1) ∧
      y * U = U * (εy • (tT : Matrix (Fin 4) (Fin 4) K)) ∧ z * U = U * (εz • (tS : Matrix (Fin 4) (Fin 4) K)) ∧
      (B * U.map (· ^ (p ^ f)) = U * (mD : Matrix (Fin 4) (Fin 4) K) ∨
        B * U.map (· ^ (p ^ f)) = U * (-(mD : Matrix (Fin 4) (Fin 4) K))) := by
  classical
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hBc : cT h B * B = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h B).1 hB
  have hyB' : y * B = B * y.map h.bar := by rw [GenLocU4ExtFrame.map_bar_eq h]; exact hyB
  have hzB' : z * B = B * z.map h.bar := by rw [GenLocU4ExtFrame.map_bar_eq h]; exact hzB
  obtain ⟨P, σy, σz, hPU, hσy, hσz, hyP, hzP⟩ := exists_frame_diag2 hp hp2 hK hy hy2 hz hz2 hyz
  have hPc : cT h P * P = 1 := (GenLocU4OutFrame.isUnitaryU_iff_cT h P).1 hPU
  have hsy : σy 0 + σy 1 + σy 2 + σy 3 = 0 := by
    have := trace_eq_of_frame h hPc hyP
    rw [hytr, Matrix.trace_diagonal, Fin.sum_univ_four] at this
    exact this.symm
  have hsz : σz 0 + σz 1 + σz 2 + σz 3 = 0 := by
    have := trace_eq_of_frame h hPc hzP
    rw [hztr, Matrix.trace_diagonal, Fin.sum_univ_four] at this
    exact this.symm
  have hsyz : σy 0 * σz 0 + σy 1 * σz 1 + σy 2 * σz 2 + σy 3 * σz 3 = 0 := by
    have hyzP : (y * z) * P = P * Matrix.diagonal (fun i => σy i * σz i) := by
      rw [Matrix.mul_assoc, hzP, ← Matrix.mul_assoc, hyP, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have := trace_eq_of_frame h hPc hyzP
    rw [hyztr, Matrix.trace_diagonal, Fin.sum_univ_four] at this
    exact this.symm
  have hd := pairs_distinct h2 hσy hσz hsy hsz hsyz
  obtain ⟨β, hBP⟩ := exists_B_diag h hPc hσy hσz hyP hzP hyB' hzB' hd
  have hβ := beta_norm h hBc hPc hBP
  obtain ⟨P', t, hP'c, ht, hyP', hzP', hBP'⟩ := rescale_frame hp hp2 hK hq h hPc hyP hzP hβ hBP
  have htp := prod_t_eq_neg_one h hP'c ht hmin hBP'
  obtain ⟨τ', εy, εz, ε, hτ'inj, hεy, hεz, hε, hτ'⟩ := sorted_cols h2 hσy hσz ht hsy hsz hsyz htp
  have hU : IsUnitaryU (p ^ f) (P'.submatrix id τ') :=
    GenLocU4ExtFrame.submatrix_unitary P' ((GenLocU4OutFrame.isUnitaryU_iff_cT h P').2 hP'c) τ' hτ'inj
  refine ⟨P'.submatrix id τ', εy, εz, hU, hεy, hεz, ?_, ?_, ?_⟩
  · rw [smul_tT]
    exact submatrix_diag hyP' τ' _ (fun k => (hτ' k).1)
  · rw [smul_tS]
    exact submatrix_diag hzP' τ' _ (fun k => (hτ' k).2.1)
  · have hmap : (P'.submatrix id τ').map (· ^ (p ^ f)) = (P'.map h.bar).submatrix id τ' := by
      rw [GenLocU4ExtFrame.map_bar_eq h, Matrix.submatrix_map]
    rw [hmap]
    have key := submatrix_diag hBP' τ' (fun k => ε * (![1, 1, 1, -1] : Fin 4 → K) k)
      (fun k => (hτ' k).2.2)
    rcases hε with rfl | rfl
    · left
      rw [key, ← smul_mD, one_smul]
    · right
      rw [key, ← smul_mD, neg_one_smul]

end GenLocU4OutFrDb

end CFSG.GH74.Generic.BProg.B2
