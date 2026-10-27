module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.Open

variable {ℓ f p n : ℕ} {K : Type} [Field K]

theorem commute_of_isDiag {x y : Matrix (Fin n) (Fin n) K} (hx : x.IsDiag) (hy : y.IsDiag) :
    x * y = y * x := by
  obtain ⟨d, rfl⟩ : ∃ d, x = diagonal d := ⟨_, hx.diagonal_diag.symm⟩
  obtain ⟨e, rfl⟩ : ∃ e, y = diagonal e := ⟨_, hy.diagonal_diag.symm⟩
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem isDiag_mul' {x y : Matrix (Fin n) (Fin n) K} (hx : x.IsDiag) (hy : y.IsDiag) :
    (x * y).IsDiag := by
  obtain ⟨d, rfl⟩ : ∃ d, x = diagonal d := ⟨_, hx.diagonal_diag.symm⟩
  obtain ⟨e, rfl⟩ : ∃ e, y = diagonal e := ⟨_, hy.diagonal_diag.symm⟩
  rw [Matrix.diagonal_mul_diagonal]
  exact Matrix.isDiag_diagonal _

@[expose] def diagP (ℓ f p n : ℕ) (K : Type) [Field K] : Subgroup (unitarySU ℓ f K n) where
  carrier := {x | ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧ x ^ p = 1}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · have := isDiag_mul' hx.1 hy.1
      simpa using this
    · have hc : Commute x y := Subtype.ext (Units.ext (commute_of_isDiag hx.1 hy.1))
      rw [hc.mul_pow, hx.2, hy.2, one_mul]
  one_mem' := ⟨by simpa using Matrix.isDiag_one, one_pow _⟩
  inv_mem' {x} hx := by
    refine ⟨?_, ?_⟩
    · have h1 : (((x⁻¹ : unitarySU ℓ f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := by
        simp [Matrix.coe_units_inv]
      obtain ⟨d, hd⟩ : ∃ d, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d :=
        ⟨_, hx.1.diagonal_diag.symm⟩
      rw [h1, hd, Matrix.inv_diagonal]
      exact Matrix.isDiag_diagonal _
    · rw [inv_pow, hx.2, inv_one]

theorem mem_diagP {x : unitarySU ℓ f K n} :
    x ∈ diagP ℓ f p n K ↔
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧ x ^ p = 1 :=
  Iff.rfl

theorem isDiag_entry_pow_eq_one {g : GL (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K).IsDiag) (hgp : g ^ p = 1) (j : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) j j ^ p = 1 := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
    ⟨_, hg.diagonal_diag.symm⟩
  have h1 : Matrix.diagonal (d ^ p) = (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.diagonal_pow, ← hd, ← Units.val_pow_eq_pow_val, hgp, Units.val_one]
  have h2 := congrFun (congrFun h1 j) j
  rw [hd, Matrix.diagonal_apply_eq]
  simpa using h2

theorem diagP_card_roots_le (hp : 0 < p) : Nat.card {a : K // a ^ p = 1} ≤ p := by
  classical
  calc Nat.card {a : K // a ^ p = 1}
      ≤ Nat.card {x : K // x ∈ Polynomial.nthRootsFinset p (1 : K)} :=
        Nat.card_le_card_of_injective
          (fun a => ⟨a.1, (Polynomial.mem_nthRootsFinset hp 1).mpr a.2⟩)
          (fun a b hab => by
            have h := congrArg Subtype.val hab
            exact Subtype.ext h)
    _ = (Polynomial.nthRootsFinset p (1 : K)).card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card (Polynomial.nthRoots p (1 : K)) := by
        rw [Polynomial.nthRootsFinset_def]
        exact Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

theorem gl_pow_eq_one_of_mem_diagP {x : unitarySU ℓ f K n} (hx : x ∈ diagP ℓ f p n K) :
    (x : GL (Fin n) K) ^ p = 1 := by
  rw [← Subgroup.coe_pow, (mem_diagP.mp hx).2, Subgroup.coe_one]

theorem ne_zero_of_pow_eq_one_of_pos {a : K} (hp : 0 < p) (ha : a ^ p = 1) : a ≠ 0 := by
  rintro rfl
  rw [zero_pow hp.ne'] at ha
  exact zero_ne_one ha

theorem eq_of_isDiag_det_one_gl {m : ℕ} {x y : GL (Fin (m + 1)) K}
    (hx : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K).IsDiag)
    (hy : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K).IsDiag)
    (hdx : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1)
    (hdy : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1)
    (hne : ∀ i : Fin m, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc i.castSucc ≠ 0)
    (hcast : ∀ i : Fin m, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc i.castSucc =
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc i.castSucc) : x = y := by
  obtain ⟨dx, hxd⟩ : ∃ d : Fin (m + 1) → K,
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = Matrix.diagonal d :=
    ⟨_, hx.diagonal_diag.symm⟩
  obtain ⟨dy, hyd⟩ : ∃ d : Fin (m + 1) → K,
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = Matrix.diagonal d :=
    ⟨_, hy.diagonal_diag.symm⟩
  have hcast' : ∀ i : Fin m, dx i.castSucc = dy i.castSucc := by
    intro i
    have h1 := hcast i
    rw [hxd, hyd, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
    exact h1
  have hP : ∏ i : Fin m, dx i.castSucc = ∏ i : Fin m, dy i.castSucc :=
    Finset.prod_congr rfl fun i _ => hcast' i
  have hx1 : (∏ i : Fin m, dx i.castSucc) * dx (Fin.last m) = 1 := by
    rw [← Fin.prod_univ_castSucc dx, ← Matrix.det_diagonal, ← hxd]
    exact hdx
  have hy1 : (∏ i : Fin m, dy i.castSucc) * dy (Fin.last m) = 1 := by
    rw [← Fin.prod_univ_castSucc dy, ← Matrix.det_diagonal, ← hyd]
    exact hdy
  have hne' : ∏ i : Fin m, dx i.castSucc ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have h1 := hne i
    rwa [hxd, Matrix.diagonal_apply_eq] at h1
  have hlast : dx (Fin.last m) = dy (Fin.last m) := by
    apply mul_left_cancel₀ hne'
    rw [hx1, hP, hy1]
  apply Units.ext
  rw [hxd, hyd]
  congr 1
  funext j
  induction j using Fin.lastCases with
  | last => exact hlast
  | cast i => exact hcast' i

theorem isDiag_units_inv_val {g : GL (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K).IsDiag) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
    ⟨_, hg.diagonal_diag.symm⟩
  rw [Matrix.coe_units_inv, hd, Matrix.inv_diagonal]
  exact Matrix.isDiag_diagonal _

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel in
theorem exists_diag_det_inv (h : UnitaryFieldData ℓ f K) (hn : 0 < n) {c : K}
    (hc : h.bar c * c = 1) :
    ∃ a : GL (Fin n) K, (a : Matrix (Fin n) (Fin n) K).IsDiag ∧
      (a : Matrix (Fin n) (Fin n) K).det = c⁻¹ ∧ a ∈ primeFormUnitary h (idGram K n) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K, d = fun j => if j = ⟨0, hn⟩ then c⁻¹ else 1 := ⟨_, rfl⟩
  have hdd : ∀ j, h.bar (d j) * d j = 1 := by
    intro j
    rw [hd]
    by_cases hj : j = ⟨0, hn⟩
    · simp only [if_pos hj, map_inv₀]
      rw [← mul_inv, hc, inv_one]
    · simp only [if_neg hj, map_one, mul_one]
  have hprod : ∏ j, d j = c⁻¹ := by
    rw [hd]
    simp
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal, hprod]
    exact inv_ne_zero hc0
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) hdet, ?_, ?_, ?_⟩
  · show (Matrix.diagonal d).IsDiag
    exact Matrix.isDiag_diagonal _
  · show (Matrix.diagonal d).det = c⁻¹
    rw [Matrix.det_diagonal, hprod]
  · rw [mem_primeFormUnitary]
    show ((Matrix.diagonal d).map h.bar)ᵀ * idGram K n * Matrix.diagonal d = idGram K n
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact hdd j

theorem card_diagP_le [Finite K] (hp : 0 < p) (hn : 1 ≤ n) :
    Nat.card (diagP ℓ f p n K) ≤ p ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let φ : diagP ℓ f p (m + 1) K → (Fin m → {a : K // a ^ p = 1}) := fun x i =>
    ⟨((x.1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc i.castSucc,
      isDiag_entry_pow_eq_one (mem_diagP.mp x.2).1 (gl_pow_eq_one_of_mem_diagP x.2) i.castSucc⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hcast : ∀ i : Fin m,
        ((x.1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc i.castSucc =
          ((y.1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc
            i.castSucc :=
      fun i => congrArg Subtype.val (congrFun hxy i)
    refine Subtype.ext (Subtype.ext (eq_of_isDiag_det_one_gl (mem_diagP.mp x.2).1
      (mem_diagP.mp y.2).1 ?_ ?_ ?_ hcast))
    · exact CFSG.Open.StatedAPI.det_of_mem_statedSU x.1.2
    · exact CFSG.Open.StatedAPI.det_of_mem_statedSU y.1.2
    · intro i
      exact ne_zero_of_pow_eq_one_of_pos hp (isDiag_entry_pow_eq_one (mem_diagP.mp x.2).1
        (gl_pow_eq_one_of_mem_diagP x.2) i.castSucc)
  calc Nat.card (diagP ℓ f p (m + 1) K) ≤ Nat.card (Fin m → {a : K // a ^ p = 1}) :=
        Nat.card_le_card_of_injective φ hinj
    _ = Nat.card {a : K // a ^ p = 1} ^ m := by
        rw [Nat.card_fun, Nat.card_fin]
    _ ≤ p ^ m := Nat.pow_le_pow_left (diagP_card_roots_le hp) m
    _ = p ^ (m + 1 - 1) := by rw [Nat.add_sub_cancel]

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel in
theorem exists_conj_le_diagP (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (B : Subgroup (unitarySU ℓ f K n)) (hB : IsElemAbelian p B) :
    ∃ P : unitarySU ℓ f K n, B ≤ (diagP ℓ f p n K).map (MulAut.conj P).toMonoidHom := by
  obtain ⟨hBcomm, hBpow⟩ := hB
  have hle : unitarySU ℓ f K n ≤ primeFormUnitary h (idGram K n) :=
    unitarySU_le_primeFormUnitary h
  have hcomm : ∀ x ∈ B.map (Subgroup.inclusion hle), ∀ y ∈ B.map (Subgroup.inclusion hle),
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext_iff.mp (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hpow : ∀ x ∈ B.map (Subgroup.inclusion hle), x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hBpow x hx, map_one]
  obtain ⟨P₀, hP₀⟩ := exists_unitary_conj_diag h hp hpq (B.map (Subgroup.inclusion hle))
    hcomm hpow
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) K,
      M = ((P₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, rfl⟩
  have hbar_det : ∀ N : Matrix (Fin n) (Fin n) K, (N.map h.bar).det = h.bar N.det := by
    intro N
    simpa using (RingHom.map_det h.bar N).symm
  have hPid : (M.map h.bar)ᵀ * M = 1 := by
    have h1 := mem_primeFormUnitary.mp P₀.2
    rw [hM]
    simpa [idGram] using h1
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = M.det := ⟨_, rfl⟩
  have hcbar : h.bar c * c = 1 := by
    have h1 := congrArg Matrix.det hPid
    rw [Matrix.det_mul, Matrix.det_transpose, hbar_det, Matrix.det_one, ← hcdef] at h1
    exact h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcbar
  obtain ⟨a, ha_diag, ha_det, ha_mem⟩ : ∃ a : GL (Fin n) K,
      (a : Matrix (Fin n) (Fin n) K).IsDiag ∧ (a : Matrix (Fin n) (Fin n) K).det = c⁻¹ ∧
        a ∈ primeFormUnitary h (idGram K n) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · have hempty : IsEmpty (Fin n) := by
        rw [hn0]
        infer_instance
      have hc1 : c = 1 := by
        rw [hcdef]
        exact Matrix.det_isEmpty
      refine ⟨1, Matrix.isDiag_one, ?_, one_mem _⟩
      simp [hc1]
    · exact exists_diag_det_inv h hn0 hcbar
  obtain ⟨P₁, hP₁def⟩ : ∃ P₁ : GL (Fin n) K, P₁ = (P₀ : GL (Fin n) K) * a := ⟨_, rfl⟩
  have hP₁mem : P₁ ∈ primeFormUnitary h (idGram K n) := by
    rw [hP₁def]
    exact mul_mem P₀.2 ha_mem
  have hP₁det : (P₁ : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [hP₁def, Units.val_mul, Matrix.det_mul, ha_det, ← hM, ← hcdef, mul_inv_cancel₀ hc0]
  have hP₁U : P₁ ∈ unitarySU ℓ f K n := by
    rw [mem_unitarySU_iff h]
    refine ⟨hP₁det, ?_⟩
    have h1 := mem_primeFormUnitary.mp hP₁mem
    simpa [idGram] using h1
  obtain ⟨Pu, hPu⟩ : ∃ Pu : unitarySU ℓ f K n, (Pu : GL (Fin n) K) = P₁ :=
    ⟨⟨P₁, hP₁U⟩, rfl⟩
  refine ⟨Pu, fun x hx => ?_⟩
  have hD := hP₀ (Subgroup.inclusion hle x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hdiag : (((Pu⁻¹ * x * Pu : unitarySU ℓ f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).IsDiag := by
    have heq : ((Pu⁻¹ * x * Pu : unitarySU ℓ f K n) : GL (Fin n) K) =
        (a⁻¹ : GL (Fin n) K) * ((P₀⁻¹ * Subgroup.inclusion hle x * P₀ :
          primeFormUnitary h (idGram K n)) : GL (Fin n) K) * a := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hPu, hP₁def,
        _root_.mul_inv_rev, mul_assoc]
    rw [heq, Units.val_mul, Units.val_mul]
    exact isDiag_mul' (isDiag_mul' (isDiag_units_inv_val ha_diag) hD) ha_diag
  have hpow' : (Pu⁻¹ * x * Pu) ^ p = 1 := by
    rw [show Pu⁻¹ * x * Pu = Pu⁻¹ * x * (Pu⁻¹)⁻¹ by rw [inv_inv], conj_pow, hBpow x hx,
      mul_one, mul_inv_cancel]
  refine Subgroup.mem_map.mpr ⟨Pu⁻¹ * x * Pu, mem_diagP.mpr ⟨hdiag, hpow'⟩, ?_⟩
  show Pu * (Pu⁻¹ * x * Pu) * Pu⁻¹ = x
  group

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
