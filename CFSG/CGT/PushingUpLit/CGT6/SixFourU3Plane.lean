module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Wc
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Plane

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

@[expose] def blk01 (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1]

theorem blk01_one : blk01 (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk01]

theorem blk01_mul (X Y : Matrix (Fin 2) (Fin 2) F) : blk01 (X * Y) = blk01 X * blk01 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk01, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blk01_injective : Function.Injective (blk01 : Matrix (Fin 2) (Fin 2) F → _) := by
  intro X Y hXY
  ext i j
  have := congrFun (congrFun hXY i.castSucc) j.castSucc
  fin_cases i <;> fin_cases j <;> simpa [blk01] using this

theorem det_blk01 (X : Matrix (Fin 2) (Fin 2) F) : (blk01 X).det = X.det := by
  simp [blk01, Matrix.det_fin_three, Matrix.det_fin_two]

theorem blk01_map_transpose (X : Matrix (Fin 2) (Fin 2) F) :
    ((blk01 X).map h.bar)ᵀ = blk01 ((X.map h.bar)ᵀ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk01]

@[expose] def blkMon : Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 3) (Fin 3) F where
  toFun := blk01
  map_one' := blk01_one
  map_mul' := blk01_mul

theorem blkGL_mem (X : GL (Fin 2) F) (hX : X ∈ gramSU h (1 : Matrix (Fin 2) (Fin 2) F)) :
    Units.map (blkMon (F := F)) X ∈ unitarySU 2 s F 3 := by
  rw [mem_unitarySU_iff h]
  obtain ⟨hX1, hX2⟩ := hX
  refine ⟨?_, ?_⟩
  · show (blk01 (X : Matrix (Fin 2) (Fin 2) F)).det = 1
    rw [det_blk01]
    exact hX2
  · show ((blk01 (X : Matrix (Fin 2) (Fin 2) F)).map h.bar)ᵀ * blk01 (X : Matrix (Fin 2) (Fin 2) F) = 1
    rw [blk01_map_transpose h, ← blk01_mul]
    have : ((X : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * (X : Matrix (Fin 2) (Fin 2) F) = 1 := by
      simpa using hX1
    rw [this, blk01_one]

@[expose] noncomputable def blkHom :
    ↥(gramSU h (1 : Matrix (Fin 2) (Fin 2) F)) →* unitarySU 2 s F 3 :=
  ((Units.map (blkMon (F := F))).comp (gramSU h (1 : Matrix (Fin 2) (Fin 2) F)).subtype).codRestrict
    _ (fun X => blkGL_mem h X.1 X.2)

theorem coe_blkHom (X : ↥(gramSU h (1 : Matrix (Fin 2) (Fin 2) F))) :
    (((blkHom h X : unitarySU 2 s F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blk01 ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem blkHom_injective : Function.Injective (blkHom h) := by
  intro X Y hXY
  apply Subtype.ext
  apply Units.ext
  apply blk01_injective
  have := congrArg (fun g : unitarySU 2 s F 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hXY
  exact this

@[expose] noncomputable def Sig01 : Subgroup (unitarySU 2 s F 3) := (blkHom h).range

theorem card_gramSU_two : Nat.card ↥(gramSU h (1 : Matrix (Fin 2) (Fin 2) F)) =
    2 ^ s * ((2 ^ s) ^ 2 - 1) := by
  have hB : (gramForm h (1 : Matrix (Fin 2) (Fin 2) F)).IsSymm :=
    gramForm_isSymm h (by simp)
  have hBl : (gramForm h (1 : Matrix (Fin 2) (Fin 2) F)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hfin : Finite F := h.finite
  have := CFSG.LinearGroups.unitary_full_group_order h hB hBl
    (n := 2) (Module.finrank_fin_fun F) (by norm_num)
  have h2 := this.2.1
  rw [card_gramSU]
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, pow_one, Finset.Icc_self,
    Finset.prod_singleton] at h2
  have hq : 1 ≤ (2 ^ s) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have : (Nat.card ↥(sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) F))) : ℤ) =
      ((2 ^ s * ((2 ^ s) ^ 2 - 1) : ℕ) : ℤ) := by
    rw [h2]
    push_cast [Nat.cast_sub hq]
    ring
  exact_mod_cast this

theorem card_Sig01 : Nat.card ↥(Sig01 h) = 2 ^ s * ((2 ^ s) ^ 2 - 1) := by
  unfold Sig01
  rw [← card_gramSU_two h]
  exact (Nat.card_congr (MonoidHom.ofInjective (blkHom_injective h)).toEquiv).symm

theorem mem_Sig01 (g : unitarySU 2 s F 3) :
    g ∈ Sig01 h ↔ ∃ X : ↥(gramSU h (1 : Matrix (Fin 2) (Fin 2) F)),
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        blk01 ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hX.symm

theorem tvG_mem_Sig01 (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F) (hc : c + h.bar c = 0)
    (ha2 : a 2 = 0) : tvG h a ha c hc ∈ Sig01 h := by
  set Xm : Matrix (Fin 2) (Fin 2) F :=
    !![tvM h a c 0 0, tvM h a c 0 1; tvM h a c 1 0, tvM h a c 1 1] with hXm
  have hblk : blk01 Xm = tvM h a c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk01, hXm, tvM_apply, ha2]
  have hdet : Xm.det = 1 := by
    rw [← det_blk01, hblk, det_tvM, ha, mul_zero, add_zero]
  have hunit : (Xm.map h.bar)ᵀ * Xm = 1 := by
    apply blk01_injective
    rw [blk01_mul, ← blk01_map_transpose h, hblk, tvM_unitary h a ha c hc, blk01_one]
  let X : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero Xm (by rw [hdet]; exact one_ne_zero)
  have hX : X ∈ gramSU h (1 : Matrix (Fin 2) (Fin 2) F) := by
    refine ⟨?_, hdet⟩
    show (Xm.map h.bar)ᵀ * 1 * Xm = 1
    simpa using hunit
  rw [mem_Sig01]
  exact ⟨⟨X, hX⟩, hblk.symm⟩

theorem unitaryProj_injOn_Sig01 : Set.InjOn (unitaryProj h 3) (Sig01 h : Set (unitarySU 2 s F 3)) := by
  have key : ∀ σ ∈ Sig01 h, unitaryProj h 3 σ = 1 → σ = 1 := by
    intro σ hσ h1
    obtain ⟨X, hX⟩ := (mem_Sig01 h σ).mp hσ
    have hz : σ ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj, MonoidHom.mem_ker]
      exact h1
    obtain ⟨ζ, -, -, hζ⟩ := mem_unitaryScalars.mp hz
    have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hζ
    have e22 := congrFun (congrFun hmat 2) 2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e22
    rw [hX] at e22
    simp [blk01] at e22
    have hζ1 : ζ = 1 := Units.ext e22.symm
    apply Subtype.ext
    rw [hζ, hζ1, map_one]
    rfl
  intro x hx y hy hxy
  have : unitaryProj h 3 (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have := key _ ((Sig01 h).mul_mem ((Sig01 h).inv_mem hx) hy) this
  exact inv_mul_eq_one.mp this

theorem card_map_Sig01 :
    Nat.card ↥((Sig01 h).map (unitaryProj h 3)) = 2 ^ s * ((2 ^ s) ^ 2 - 1) := by
  rw [← card_Sig01 h]
  have hf : Function.Bijective ((unitaryProj h 3).subgroupMap (Sig01 h)) :=
    ⟨fun x y hxy => Subtype.ext (unitaryProj_injOn_Sig01 h x.2 y.2 (congrArg Subtype.val hxy)),
      MonoidHom.subgroupMap_surjective _ _⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hf)).symm

@[expose] def NO (x : F) : Prop := h.bar x * x = 1

theorem NO.ne_zero {x : F} (hx : NO h x) : x ≠ 0 := by
  rintro rfl
  simp [NO] at hx

theorem NO.mul {x y : F} (hx : NO h x) (hy : NO h y) : NO h (x * y) := by
  unfold NO at *
  rw [map_mul]
  linear_combination (h.bar y * y) * hx + hy

theorem NO.inv {x : F} (hx : NO h x) : NO h x⁻¹ := by
  unfold NO at *
  rw [map_inv₀, ← mul_inv, hx, inv_one]

@[expose] noncomputable def diagG (u v w : F) (hu : NO h u) (hv : NO h v) (hw : NO h w)
    (hdet : u * v * w = 1) : unitarySU 2 s F 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![u, v, w]) (by
      simp [Matrix.det_diagonal, Fin.prod_univ_three, hdet]),
    (mem_unitarySU_iff h).mpr ⟨by simp [Matrix.det_diagonal, Fin.prod_univ_three, hdet], by
      show ((Matrix.diagonal ![u, v, w]).map h.bar)ᵀ * Matrix.diagonal ![u, v, w] = 1
      rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> assumption⟩⟩

theorem coe_diagG (u v w : F) (hu : NO h u) (hv : NO h v) (hw : NO h w) (hdet : u * v * w = 1) :
    (((diagG h u v w hu hv hw hdet : unitarySU 2 s F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![u, v, w] := rfl

theorem diagG_comm_Sig01 (u w : F) (hu : NO h u) (hw : NO h w) (hdet : u * u * w = 1)
    (σ : unitarySU 2 s F 3) (hσ : σ ∈ Sig01 h) :
    diagG h u u w hu hu hw hdet * σ = σ * diagG h u u w hu hu hw hdet := by
  obtain ⟨X, hX⟩ := (mem_Sig01 h σ).mp hσ
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagG]
  rw [hX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk01, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem diagG_mem_Sig01 (u v : F) (hu : NO h u) (hv : NO h v) (huv : u * v = 1)
    (hdet : u * v * 1 = 1) (h1 : NO h (1 : F)) : diagG h u v 1 hu hv h1 hdet ∈ Sig01 h := by
  set Xm : Matrix (Fin 2) (Fin 2) F := Matrix.diagonal ![u, v] with hXm
  have hblk : blk01 Xm = Matrix.diagonal ![u, v, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk01, hXm]
  have hdetX : Xm.det = 1 := by
    simp [hXm, Matrix.det_diagonal, Fin.prod_univ_two, huv]
  let X : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero Xm (by rw [hdetX]; exact one_ne_zero)
  have hX : X ∈ gramSU h (1 : Matrix (Fin 2) (Fin 2) F) := by
    refine ⟨?_, hdetX⟩
    show (Xm.map h.bar)ᵀ * 1 * Xm = 1
    rw [Matrix.mul_one, hXm, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> assumption
  rw [mem_Sig01]
  exact ⟨⟨X, hX⟩, hblk.symm⟩

@[expose] def permP : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem permP_unitary : ((permP (F := F)).map h.bar)ᵀ * permP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permP, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_permP : (permP (F := F)).det = 1 := by
  simp [permP, Matrix.det_fin_three]

@[expose] noncomputable def PG : unitarySU 2 s F 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (permP (F := F)) (by rw [det_permP]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨det_permP, permP_unitary h⟩⟩

theorem coe_PG : (((PG h : unitarySU 2 s F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = permP :=
  rfl

theorem coe_PG_inv : ((((PG h : unitarySU 2 s F 3)⁻¹ : unitarySU 2 s F 3) : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = (permP (F := F))ᵀ := by
  show ((((PG h : unitarySU 2 s F 3) : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = _
  rw [Matrix.coe_units_inv, coe_PG]
  have : ((permP (F := F)).map h.bar)ᵀ = (permP (F := F))ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [permP]
  rw [← this]
  exact Matrix.inv_eq_left_inv (permP_unitary h)

theorem PG_inv_mul_diagG_mul_PG (u v w : F) (hu : NO h u) (hv : NO h v) (hw : NO h w)
    (hdet : u * v * w = 1) (hdet' : v * w * u = 1) :
    (PG h)⁻¹ * diagG h u v w hu hv hw hdet * PG h = diagG h v w u hv hw hu hdet' := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagG, coe_PG, coe_PG_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permP, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three]

theorem NO.zpow {h : UnitaryFieldData 2 s F} {κ : F} (hκ : NO h κ) (n : ℤ) : NO h (κ ^ n) := by
  unfold NO at *
  rw [map_zpow₀, ← mul_zpow, hκ, _root_.one_zpow]

@[expose] noncomputable def dg {κ : F} (hκ : NO h κ) (a b c : ℤ) (hs : a + b + c = 0) :
    unitarySU 2 s F 3 :=
  diagG h (κ ^ a) (κ ^ b) (κ ^ c) (hκ.zpow a) (hκ.zpow b) (hκ.zpow c)
    (by rw [← zpow_add₀ hκ.ne_zero, ← zpow_add₀ hκ.ne_zero, hs, zpow_zero])

theorem coe_dg {κ : F} (hκ : NO h κ) (a b c : ℤ) (hs : a + b + c = 0) :
    (((dg h hκ a b c hs : unitarySU 2 s F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![κ ^ a, κ ^ b, κ ^ c] := rfl

theorem dg_mul {κ : F} (hκ : NO h κ) (a b c a' b' c' : ℤ) (hs : a + b + c = 0)
    (hs' : a' + b' + c' = 0) :
    dg h hκ a b c hs * dg h hκ a' b' c' hs' =
      dg h hκ (a + a') (b + b') (c + c') (by omega) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_dg, Matrix.diagonal_mul_diagonal]
  ext i j
  have h0 := hκ.ne_zero
  fin_cases i <;> fin_cases j <;> simp [zpow_add₀ h0]

theorem dg_inv {κ : F} (hκ : NO h κ) (a b c : ℤ) (hs : a + b + c = 0) :
    (dg h hκ a b c hs)⁻¹ = dg h hκ (-a) (-b) (-c) (by omega) := by
  rw [inv_eq_iff_mul_eq_one, dg_mul]
  apply Subtype.ext
  apply Units.ext
  simp only [add_neg_cancel, coe_dg, zpow_zero, Subgroup.coe_one, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem PG_inv_dg_PG {κ : F} (hκ : NO h κ) (a b c : ℤ) (hs : a + b + c = 0) :
    (PG h)⁻¹ * dg h hκ a b c hs * PG h = dg h hκ b c a (by omega) :=
  PG_inv_mul_diagG_mul_PG h _ _ _ _ _ _ _ _

theorem dg_comm_Sig01 {κ : F} (hκ : NO h κ) (a c : ℤ) (hs : a + a + c = 0) (σ : unitarySU 2 s F 3)
    (hσ : σ ∈ Sig01 h) : dg h hκ a a c hs * σ = σ * dg h hκ a a c hs :=
  diagG_comm_Sig01 h _ _ _ _ _ σ hσ

theorem dg_mem_Sig01 {κ : F} (hκ : NO h κ) (a : ℤ) :
    dg h hκ a (-a) 0 (by omega) ∈ Sig01 h := by
  have h0 := hκ.ne_zero
  have := diagG_mem_Sig01 h (κ ^ a) (κ ^ (-a)) (hκ.zpow a) (hκ.zpow (-a))
    (by rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero])
    (by rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero, mul_one]) (by simp [NO])
  convert this using 1
  unfold dg
  congr
  simp

theorem dg_pow_orderdvd {κ : F} (hκ : NO h κ) (n : ℕ) (hn : κ ^ n = 1) (a b c : ℤ)
    (hs : a + b + c = 0) : dg h hκ a b c hs ^ n = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_dg, Matrix.diagonal_pow,
    Subgroup.coe_one, Units.val_one]
  have e : ∀ k : ℤ, (κ ^ k) ^ n = 1 := fun k => by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hn,
      _root_.one_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e]

theorem dg_not_mem_scalars {κ : F} (hκ : NO h κ) (a b c : ℤ) (hs : a + b + c = 0)
    (hab : κ ^ a ≠ κ ^ b) : dg h hκ a b c hs ∉ unitaryScalars h 3 := by
  intro hz
  obtain ⟨ζ, -, -, hζ⟩ := mem_unitaryScalars.mp hz
  have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hζ
  have e00 := congrFun (congrFun hmat 0) 0
  have e11 := congrFun (congrFun hmat 1) 1
  simp [coe_dg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e00 e11
  exact hab (e00.trans e11.symm)

theorem TGsub_le_Sig01 (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (ha2 : a 2 = 0) :
    TGsub h a ha ≤ Sig01 h := by
  intro g hg
  obtain ⟨c, hc, hmat⟩ := hg
  rw [tvG_eq_of_matrix h a ha c hc g hmat]
  exact tvG_mem_Sig01 h a ha c hc ha2

@[expose] def b₀ (ω : F) : Fin 3 → F := ![1, ω, 0]

theorem sqNorm3_b₀ {ω : F} (hω : NO h ω) : sqNorm3 h (b₀ ω) = 0 := by
  have h2 := two_eq_zero_of_h h
  have hω' : h.bar ω * ω = 1 := hω
  simp [sqNorm3, b₀, Fin.sum_univ_three]
  linear_combination hω' + h2

theorem map_TGsub_b₀_ne {ω : F} (hω : NO h ω) (hω1 : ω ≠ 1) :
    (TGsub h (b₀ ω) (sqNorm3_b₀ h hω)).map (unitaryProj h 3) ≠
      (TGsub h (a₀ : Fin 3 → F) (sqNorm3_a₀ h)).map (unitaryProj h 3) := by
  intro heq
  obtain ⟨c₁, hc₁E, hc₁ne⟩ := h.exists_mem_traceZero_ne_zero
  have hc₁ : c₁ + h.bar c₁ = 0 := (h.mem_traceZero).mp hc₁E
  have hmem : unitaryProj h 3 (tvG h (b₀ ω) (sqNorm3_b₀ h hω) c₁ hc₁) ∈
      (TGsub h (a₀ : Fin 3 → F) (sqNorm3_a₀ h)).map (unitaryProj h 3) := by
    rw [← heq]
    exact Subgroup.mem_map_of_mem _ (tvG_mem_TGsub h _ _ c₁ hc₁)
  obtain ⟨g', ⟨c', hc', hmat'⟩, hg'⟩ := Subgroup.mem_map.mp hmem
  have hz : g'⁻¹ * tvG h (b₀ ω) (sqNorm3_b₀ h hω) c₁ hc₁ ∈ unitaryScalars h 3 :=
    QuotientGroup.eq.mp hg'
  obtain ⟨ζ, -, -, hζ⟩ := mem_unitaryScalars.mp hz
  have e1 : ((tvG h (b₀ ω) (sqNorm3_b₀ h hω) c₁ hc₁ : unitarySU 2 s F 3) : GL (Fin 3) F) =
      (g' : GL (Fin 3) F) * (((g'⁻¹ * tvG h (b₀ ω) (sqNorm3_b₀ h hω) c₁ hc₁ : unitarySU 2 s F 3)) :
        GL (Fin 3) F) := by
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  rw [hζ] at e1
  have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) e1
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hmat', coe_tvG] at hmat
  have e22 := congrFun (congrFun hmat 2) 2
  have e00 := congrFun (congrFun hmat 0) 0
  have e01 := congrFun (congrFun hmat 0) 1
  simp [tvM_apply, a₀, b₀, Matrix.mul_apply, Matrix.diagonal_apply] at e22 e00 e01
  have hz1 : (ζ : F) = 1 := e22.symm
  rw [hz1] at e00 e01
  have hcc : c₁ = c' := by linear_combination e00
  have h5 : c₁ * h.bar ω = c₁ * 1 := by rw [e01, ← hcc]
  have hb : h.bar ω = 1 := mul_left_cancel₀ hc₁ne h5
  apply hω1
  apply h.bar.injective
  rw [hb, map_one]

end Plane

end CFSG.CGT.PushingUpLit.CGT6
