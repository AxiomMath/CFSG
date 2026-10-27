module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryPiecesSU

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear
  commute_blockSpecialLinear_of_disjoint)

section Theta

variable {p f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
  {C : Matrix (Fin n) (Fin n) F}

theorem uPieceTheta_det (hCC : C * C = 1) (x : SpecialLinearGroup (Fin n) F) :
    (C * ((((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map h.bar)ᵀ *
      C).det = 1 := by
  have h1 : ((((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map
      h.bar).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, (x⁻¹).2, map_one]
  rw [det_mul, det_mul, det_transpose, h1, mul_one, ← det_mul, hCC, det_one]

@[expose] noncomputable def uPieceTheta (hCC : C * C = 1) :
    SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F where
  toFun x := ⟨C * ((((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map
      h.bar)ᵀ * C, uPieceTheta_det h hCC x⟩
  map_one' := by
    apply Subtype.ext
    simp only [inv_one, Matrix.SpecialLinearGroup.coe_one,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, Matrix.mul_one, hCC]
  map_mul' x y := by
    apply Subtype.ext
    have hCC' : ∀ Z : Matrix (Fin n) (Fin n) F, C * (C * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
    refine Eq.trans ?_ (Matrix.SpecialLinearGroup.coe_mul _ _).symm
    dsimp only
    simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul, transpose_mul,
      Matrix.mul_assoc, hCC']

theorem coe_uPieceTheta (hCC : C * C = 1) (x : SpecialLinearGroup (Fin n) F) :
    ((uPieceTheta h hCC x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      C * ((((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map h.bar)ᵀ * C :=
  rfl

theorem uPieceTheta_eq_self_iff (hCC : C * C = 1) (x : SpecialLinearGroup (Fin n) F) :
    uPieceTheta h hCC x = x ↔
      (((x : Matrix (Fin n) (Fin n) F)).map h.bar)ᵀ * C * (x : Matrix (Fin n) (Fin n) F) = C := by
  have hXX' : (x : Matrix (Fin n) (Fin n) F).map h.bar *
      ((((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map h.bar) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hX'X : ((((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map h.bar) *
      (x : Matrix (Fin n) (Fin n) F).map h.bar = 1 := by
    rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  set X := (x : Matrix (Fin n) (Fin n) F)
  set Xb := X.map h.bar
  set X'b := (((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)).map h.bar
  have ht1 : Xbᵀ * X'bᵀ = 1 := by rw [← transpose_mul, hX'X, transpose_one]
  have ht2 : X'bᵀ * Xbᵀ = 1 := by rw [← transpose_mul, hXX', transpose_one]
  constructor
  · intro hθ
    have hθ' : C * X'bᵀ * C = X := congrArg
      (fun y : SpecialLinearGroup (Fin n) F => (y : Matrix (Fin n) (Fin n) F)) hθ
    calc Xbᵀ * C * X = Xbᵀ * C * (C * X'bᵀ * C) := by rw [hθ']
      _ = Xbᵀ * (C * C) * X'bᵀ * C := by simp only [Matrix.mul_assoc]
      _ = C := by rw [hCC, Matrix.mul_one, ht1, Matrix.one_mul]
  · intro hu
    apply Subtype.ext
    rw [coe_uPieceTheta]
    have h1 : C * X = X'bᵀ * C := by
      calc C * X = X'bᵀ * Xbᵀ * C * X := by rw [ht2, Matrix.one_mul]
        _ = X'bᵀ * (Xbᵀ * C * X) := by simp only [Matrix.mul_assoc]
        _ = X'bᵀ * C := by rw [hu]
    calc C * X'bᵀ * C = C * (X'bᵀ * C) := Matrix.mul_assoc _ _ _
      _ = C * (C * X) := by rw [h1]
      _ = X := by rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]

theorem mem_range_gramSUToSL_iff_uPieceTheta (hCC : C * C = 1)
    (x : SpecialLinearGroup (Fin n) F) :
    x ∈ (gramSUToSL h C).range ↔ uPieceTheta h hCC x = x := by
  rw [uPieceTheta_eq_self_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2.1
  · intro hx
    exact ⟨⟨SpecialLinearGroup.toGL x, hx, x.2⟩, rfl⟩

theorem uPieceTheta_uPieceTheta (hCC : C * C = 1) (hCt : Cᵀ = C) (hCb : C.map h.bar = C)
    (x : SpecialLinearGroup (Fin n) F) : uPieceTheta h hCC (uPieceTheta h hCC x) = x := by
  apply Subtype.ext
  have hbb : ∀ X : Matrix (Fin n) (Fin n) F, (X.map h.bar).map h.bar = X := fun X => by
    ext i j
    simp [UnitaryFieldData.bar_bar]
  rw [coe_uPieceTheta, ← map_inv, coe_uPieceTheta, inv_inv, Matrix.map_mul, Matrix.map_mul, hCb,
    ← transpose_map, hbb, transpose_mul, transpose_mul, transpose_transpose, hCt]
  calc C * (C * ((x : Matrix (Fin n) (Fin n) F) * C)) * C =
      (C * C) * (x : Matrix (Fin n) (Fin n) F) * (C * C) := by simp only [Matrix.mul_assoc]
    _ = (x : Matrix (Fin n) (Fin n) F) := by rw [hCC, Matrix.one_mul, Matrix.mul_one]

end Theta

section TwoBlocks

variable {n : ℕ} {F : Type} [Field F] {E E' : Finset (Fin n)}

theorem uPiece_exists_mul_of_mem_sup (hd : Disjoint E E') {x : SpecialLinearGroup (Fin n) F}
    (hx : x ∈ blockSpecialLinear (K := F) E ⊔ blockSpecialLinear E') :
    ∃ a ∈ blockSpecialLinear (K := F) E, ∃ b ∈ blockSpecialLinear (K := F) E', x = a * b := by
  have hcomm : ∀ (a : blockSpecialLinear (K := F) E) (b : blockSpecialLinear (K := F) E'),
      Commute ((blockSpecialLinear (K := F) E).subtype a)
        ((blockSpecialLinear (K := F) E').subtype b) :=
    fun a b => commute_blockSpecialLinear_of_disjoint hd a.2 b.2
  rw [← range_subtype (blockSpecialLinear (K := F) E),
    ← range_subtype (blockSpecialLinear (K := F) E'),
    ← MonoidHom.noncommCoprod_range _ _ hcomm] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem uPiece_eq_of_mul_eq_mul (hd : Disjoint E E') {a a' b b' : SpecialLinearGroup (Fin n) F}
    (ha : a ∈ blockSpecialLinear (K := F) E) (ha' : a' ∈ blockSpecialLinear (K := F) E)
    (hb : b ∈ blockSpecialLinear (K := F) E') (hb' : b' ∈ blockSpecialLinear (K := F) E')
    (hab : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ blockSpecialLinear (K := F) E ⊓ blockSpecialLinear E' :=
    mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [blockSpecialLinear_inf_eq_bot_of_disjoint hd, mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at hab
  exact mul_left_cancel hab

end TwoBlocks

section Piece

variable {p f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
  {C : Matrix (Fin n) (Fin n) F} {π : Fin n → Fin n}

theorem uPieceTheta_mem_blockSpecialLinear (hC : IsPermGram C π) {E E' : Finset (Fin n)}
    (hEE' : ∀ i, i ∈ E' ↔ π i ∈ E) {a : SpecialLinearGroup (Fin n) F}
    (ha : a ∈ blockSpecialLinear (K := F) E) :
    uPieceTheta h hC.mul_self a ∈ blockSpecialLinear (K := F) E' := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  have hinv := mem_blockSpecialLinear.mp (inv_mem ha) (π j) (π i)
    (hij.elim (fun hi => Or.inr ((not_congr (hEE' i)).mp hi))
      (fun hj => Or.inl ((not_congr (hEE' j)).mp hj)))
  rw [coe_uPieceTheta, hC.conj_apply, transpose_apply, map_apply, hinv]
  by_cases hij' : i = j
  · subst hij'
    rw [one_apply_eq, one_apply_eq, map_one]
  · rw [one_apply_ne (fun h' => hij' (hC.invol.injective h').symm), map_zero, one_apply_ne hij']

variable {E E' : Finset (Fin n)}

@[expose] noncomputable def uPiecePsi (hC : IsPermGram C π) (hd : Disjoint E E')
    (hE : ∀ i, i ∈ E' ↔ π i ∈ E) :
    blockSpecialLinear (K := F) E →* SpecialLinearGroup (Fin n) F where
  toFun a := (a : SpecialLinearGroup (Fin n) F) * uPieceTheta h hC.mul_self a
  map_one' := by simp
  map_mul' a b := by
    have hcomm : Commute (b : SpecialLinearGroup (Fin n) F) (uPieceTheta h hC.mul_self a) :=
      commute_blockSpecialLinear_of_disjoint hd b.2
        (uPieceTheta_mem_blockSpecialLinear h hC hE a.2)
    simp only [Subgroup.coe_mul, map_mul]
    rw [mul_assoc, ← mul_assoc (b : SpecialLinearGroup (Fin n) F), hcomm.eq]
    simp only [mul_assoc]

variable (hC : IsPermGram C π) (hd : Disjoint E E') (hE : ∀ i, i ∈ E' ↔ π i ∈ E)

theorem uPiecePsi_apply (a : blockSpecialLinear (K := F) E) :
    uPiecePsi h hC hd hE a = (a : SpecialLinearGroup (Fin n) F) * uPieceTheta h hC.mul_self a :=
  rfl

theorem uPiecePsi_injective : Function.Injective (uPiecePsi h hC hd hE) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [uPiecePsi_apply] at ha
  have h1 : (a : SpecialLinearGroup (Fin n) F) = (uPieceTheta h hC.mul_self a)⁻¹ :=
    eq_inv_of_mul_eq_one_left ha
  have h2 : (a : SpecialLinearGroup (Fin n) F) ∈
      blockSpecialLinear (K := F) E ⊓ blockSpecialLinear E' :=
    mem_inf.mpr ⟨a.2, h1 ▸ inv_mem (uPieceTheta_mem_blockSpecialLinear h hC hE a.2)⟩
  rw [blockSpecialLinear_inf_eq_bot_of_disjoint hd, mem_bot] at h2
  exact Subtype.ext h2

theorem range_inf_sup_eq_range_uPiecePsi (hE' : ∀ i, i ∈ E ↔ π i ∈ E') :
    (gramSUToSL h C).range ⊓ (blockSpecialLinear (K := F) E ⊔ blockSpecialLinear E') =
      (uPiecePsi h hC hd hE).range := by
  have hθθ := uPieceTheta_uPieceTheta h hC.mul_self hC.transpose_eq (hC.map_eq h.bar)
  apply le_antisymm
  · intro x hx
    obtain ⟨hxj, hxB⟩ := mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := uPiece_exists_mul_of_mem_sup hd hxB
    rw [mem_range_gramSUToSL_iff_uPieceTheta h hC.mul_self, map_mul] at hxj
    have hθa := uPieceTheta_mem_blockSpecialLinear h hC hE ha
    have hθb := uPieceTheta_mem_blockSpecialLinear h hC hE' hb
    have hcomm := commute_blockSpecialLinear_of_disjoint hd hθb hθa
    rw [← hcomm.eq] at hxj
    obtain ⟨-, hb'⟩ := uPiece_eq_of_mul_eq_mul hd hθb ha hθa hb hxj
    exact ⟨⟨a, ha⟩, by rw [uPiecePsi_apply, hb']⟩
  · rintro _ ⟨a, rfl⟩
    have hθa := uPieceTheta_mem_blockSpecialLinear h hC hE a.2
    refine mem_inf.mpr ⟨?_, mul_mem (mem_sup_left a.2) (mem_sup_right hθa)⟩
    rw [mem_range_gramSUToSL_iff_uPieceTheta h hC.mul_self, uPiecePsi_apply,
      map_mul, hθθ]
    exact (commute_blockSpecialLinear_of_disjoint hd a.2 hθa).eq.symm

include hC hd hE in
theorem natCard_range_inf_sup (hE' : ∀ i, i ∈ E ↔ π i ∈ E') :
    Nat.card ((gramSUToSL h C).range ⊓ (blockSpecialLinear (K := F) E ⊔ blockSpecialLinear E') :
      Subgroup _) = Nat.card (blockSpecialLinear (K := F) E) := by
  rw [range_inf_sup_eq_range_uPiecePsi h hC hd hE hE']
  exact (Nat.card_congr (MonoidHom.ofInjective (uPiecePsi_injective h hC hd hE)).toEquiv).symm

include hC hd hE in
theorem commutator_range_inf_sup (hE' : ∀ i, i ∈ E ↔ π i ∈ E')
    (hperf : ⁅blockSpecialLinear (K := F) E, blockSpecialLinear (K := F) E⁆ =
      blockSpecialLinear E) :
    ⁅(gramSUToSL h C).range ⊓ (blockSpecialLinear (K := F) E ⊔ blockSpecialLinear E'),
      (gramSUToSL h C).range ⊓ (blockSpecialLinear (K := F) E ⊔ blockSpecialLinear E')⁆ =
        (gramSUToSL h C).range ⊓ (blockSpecialLinear (K := F) E ⊔ blockSpecialLinear E') := by
  rw [range_inf_sup_eq_range_uPiecePsi h hC hd hE hE', ← isPerfect_iff]
  have : Group.IsPerfect (blockSpecialLinear (K := F) E) := isPerfect_iff.mpr hperf
  exact Group.IsPerfect.range _

end Piece

end CFSG.SeitzReduction.F4Pilot
