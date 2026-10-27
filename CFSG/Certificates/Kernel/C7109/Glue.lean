module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.Certificates.Kernel.C7109.Sound
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

namespace CFSG.KC.C7109

open scoped Matrix

local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "G5" => GL (Fin 5) (ZMod 2)

theorem IsUni.isUpperTriangular {M : M5} (hM : IsUni M) : M.IsUpperTriangular :=
  fun i j h => hM.1 i j h

theorem isUni_one : IsUni (1 : M5) :=
  ⟨fun _ _ hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem IsUni.mul {M N : M5} (hM : IsUni M) (hN : IsUni N) : IsUni (M * N) := by
  refine ⟨fun i j hij => hM.isUpperTriangular.mul hN.isUpperTriangular hij, fun i => ?_⟩
  have h0 : ∀ k ∈ Finset.univ, k ≠ i → M i k * N k i = 0 := by
    intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hM.1 i k h, zero_mul]
    · rw [hN.1 k i h, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h), hM.2,
    hN.2, mul_one]

theorem IsUni.det {M : M5} (hM : IsUni M) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hM.isUpperTriangular]
  simp [hM.2]

theorem IsUni.det_ne_zero {M : M5} (hM : IsUni M) : M.det ≠ 0 := by
  rw [hM.det]
  exact one_ne_zero

namespace Glue

theorem isUni_pow {g : G5} (hg : IsUni (g : M5)) : ∀ k : ℕ, IsUni ((g ^ k : G5) : M5)
  | 0 => by rw [pow_zero, Units.val_one]; exact isUni_one
  | k + 1 => by rw [pow_succ, Units.val_mul]; exact (isUni_pow hg k).mul hg

@[expose] noncomputable def U5 : Subgroup G5 where
  carrier := {g | IsUni (g : M5)}
  mul_mem' := fun {a b} ha hb => by
    change IsUni ((a * b : G5) : M5)
    rw [Units.val_mul]
    exact ha.mul hb
  one_mem' := by
    change IsUni ((1 : G5) : M5)
    rw [Units.val_one]
    exact isUni_one
  inv_mem' := fun {g} hg => by
    have h1 : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    change IsUni ((g⁻¹ : G5) : M5)
    rw [h1]
    exact isUni_pow hg _

theorem mem_U5 {g : G5} : g ∈ U5 ↔ IsUni (g : M5) := Iff.rfl

@[expose] def uniOf (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) : M5 :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

theorem isUni_uniOf (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) : IsUni (uniOf f) := by
  refine ⟨fun i j hij => ?_, fun i => by simp [uniOf]⟩
  have h : j < i := hij
  simp [uniOf, (ne_of_lt h).symm, not_lt_of_gt h]

@[expose] noncomputable def uniGL (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) : G5 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uniOf f) (isUni_uniOf f).det_ne_zero

theorem coe_uniGL (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    (uniGL f : M5) = uniOf f :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem uniGL_mem (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) : uniGL f ∈ U5 := by
  rw [mem_U5, coe_uniGL]
  exact isUni_uniOf f

theorem card_U5 : Nat.card U5 = 2 ^ 10 := by
  let e : U5 ≃ ({p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :=
    { toFun := fun g p => (g.1 : M5) p.1.1 p.1.2
      invFun := fun f => ⟨uniGL f, uniGL_mem f⟩
      left_inv := fun g => by
        have hg : IsUni (g.1 : M5) := g.2
        refine Subtype.ext (Units.ext ?_)
        change (uniGL _ : M5) = _
        rw [coe_uniGL]
        ext i j
        simp only [uniOf, Matrix.of_apply]
        rcases lt_trichotomy i j with h | rfl | h
        · simp [ne_of_lt h, h]
        · simp [hg.2 i]
        · simp [(ne_of_lt h).symm, not_lt_of_gt h, hg.1 i j h]
      right_inv := fun f => by
        funext p
        change (uniGL f : M5) p.1.1 p.1.2 = f p
        rw [coe_uniGL]
        simp [uniOf, ne_of_lt p.2, p.2] }
  have h10 : Nat.card {p : Fin 5 × Fin 5 // p.1 < p.2} = 10 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, h10]

theorem card_GL5 : Nat.card G5 = 2 ^ 10 * 9765 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_five]

theorem exists_conj_le_U5 {S : Subgroup G5} (hS : IsPGroup 2 S) :
    ∃ h : G5, S.map (MulAut.conj h).toMonoidHom ≤ U5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 U5 := IsPGroup.of_card card_U5
  have hidx : ¬ 2 ∣ U5.index := by
    have h := Subgroup.card_mul_index U5
    rw [card_U5, card_GL5] at h
    have h1 : U5.index = 9765 := Nat.eq_of_mul_eq_mul_left (by norm_num) h
    rw [h1]
    decide
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G5 Q (hU.toSylow hidx)
  refine ⟨h, ?_⟩
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  have h1 : (MulAut.conj h).toMonoidHom s ∈ ((h • Q : Sylow 2 _) : Subgroup _) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨s, hQ hs, rfl⟩
  rw [hh, IsPGroup.toSylow_coe] at h1
  exact h1

@[expose] def fixV (S : Subgroup G5) : Set (Fin 5 → ZMod 2) :=
  {v | ∀ g ∈ S, (g : M5) *ᵥ v = v}

@[expose] def fixVT (S : Subgroup G5) : Set (Fin 5 → ZMod 2) :=
  {v | ∀ g ∈ S, (g : M5)ᵀ *ᵥ v = v}

theorem mulVec_inv_mulVec (h : G5) (v : Fin 5 → ZMod 2) :
    (↑h⁻¹ : M5) *ᵥ ((↑h : M5) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (h : G5) (v : Fin 5 → ZMod 2) :
    (↑h : M5) *ᵥ ((↑h⁻¹ : M5) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem tr_inv_mulVec (h : G5) (v : Fin 5 → ZMod 2) :
    (↑h⁻¹ : M5)ᵀ *ᵥ ((↑h : M5)ᵀ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]

theorem tr_mulVec_inv (h : G5) (v : Fin 5 → ZMod 2) :
    (↑h : M5)ᵀ *ᵥ ((↑h⁻¹ : M5)ᵀ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]

theorem conj_mulVec (h g : G5) (v : Fin 5 → ZMod 2) :
    (↑(MulAut.conj h g) : M5) *ᵥ ((↑h : M5) *ᵥ v) = (↑h : M5) *ᵥ ((↑g : M5) *ᵥ v) := by
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, mulVec_inv_mulVec]

theorem conjT_mulVec (h g : G5) (v : Fin 5 → ZMod 2) :
    (↑(MulAut.conj h g) : M5)ᵀ *ᵥ ((↑h⁻¹ : M5)ᵀ *ᵥ v) =
      (↑h⁻¹ : M5)ᵀ *ᵥ ((↑g : M5)ᵀ *ᵥ v) := by
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tr_mulVec_inv]

theorem fixV_conj (S : Subgroup G5) (h : G5) :
    fixV (S.map (MulAut.conj h).toMonoidHom) = (fun v => (↑h : M5) *ᵥ v) '' fixV S := by
  ext w
  constructor
  · intro hw
    refine ⟨(↑h⁻¹ : M5) *ᵥ w, fun g hg => ?_, mulVec_mulVec_inv h w⟩
    have h1 : (↑(MulAut.conj h g) : M5) *ᵥ w = w := hw _ (Subgroup.mem_map_of_mem _ hg)
    rw [← mulVec_mulVec_inv h w, conj_mulVec] at h1
    have h2 := congrArg ((↑h⁻¹ : M5) *ᵥ ·) h1
    simpa only [mulVec_inv_mulVec] using h2
  · rintro ⟨v, hv, rfl⟩ g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    change (↑(MulAut.conj h g) : M5) *ᵥ _ = _
    rw [conj_mulVec, hv g hg]

theorem fixVT_conj (S : Subgroup G5) (h : G5) :
    fixVT (S.map (MulAut.conj h).toMonoidHom) = (fun v => (↑h⁻¹ : M5)ᵀ *ᵥ v) '' fixVT S := by
  ext w
  constructor
  · intro hw
    refine ⟨(↑h : M5)ᵀ *ᵥ w, fun g hg => ?_, tr_inv_mulVec h w⟩
    have h1 : (↑(MulAut.conj h g) : M5)ᵀ *ᵥ w = w := hw _ (Subgroup.mem_map_of_mem _ hg)
    rw [← tr_inv_mulVec h w, conjT_mulVec] at h1
    have h2 := congrArg ((↑h : M5)ᵀ *ᵥ ·) h1
    simpa only [tr_mulVec_inv] using h2
  · rintro ⟨v, hv, rfl⟩ g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    change (↑(MulAut.conj h g) : M5)ᵀ *ᵥ _ = _
    rw [conjT_mulVec, hv g hg]

theorem card_fixV_conj (S : Subgroup G5) (h : G5) :
    Nat.card (fixV (S.map (MulAut.conj h).toMonoidHom)) = Nat.card (fixV S) := by
  rw [fixV_conj, Nat.card_image_of_injective]
  intro a b hab
  have := congrArg ((↑h⁻¹ : M5) *ᵥ ·) hab
  simpa only [mulVec_inv_mulVec] using this

theorem card_fixVT_conj (S : Subgroup G5) (h : G5) :
    Nat.card (fixVT (S.map (MulAut.conj h).toMonoidHom)) = Nat.card (fixVT S) := by
  rw [fixVT_conj, Nat.card_image_of_injective]
  intro a b hab
  have := congrArg ((↑h : M5)ᵀ *ᵥ ·) hab
  simpa only [tr_mulVec_inv] using this

theorem card_fixVT_eq_of_form {S : Subgroup G5} {P : M5} (hdet : P.det ≠ 0)
    (hP : ∀ g ∈ S, (↑g : M5) * P * (↑g : M5)ᵀ = P) :
    Nat.card (fixVT S) = Nat.card (fixV S) := by
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
  have hQv : ∀ v : Fin 5 → ZMod 2, P⁻¹ *ᵥ (P *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have h1 : ∀ g ∈ S, P * (↑g : M5)ᵀ = (↑g⁻¹ : M5) * P := by
    intro g hg
    calc _ = (↑g⁻¹ : M5) * ((↑g : M5) * P * (↑g : M5)ᵀ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, Matrix.one_mul]
      _ = (↑g⁻¹ : M5) * P := by rw [hP g hg]
  have hfix : ∀ g ∈ S, ∀ y : Fin 5 → ZMod 2,
      (↑g : M5)ᵀ *ᵥ y = y ↔ (↑g : M5) *ᵥ (P *ᵥ y) = P *ᵥ y := by
    intro g hg y
    have e : P *ᵥ ((↑g : M5)ᵀ *ᵥ y) = (↑g⁻¹ : M5) *ᵥ (P *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, h1 g hg, ← Matrix.mulVec_mulVec]
    constructor
    · intro hy
      rw [hy] at e
      calc _ = (↑g : M5) *ᵥ ((↑g⁻¹ : M5) *ᵥ (P *ᵥ y)) := by rw [← e]
        _ = P *ᵥ y := mulVec_mulVec_inv g _
    · intro hy
      have h2 : (↑g⁻¹ : M5) *ᵥ (P *ᵥ y) = P *ᵥ y := by
        calc _ = (↑g⁻¹ : M5) *ᵥ ((↑g : M5) *ᵥ (P *ᵥ y)) := by rw [hy]
          _ = P *ᵥ y := mulVec_inv_mulVec g _
      have h3 : P *ᵥ ((↑g : M5)ᵀ *ᵥ y) = P *ᵥ y := e.trans h2
      calc _ = P⁻¹ *ᵥ (P *ᵥ ((↑g : M5)ᵀ *ᵥ y)) := (hQv _).symm
        _ = P⁻¹ *ᵥ (P *ᵥ y) := by rw [h3]
        _ = y := hQv y
  have hz : ∀ z : Fin 5 → ZMod 2, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  have himg : fixV S = (fun y => P *ᵥ y) '' fixVT S := by
    ext z
    constructor
    · intro hz'
      refine ⟨P⁻¹ *ᵥ z, fun g hg => (hfix g hg _).mpr ?_, hz z⟩
      rw [hz]
      exact hz' g hg
    · rintro ⟨y, hy, rfl⟩ g hg
      exact (hfix g hg y).mp (hy g hg)
  rw [himg, Nat.card_image_of_injective]
  intro a b hab
  have hab' : P *ᵥ a = P *ᵥ b := hab
  calc a = P⁻¹ *ᵥ (P *ᵥ a) := (hQv a).symm
    _ = P⁻¹ *ᵥ (P *ᵥ b) := by rw [hab']
    _ = b := hQv b

theorem isPGroup_of_sq {S : Subgroup G5} (hsq : ∀ x ∈ S, x * x = 1) : IsPGroup 2 S :=
  fun g => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hsq _ g.2)⟩

theorem conj_props {S : Subgroup G5} (h : G5) (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) :
    (∀ x ∈ S.map (MulAut.conj h).toMonoidHom, ∀ y ∈ S.map (MulAut.conj h).toMonoidHom,
      x * y = y * x) ∧ (∀ x ∈ S.map (MulAut.conj h).toMonoidHom, x * x = 1) ∧
      Nat.card (S.map (MulAut.conj h).toMonoidHom) = Nat.card S := by
  refine ⟨?_, ?_, Subgroup.card_map_of_injective (MulAut.conj h).injective⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hsq x hx, map_one]

theorem subgroup_props {S : Subgroup G5} (K : Subgroup S)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) :
    (∀ x ∈ K.map S.subtype, ∀ y ∈ K.map S.subtype, x * y = y * x) ∧
      (∀ x ∈ K.map S.subtype, x * x = 1) ∧ Nat.card (K.map S.subtype) = Nat.card K :=
  ⟨fun x hx y hy => hcomm x (Subgroup.map_subtype_le K hx) y (Subgroup.map_subtype_le K hy),
    fun x hx => hsq x (Subgroup.map_subtype_le K hx),
    Subgroup.card_map_of_injective S.subtype_injective⟩

theorem exists_sub_card {S : Subgroup G5} (hsq : ∀ x ∈ S, x * x = 1) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card S) : ∃ K : Subgroup S, Nat.card K = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_of_sq hsq)
  have hkn : k ≤ n := by
    rw [hn] at hk
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hk
  exact Sylow.exists_subgroup_card_pow_prime 2 (by rw [hn]; exact pow_dvd_pow 2 hkn)

theorem large_of_U5
    (h7 : ∀ S : Subgroup G5, S ≤ U5 → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → Nat.card S ≠ 2 ^ 7)
    (h56 : ∀ S : Subgroup G5, S ≤ U5 → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → (Nat.card S = 2 ^ 5 ∨ Nat.card S = 2 ^ 6) →
      (Nat.card (fixV S) = 4 ∧ Nat.card (fixVT S) = 8) ∨
        (Nat.card (fixV S) = 8 ∧ Nat.card (fixVT S) = 4))
    {S : Subgroup G5} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1)
    (h32 : 2 ^ 5 ≤ Nat.card S) :
    (Nat.card (fixV S) = 4 ∧ Nat.card (fixVT S) = 8) ∨
      (Nat.card (fixV S) = 8 ∧ Nat.card (fixVT S) = 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := exists_conj_le_U5 (isPGroup_of_sq hsq)
  obtain ⟨hc', hs', hcard'⟩ := conj_props h hcomm hsq
  rw [← card_fixV_conj S h, ← card_fixVT_conj S h]
  set S' := S.map (MulAut.conj h).toMonoidHom with hS'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (isPGroup_of_sq hs')
  have hk7 : k < 7 := by
    by_contra hk7
    have h7le : 2 ^ 7 ≤ Nat.card S' := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨K, hK⟩ := exists_sub_card hs' h7le
    obtain ⟨hcK, hsK, hcardK⟩ := subgroup_props K hc' hs'
    exact h7 _ ((Subgroup.map_subtype_le K).trans hh) hcK hsK (hcardK.trans hK)
  have hk5 : 5 ≤ k := by
    rw [← hcard', hk] at h32
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h32
  refine h56 S' hh hc' hs' ?_
  rw [hk]
  rcases (show k = 5 ∨ k = 6 by omega) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem noForm_of_U5
    (h4 : ∀ S : Subgroup G5, S ≤ U5 → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → Nat.card S = 2 ^ 4 → ∀ P : M5, Pᵀ = P → P.det ≠ 0 →
      ∃ g ∈ S, (↑g : M5) * P * (↑g : M5)ᵀ ≠ P)
    {S : Subgroup G5} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1)
    (h16 : 2 ^ 4 ≤ Nat.card S) {P : M5} (hP : Pᵀ = P) (hdet : P.det ≠ 0) :
    ∃ g ∈ S, (↑g : M5) * P * (↑g : M5)ᵀ ≠ P := by
  by_contra hall
  push Not at hall
  obtain ⟨K, hK⟩ := exists_sub_card hsq h16
  obtain ⟨hcK, hsK, hcardK⟩ := subgroup_props K hcomm hsq
  set S₀ := K.map S.subtype with hS₀
  obtain ⟨h, hh⟩ := exists_conj_le_U5 (isPGroup_of_sq hsK)
  obtain ⟨hc', hs', hcard'⟩ := conj_props h hcK hsK
  set H : M5 := ↑h with hH
  set Hi : M5 := ↑h⁻¹ with hHi
  have h2 : Hi * H = 1 := by rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : Hᵀ * Hiᵀ = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  have hP'sym : (H * P * Hᵀ)ᵀ = H * P * Hᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hP,
      Matrix.mul_assoc]
  have hP'det : (H * P * Hᵀ).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hh1 := (Matrix.isUnit_iff_isUnit_det _).mp h.isUnit
    exact mul_ne_zero (mul_ne_zero hh1.ne_zero hdet) hh1.ne_zero
  obtain ⟨g', hg', hne⟩ := h4 _ hh hc' hs' (hcard'.trans (hcardK.trans hK)) _ hP'sym hP'det
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
  apply hne
  have h1 := hall g (Subgroup.map_subtype_le K hg)
  set G : M5 := ↑g with hG
  have e : (↑((MulAut.conj h).toMonoidHom g) : M5) = H * G * Hi := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul]
  rw [e, Matrix.transpose_mul, Matrix.transpose_mul]
  calc _ = H * G * (Hi * H) * P * (Hᵀ * Hiᵀ) * Gᵀ * Hᵀ := by simp only [Matrix.mul_assoc]
    _ = H * (G * P * Gᵀ) * Hᵀ := by
        rw [h2, h3, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = H * P * Hᵀ := by rw [h1]

open scoped Matrix in
theorem certificate_of_U5
    (h7 : ∀ S : Subgroup G5, S ≤ U5 → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → Nat.card S ≠ 2 ^ 7)
    (h56 : ∀ S : Subgroup G5, S ≤ U5 → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → (Nat.card S = 2 ^ 5 ∨ Nat.card S = 2 ^ 6) →
      (Nat.card (fixV S) = 4 ∧ Nat.card (fixVT S) = 8) ∨
        (Nat.card (fixV S) = 8 ∧ Nat.card (fixVT S) = 4))
    (h4 : ∀ S : Subgroup G5, S ≤ U5 → (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → Nat.card S = 2 ^ 4 → ∀ P : M5, Pᵀ = P → P.det ≠ 0 →
      ∃ g ∈ S, (↑g : M5) * P * (↑g : M5)ᵀ ≠ P) :

    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 5 ≤ Nat.card S →
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 4 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 8) ∨
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 8 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 4)) ∧
    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 4 ≤ Nat.card S →
      ∀ P : Matrix (Fin 5) (Fin 5) (ZMod 2), Pᵀ = P → P.det ≠ 0 →
      ∃ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * P *
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ ≠ P) :=
  ⟨fun _ hc hs h => large_of_U5 h7 h56 hc hs h,
    fun _ hc hs h _ hP hd => noForm_of_U5 h4 hc hs h hP hd⟩

structure TableOK (N : ℕ) (mat : ℕ → M5) (row : ℕ → ℕ → ℕ) : Prop where
  uni : ∀ i < N, IsUni (mat i)
  sq : ∀ i < N, mat i * mat i = 1
  ne_one : ∀ i < N, mat i ≠ 1
  compl : ∀ M : M5, IsUni M → M * M = 1 → M ≠ 1 → ∃ i < N, mat i = M
  prod : ∀ i < N, ∀ j < N, i ≠ j → mat i * mat j = mat j * mat i →
    row i j < N ∧ mat (row i j) = mat i * mat j

@[expose] def Closed (N : ℕ) (mat : ℕ → M5) (row : ℕ → ℕ → ℕ) (X : Finset ℕ) : Prop :=
  (∀ a ∈ X, a < N) ∧ ∀ a ∈ X, ∀ b ∈ X, a ≠ b → mat a * mat b = mat b * mat a ∧ row a b ∈ X

@[expose] def WalkFacts (N : ℕ) (mat : ℕ → M5) (row : ℕ → ℕ → ℕ) : Prop :=
  ∀ X : Finset ℕ, Closed N mat row X → ∃ m ≤ 6, X.card + 1 = 2 ^ m ∧
    ((m = 5 ∨ m = 6) →
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, mat i *ᵥ v = v} = 4 ∧
        Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, (mat i)ᵀ *ᵥ v = v} = 8) ∨
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, mat i *ᵥ v = v} = 8 ∧
        Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, (mat i)ᵀ *ᵥ v = v} = 4)) ∧
    (m = 4 → Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, mat i *ᵥ v = v} =
        Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, (mat i)ᵀ *ᵥ v = v} →
      ∀ P : M5, Pᵀ = P → P.det ≠ 0 → ∃ i ∈ X, mat i * P * (mat i)ᵀ ≠ P)

section Table

variable {N : ℕ} {mat : ℕ → M5} {row : ℕ → ℕ → ℕ}

theorem TableOK.inj (ht : TableOK N mat row) {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : mat i = mat j) : i = j := by
  by_contra hij
  have h1 := (ht.prod i hi j hj hij (by rw [h])).2
  rw [← h, ht.sq i hi] at h1
  exact ht.ne_one _ (ht.prod i hi j hj hij (by rw [h])).1 h1

open Classical in
@[expose] noncomputable def idxs (N : ℕ) (mat : ℕ → M5) (S : Subgroup G5) : Finset ℕ :=
  (Finset.range N).filter fun i => ∃ g ∈ S, (g : M5) = mat i

theorem mem_idxs {S : Subgroup G5} {i : ℕ} :
    i ∈ idxs N mat S ↔ i < N ∧ ∃ g ∈ S, (g : M5) = mat i := by
  simp [idxs]

theorem exists_idx (ht : TableOK N mat row) {S : Subgroup G5} (hSU : S ≤ U5)
    (hsq : ∀ x ∈ S, x * x = 1) {g : G5} (hg : g ∈ S) (hg1 : g ≠ 1) :
    ∃ i ∈ idxs N mat S, (g : M5) = mat i := by
  have hM1 : (g : M5) ≠ 1 := fun h => hg1 (Units.ext h)
  have hsqM : (g : M5) * (g : M5) = 1 := by
    rw [← Units.val_mul, hsq g hg, Units.val_one]
  obtain ⟨i, hi, hgi⟩ := ht.compl _ (hSU hg) hsqM hM1
  exact ⟨i, mem_idxs.mpr ⟨hi, g, hg, hgi.symm⟩, hgi.symm⟩

theorem closed_idxs (ht : TableOK N mat row) {S : Subgroup G5} (hSU : S ≤ U5)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) :
    Closed N mat row (idxs N mat S) := by
  refine ⟨fun a ha => (mem_idxs.mp ha).1, fun a ha b hb hab => ?_⟩
  obtain ⟨haN, ga, hga, hgae⟩ := mem_idxs.mp ha
  obtain ⟨hbN, gb, hgb, hgbe⟩ := mem_idxs.mp hb
  have hc : mat a * mat b = mat b * mat a := by
    rw [← hgae, ← hgbe, ← Units.val_mul, ← Units.val_mul, hcomm _ hga _ hgb]
  obtain ⟨hr, hre⟩ := ht.prod a haN b hbN hab hc
  refine ⟨hc, mem_idxs.mpr ⟨hr, ga * gb, S.mul_mem hga hgb, ?_⟩⟩
  rw [hre, Units.val_mul, hgae, hgbe]

theorem card_eq_idxs (ht : TableOK N mat row) {S : Subgroup G5} (hSU : S ≤ U5)
    (hsq : ∀ x ∈ S, x * x = 1) : Nat.card S = (idxs N mat S).card + 1 := by
  have hch : ∀ i : idxs N mat S, ∃ g ∈ S, (g : M5) = mat i := fun i => (mem_idxs.mp i.2).2
  let f : Option (idxs N mat S) → S := fun o => match o with
    | none => 1
    | some i => ⟨(hch i).choose, (hch i).choose_spec.1⟩
  have hval : ∀ i : idxs N mat S, (((f (some i)).1 : G5) : M5) = mat i :=
    fun i => (hch i).choose_spec.2
  have hone : ∀ i : idxs N mat S, f none ≠ f (some i) := by
    intro i h
    have h1 := congrArg (fun s : S => ((s.1 : G5) : M5)) h
    simp only [hval] at h1
    have h2 : ((1 : G5) : M5) = mat i := h1
    rw [Units.val_one] at h2
    exact ht.ne_one i (mem_idxs.mp i.2).1 h2.symm
  have hbij : Function.Bijective f := by
    constructor
    · rintro (_ | i) (_ | j) h
      · rfl
      · exact absurd h (hone j)
      · exact absurd h.symm (hone i)
      · have h1 := congrArg (fun s : S => ((s.1 : G5) : M5)) h
        simp only [hval] at h1
        exact congrArg some (Subtype.ext (ht.inj (mem_idxs.mp i.2).1 (mem_idxs.mp j.2).1 h1))
    · intro s
      by_cases hs : s = 1
      · exact ⟨none, hs.symm⟩
      · have hs1 : s.1 ≠ 1 := fun h => hs (Subtype.ext h)
        obtain ⟨i, hi, hsi⟩ := exists_idx ht hSU hsq s.2 hs1
        refine ⟨some ⟨i, hi⟩, Subtype.ext (Units.ext ?_)⟩
        rw [hval, hsi]
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_coe]

theorem fixV_eq_idxs (ht : TableOK N mat row) {S : Subgroup G5} (hSU : S ≤ U5)
    (hsq : ∀ x ∈ S, x * x = 1) :
    fixV S = {v : Fin 5 → ZMod 2 | ∀ i ∈ idxs N mat S, mat i *ᵥ v = v} := by
  ext v
  constructor
  · intro hv i hi
    obtain ⟨_, g, hg, hgi⟩ := mem_idxs.mp hi
    rw [← hgi]
    exact hv g hg
  · intro hv g hg
    by_cases hg1 : g = 1
    · rw [hg1, Units.val_one, Matrix.one_mulVec]
    · obtain ⟨i, hi, hgi⟩ := exists_idx ht hSU hsq hg hg1
      rw [hgi]
      exact hv i hi

theorem fixVT_eq_idxs (ht : TableOK N mat row) {S : Subgroup G5} (hSU : S ≤ U5)
    (hsq : ∀ x ∈ S, x * x = 1) :
    fixVT S = {v : Fin 5 → ZMod 2 | ∀ i ∈ idxs N mat S, (mat i)ᵀ *ᵥ v = v} := by
  ext v
  constructor
  · intro hv i hi
    obtain ⟨_, g, hg, hgi⟩ := mem_idxs.mp hi
    rw [← hgi]
    exact hv g hg
  · intro hv g hg
    by_cases hg1 : g = 1
    · rw [hg1, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
    · obtain ⟨i, hi, hgi⟩ := exists_idx ht hSU hsq hg hg1
      rw [hgi]
      exact hv i hi

open scoped Matrix in
theorem certificate_of_table (ht : TableOK N mat row) (hw : WalkFacts N mat row) :

    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 5 ≤ Nat.card S →
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 4 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 8) ∨
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 8 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 4)) ∧
    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 4 ≤ Nat.card S →
      ∀ P : Matrix (Fin 5) (Fin 5) (ZMod 2), Pᵀ = P → P.det ≠ 0 →
      ∃ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * P *
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ ≠ P) := by
  refine certificate_of_U5 (fun S hSU hc hs hcard => ?_) (fun S hSU hc hs hcard => ?_)
    (fun S hSU hc hs hcard P hP hdet => ?_)
  · obtain ⟨m, hm, hX, -, -⟩ := hw _ (closed_idxs ht hSU hc hs)
    rw [← card_eq_idxs ht hSU hs, hcard] at hX
    have h1 : 7 = m := Nat.pow_right_injective (le_refl 2) hX
    omega
  · obtain ⟨m, -, hX, h5, -⟩ := hw _ (closed_idxs ht hSU hc hs)
    rw [← card_eq_idxs ht hSU hs] at hX
    rw [fixV_eq_idxs ht hSU hs, fixVT_eq_idxs ht hSU hs]
    apply h5
    rcases hcard with h | h
    · rw [h] at hX
      exact Or.inl (Nat.pow_right_injective (le_refl 2) hX).symm
    · rw [h] at hX
      exact Or.inr (Nat.pow_right_injective (le_refl 2) hX).symm
  · by_contra hall
    push Not at hall
    obtain ⟨m, -, hX, -, h4⟩ := hw _ (closed_idxs ht hSU hc hs)
    rw [← card_eq_idxs ht hSU hs, hcard] at hX
    have hm4 : m = 4 := (Nat.pow_right_injective (le_refl 2) hX).symm
    have hD := card_fixVT_eq_of_form hdet hall
    rw [fixV_eq_idxs ht hSU hs, fixVT_eq_idxs ht hSU hs] at hD
    obtain ⟨i, hi, hne⟩ := h4 hm4 hD.symm P hP hdet
    obtain ⟨_, g, hg, hgi⟩ := mem_idxs.mp hi
    apply hne
    rw [← hgi]
    exact hall g hg

end Table

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem lane_lt (MT i : ℕ) : lane MT i < 2 ^ 25 := by
  have h : lane MT i = (MT >>> (25 * i)) &&& 33554431 := rfl
  rw [h]
  exact Nat.and_lt_two_pow _ (by norm_num)

theorem vdec_inj {a b : ℕ} (ha : a < 32) (hb : b < 32) (h : vdec a = vdec b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 5
  · have h1 := congrFun h ⟨i, hi⟩
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp [vdec, ha', hb'] at h1 ⊢
  · have h5 : 32 ≤ 2 ^ i :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h5),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h5)]

open Classical in
theorem card_vdec (P : (Fin 5 → ZMod 2) → Prop) :
    ((Finset.range 32).filter fun v => P (vdec v)).card = Nat.card {w | P w} := by
  have hinj : Set.InjOn vdec (Finset.range 32 : Set ℕ) := fun a ha b hb h =>
    vdec_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h
  have himg : (Finset.range 32).image vdec = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  have e : {w | P w} = ((Finset.univ.filter P : Finset _) : Set (Fin 5 → ZMod 2)) := by
    ext w
    simp
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset, ← himg, Finset.filter_image,
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

theorem pop32_eq_card {x : ℕ} (hx : x < 2 ^ 32) (P : (Fin 5 → ZMod 2) → Prop)
    (h : ∀ v < 32, x.testBit v = true ↔ P (vdec v)) : pop32 x = Nat.card {w | P w} := by
  classical
  rw [pop32_spec hx, ← card_vdec P]
  congr 1
  exact Finset.filter_congr fun v hv => h v (Finset.mem_range.mp hv)

variable {MT : ℕ} {RL : List ℕ}

theorem tableOK (hR : recsOK MT RL = true) (hC : complOK MT = true) :
    TableOK 191 (fun i => matOf (lane MT i)) (fun i j => rowAt (recAt RL i) j) := by
  obtain ⟨-, hr⟩ := recsOK_sound hR
  refine ⟨fun i hi => (hr i hi).2.2.1, fun i hi => (hr i hi).2.2.2.1,
    fun i hi => (hr i hi).2.2.2.2.1, fun M hu h2 h1 => complOK_sound hC M hu h2 h1,
    fun i hi j hj hij hc => ?_⟩
  have hj' := (hr i hi).2.2.2.2.2.2 j hj
  exact hj'.2.2 (hj'.2.1.mpr ⟨hij, hc⟩)

theorem walkFacts (hR : recsOK MT RL = true)
    (hW : walkP singMask 7 0 0 [] 4294967295 4294967295 [] RL = true) :
    WalkFacts 191 (fun i => matOf (lane MT i)) (fun i j => rowAt (recAt RL i) j) := by
  obtain ⟨-, hr⟩ := recsOK_sound hR
  unfold WalkFacts Closed
  intro X hXc
  obtain ⟨hX, hcl⟩ := hXc
  dsimp only at hcl ⊢
  obtain ⟨B, hBX, hcard, hlen, hnode⟩ := walk_sound hR hW X hX fun a ha b hb hab =>
    ⟨((hr a (hX a ha)).2.2.2.2.2.2 b (hX b hb)).2.1.mpr ⟨hab, (hcl a ha b hb hab).1⟩,
      (hcl a ha b hb hab).2⟩
  have hfix : pop32 (andMask rfix RL X) =
      Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, matOf (lane MT i) *ᵥ v = v} := by
    refine pop32_eq_card (andMask_lt _ _ _) _ fun v hv => ?_
    rw [testBit_andMask _ _ _ hv]
    constructor
    · intro h i hi
      exact ((hr i (hX i hi)).2.2.2.2.2.1 v hv).1.mp (h i hi (hX i hi))
    · intro h i hi hi'
      exact ((hr i hi').2.2.2.2.2.1 v hv).1.mpr (h i hi)
  have hfixT : pop32 (andMask rfixT RL X) =
      Nat.card {v : Fin 5 → ZMod 2 | ∀ i ∈ X, (matOf (lane MT i))ᵀ *ᵥ v = v} := by
    refine pop32_eq_card (andMask_lt _ _ _) _ fun v hv => ?_
    rw [testBit_andMask _ _ _ hv]
    constructor
    · intro h i hi
      exact ((hr i (hX i hi)).2.2.2.2.2.1 v hv).2.mp (h i hi (hX i hi))
    · intro h i hi hi'
      exact ((hr i hi').2.2.2.2.2.1 v hv).2.mpr (h i hi)
  obtain ⟨hn56, hn4⟩ := nodeOK_sound hnode
  refine ⟨B.length, hlen, hcard, fun hm => ?_, fun hm hc P hP hdet => ?_⟩
  · rw [← hfix, ← hfixT]
    exact hn56 hm
  · rw [← hfix, ← hfixT] at hc
    have hF := hn4 hm hc
    by_contra hall
    push Not at hall
    obtain ⟨p, hp, rfl⟩ := exists_symC P hP
    have hS := formOK_sound hF p hp fun r hr' => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
      rw [(hr b (hX b (hBX b hb))).2.1, ffG_spec (lane_lt MT b) hp]
      exact hall b (hBX b hb)
    obtain ⟨v, hv0, hv⟩ := singMask_spec hp hS
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hv⟩)

open scoped Matrix in
theorem certificate_of_checks (hR : recsOK MT RL = true) (hC : complOK MT = true)
    (hW : letB singMask (fun S => walkP S 7 0 0 [] 4294967295 4294967295 [] RL) = true) :

    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 5 ≤ Nat.card S →
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 4 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 8) ∨
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 8 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 4)) ∧
    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 4 ≤ Nat.card S →
      ∀ P : Matrix (Fin 5) (Fin 5) (ZMod 2), Pᵀ = P → P.det ≠ 0 →
      ∃ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * P *
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ ≠ P) :=
  certificate_of_table (tableOK hR hC) (walkFacts hR (by rwa [letB_eq] at hW))

end Glue

end CFSG.KC.C7109
