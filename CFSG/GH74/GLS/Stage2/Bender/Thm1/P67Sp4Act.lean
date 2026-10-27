module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

abbrev mx (g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  (g : Matrix _ _ K)

theorem spForm_gsp (A : gsp 2 K) (x y : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (mx (A : GL _ K) *ᵥ x) (mx (A : GL _ K) *ᵥ y) =
      ((multiplier 2 K A : Kˣ) : K) * spForm 2 K x y := by
  have h := multiplier_spec A
  rw [spForm, Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_comm,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  have h' : (mx (A : GL _ K))ᵀ * spGram 2 K * mx (A : GL _ K) =
      ((multiplier 2 K A : Kˣ) : K) • spGram 2 K := h
  rw [h', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem spForm_map (σ : K ≃+* K) (x y : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (⇑σ ∘ x) (⇑σ ∘ y) = σ (spForm 2 K x y) := by
  rw [spForm_apply, spForm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_sub, map_mul]

@[expose] def semi (A : gsp 2 K) (σ : K ≃+* K) (v : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  mx (A : GL _ K) *ᵥ (⇑σ ∘ v)

theorem semi_add (A : gsp 2 K) (σ : K ≃+* K) (v w : Fin 2 ⊕ Fin 2 → K) :
    semi A σ (v + w) = semi A σ v + semi A σ w := by
  unfold semi
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem semi_sub (A : gsp 2 K) (σ : K ≃+* K) (v w : Fin 2 ⊕ Fin 2 → K) :
    semi A σ (v - w) = semi A σ v - semi A σ w := by
  unfold semi
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp

theorem semi_smul (A : gsp 2 K) (σ : K ≃+* K) (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    semi A σ (c • v) = σ c • semi A σ v := by
  unfold semi
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem semi_zero (A : gsp 2 K) (σ : K ≃+* K) : semi A σ 0 = 0 := by
  unfold semi
  have : (⇑σ ∘ (0 : Fin 2 ⊕ Fin 2 → K)) = 0 := by
    funext i; simp
  rw [this, Matrix.mulVec_zero]

theorem spForm_semi (A : gsp 2 K) (σ : K ≃+* K) (v w : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (semi A σ v) (semi A σ w) =
      ((multiplier 2 K A : Kˣ) : K) * σ (spForm 2 K v w) := by
  unfold semi
  rw [spForm_gsp, spForm_map]

theorem exists_semi_eq (A : gsp 2 K) (σ : K ≃+* K) (v : Fin 2 ⊕ Fin 2 → K) :
    ∃ w, semi A σ w = v := by
  refine ⟨fun i => σ.symm ((mx ((A : GL _ K)⁻¹) *ᵥ v) i), ?_⟩
  unfold semi
  have : (⇑σ ∘ fun i => σ.symm ((mx ((A : GL _ K)⁻¹) *ᵥ v) i)) = mx ((A : GL _ K)⁻¹) *ᵥ v := by
    funext i; simp
  rw [this, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem semi_eq_zero_iff (A : gsp 2 K) (σ : K ≃+* K) (v : Fin 2 ⊕ Fin 2 → K) :
    semi A σ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : mx ((A : GL _ K)⁻¹) *ᵥ semi A σ v = ⇑σ ∘ v := by
      unfold semi
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at h1
    funext i
    have := congrFun h1 i
    simpa using this.symm
  · rintro rfl
    exact semi_zero A σ

@[expose] noncomputable def cf (A : gsp 2 K) (σ : K ≃+* K) : StatedSp 2 K →* StatedSp 2 K :=
  ((conjSp 2 K A) : StatedSp 2 K ≃* StatedSp 2 K).toMonoidHom.comp
    ((fieldSp 2 K σ) : StatedSp 2 K ≃* StatedSp 2 K).toMonoidHom

theorem coe_cf (A : gsp 2 K) (σ : K ≃+* K) (x : StatedSp 2 K) :
    mx ((cf A σ x : StatedSp 2 K) : GL _ K) =
      mx (A : GL _ K) * (mx (x : GL _ K)).map σ * mx ((A : GL _ K)⁻¹) := by
  change mx (((conjSp 2 K A) (fieldSp 2 K σ x) : StatedSp 2 K) : GL _ K) = _
  rw [coe_conjSp]
  simp only [mx, Units.val_mul]
  rw [coe_fieldSp]

theorem cf_mulVec_semi (A : gsp 2 K) (σ : K ≃+* K) (x : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    mx ((cf A σ x : StatedSp 2 K) : GL _ K) *ᵥ semi A σ v = semi A σ (mx (x : GL _ K) *ᵥ v) := by
  rw [coe_cf]
  unfold semi
  have h1 : mx ((A : GL _ K)⁻¹) *ᵥ (mx (A : GL _ K) *ᵥ (⇑σ ∘ v)) = ⇑σ ∘ v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : (mx (x : GL _ K)).map σ *ᵥ (⇑σ ∘ v) = ⇑σ ∘ (mx (x : GL _ K) *ᵥ v) := by
    funext i
    exact (RingHom.map_mulVec (σ : K →+* K) (mx (x : GL _ K)) v i).symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2]

theorem conjAut_fieldAut_proj (A : gsp 2 K) (σ : K ≃+* K) (x : StatedSp 2 K) :
    (conjAut 2 K A * fieldAut 2 K σ) (proj 2 K x) = proj 2 K (cf A σ x) := rfl

@[expose] noncomputable def tvS (a : Fin 2 ⊕ Fin 2 → K) (c : K) : StatedSp 2 K :=
  ⟨spTrans a c, spTrans_mem_statedSp a c⟩

theorem mx_tvS_mulVec (a : Fin 2 ⊕ Fin 2 → K) (c : K) (x : Fin 2 ⊕ Fin 2 → K) :
    mx ((tvS a c : StatedSp 2 K) : GL _ K) *ᵥ x = x + (c * spForm 2 K x a) • a :=
  spTrans_mulVec a c x

theorem cf_tvS (A : gsp 2 K) (σ : K ≃+* K) (a : Fin 2 ⊕ Fin 2 → K) (c : K) :
    cf A σ (tvS a c) = tvS (semi A σ a) (σ c / ((multiplier 2 K A : Kˣ) : K)) := by
  apply Subtype.ext
  apply gl_ext_mulVec
  intro v
  obtain ⟨w, rfl⟩ := exists_semi_eq A σ v
  have hμ : ((multiplier 2 K A : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [cf_mulVec_semi, mx_tvS_mulVec, mx_tvS_mulVec, semi_add, semi_smul, spForm_semi, map_mul]
  congr 2
  field_simp

theorem tvS_mulVec_eq_iff {a a' : Fin 2 ⊕ Fin 2 → K} {c c' : K}
    (h : tvS a' c' = tvS a c) (x : Fin 2 ⊕ Fin 2 → K) :
    (c' * spForm 2 K x a') • a' = (c * spForm 2 K x a) • a := by
  have := congrArg (fun g : StatedSp 2 K => mx (g : GL _ K) *ᵥ x) h
  simp only [mx_tvS_mulVec] at this
  simpa using this

theorem exists_spForm_ne_zero {a : Fin 2 ⊕ Fin 2 → K} (ha : a ≠ 0) :
    ∃ x, spForm 2 K x a ≠ 0 := by
  by_contra hcon
  apply ha
  apply spForm_separatingLeft
  intro y
  by_contra hy
  exact hcon ⟨y, fun h => hy (spForm_isRefl _ _ h)⟩

theorem exists_smul_of_tvS_eq {a a' : Fin 2 ⊕ Fin 2 → K} {c c' : K} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : tvS a' c' = tvS a c) : ∃ l : K, a' = l • a ∧ c' * l ^ 2 = c := by
  obtain ⟨x0, hx0⟩ := exists_spForm_ne_zero ha
  have h0 := tvS_mulVec_eq_iff h x0
  have hne : (c * spForm 2 K x0 a) • a ≠ 0 := smul_ne_zero (mul_ne_zero hc hx0) ha
  rw [← h0] at hne
  have hc'0 : c' ≠ 0 := fun h' => hne (by rw [h', zero_mul, zero_smul])
  have hx0' : spForm 2 K x0 a' ≠ 0 := fun h' => hne (by rw [h', mul_zero, zero_smul])
  have ht' : c' * spForm 2 K x0 a' ≠ 0 := mul_ne_zero hc'0 hx0'
  have hal : a' = ((c' * spForm 2 K x0 a')⁻¹ * (c * spForm 2 K x0 a)) • a := by
    have h5 : a' = ((c' * spForm 2 K x0 a')⁻¹ * (c' * spForm 2 K x0 a')) • a' := by
      rw [inv_mul_cancel₀ ht', one_smul]
    rw [mul_smul, h0, smul_smul] at h5
    exact h5
  refine ⟨(c' * spForm 2 K x0 a')⁻¹ * (c * spForm 2 K x0 a), hal, ?_⟩
  have h1 : spForm 2 K x0 a' = ((c' * spForm 2 K x0 a')⁻¹ * (c * spForm 2 K x0 a)) *
      spForm 2 K x0 a := by
    conv_lhs => rw [hal]
    rw [map_smul, smul_eq_mul]
  set t' := c' * spForm 2 K x0 a' with ht'def
  set l := t'⁻¹ * (c * spForm 2 K x0 a) with hl
  have h2 : t' = c' * (l * spForm 2 K x0 a) := by rw [ht'def, h1]
  have h3 : l * t' = c * spForm 2 K x0 a := by
    rw [hl, mul_comm t'⁻¹, mul_assoc, inv_mul_cancel₀ ht', mul_one]
  have h4 : c' * l ^ 2 * spForm 2 K x0 a = c * spForm 2 K x0 a := by
    rw [← h3, h2]; ring
  exact mul_right_cancel₀ hx0 h4

theorem eq_of_tvS_eq {a : Fin 2 ⊕ Fin 2 → K} {c d : K} (ha : a ≠ 0) (h : tvS a c = tvS a d) :
    c = d := by
  obtain ⟨x0, hx0⟩ := exists_spForm_ne_zero ha
  have h0 := tvS_mulVec_eq_iff h x0
  obtain ⟨y, hy⟩ : ∃ y, y ≠ 0 := ⟨a, ha⟩
  have h1 : (c * spForm 2 K x0 a) • a = (d * spForm 2 K x0 a) • a := h0
  have := smul_left_injective K ha h1
  exact mul_right_cancel₀ hx0 this

theorem scalar_eq_one {c : Kˣ} (h2 : GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = 1) : c = 1 := by
  have h3 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2))) h2
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h3
  simp at h3
  exact h3

theorem scalar_pow_eq_one_iff_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] (c : Kˣ) :
    c ^ p = 1 → c = 1 := by
  intro h
  have h1 : ((c : K) - 1) ^ p = 0 := by
    have := congrArg (fun u : Kˣ => (u : K)) h
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [sub_pow_char, this]
    simp
  have h2 : (c : K) - 1 = 0 := pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h1
  exact Units.ext (sub_eq_zero.mp h2)

theorem eq_of_proj_eq {p : ℕ} [Fact p.Prime] [CharP K p] {x y : StatedSp 2 K} (hx : x ^ p = 1)
    (hy : y ^ p = 1) (h : proj 2 K x = proj 2 K y) : x = y := by
  have h' : (QuotientGroup.mk x : StatedSp 2 K ⧸ spScalars 2 K) = QuotientGroup.mk y := h
  have hs := QuotientGroup.eq.mp h'
  rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hs
  obtain ⟨c, hc⟩ := hs
  set s : StatedSp 2 K := x⁻¹ * y with hsdef
  have hcomm : Commute x s := by
    apply Subtype.ext
    have hz : ((s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈
        Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, hc⟩
    exact (Subgroup.mem_center_iff.mp hz (x : GL _ K))
  have hy' : y = x * s := by rw [hsdef]; group
  have hs1 : s ^ p = 1 := by
    have : (x * s) ^ p = x ^ p * s ^ p := hcomm.mul_pow p
    rw [← hy', hy, hx, one_mul] at this
    exact this.symm
  have hc1 : c ^ p = 1 := by
    apply scalar_eq_one
    rw [map_pow, hc]
    exact congrArg Subtype.val hs1
  have hc1' := scalar_pow_eq_one_iff_of_charP c hc1
  have : s = 1 := by
    apply Subtype.ext
    rw [← hc, hc1', map_one]
    rfl
  rw [hy', this, mul_one]

theorem pow_char_tvS {p : ℕ} [Fact p.Prime] [CharP K p] (a : Fin 2 ⊕ Fin 2 → K) (c : K) :
    tvS a c ^ p = 1 := by
  apply Subtype.ext
  show spTrans a c ^ p = 1
  rw [spTrans_npow, CharP.cast_eq_zero, zero_mul, spTrans_zero]

theorem fix_tvS (A : gsp 2 K) (σ : K ≃+* K) {a : Fin 2 ⊕ Fin 2 → K} (ha : a ≠ 0) (F : Subfield K)
    (h : ∀ c ∈ F, cf A σ (tvS a c) = tvS a c) :
    ∃ l : K, semi A σ a = l • a ∧ l ^ 2 = ((multiplier 2 K A : Kˣ) : K) ∧ ∀ c ∈ F, σ c = c := by
  have hμ : ((multiplier 2 K A : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have h1 := h 1 F.one_mem
  rw [cf_tvS, map_one] at h1
  obtain ⟨l, hl, hl2⟩ := exists_smul_of_tvS_eq ha one_ne_zero h1
  have hl2' : l ^ 2 = ((multiplier 2 K A : Kˣ) : K) := by
    field_simp at hl2
    linear_combination hl2
  refine ⟨l, hl, hl2', fun c hc => ?_⟩
  have h2 := h c hc
  rw [cf_tvS, hl] at h2
  have h3 : tvS (l • a) (σ c / ((multiplier 2 K A : Kˣ) : K)) =
      tvS a (l ^ 2 * (σ c / ((multiplier 2 K A : Kˣ) : K))) :=
    Subtype.ext (spTrans_smul a l _)
  rw [h3] at h2
  have h4 := eq_of_tvS_eq ha h2
  rw [hl2'] at h4
  field_simp at h4
  exact h4

@[expose] noncomputable def epsMat (e w : Fin 2 ⊕ Fin 2 → K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  1 + vecMulVec w (spGram 2 K *ᵥ e) + vecMulVec e (spGram 2 K *ᵥ w)

theorem epsMat_mulVec (e w x : Fin 2 ⊕ Fin 2 → K) :
    epsMat e w *ᵥ x = x + spForm 2 K x e • w + spForm 2 K x w • e := by
  rw [epsMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, spForm_eq_dotProduct, spForm_eq_dotProduct,
    dotProduct_comm (spGram 2 K *ᵥ e) x, dotProduct_comm (spGram 2 K *ᵥ w) x]

theorem spForm_neg_left (x y : Fin 2 ⊕ Fin 2 → K) : spForm 2 K y x = - spForm 2 K x y := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt]

theorem epsMat_mul_neg {e w : Fin 2 ⊕ Fin 2 → K} (h : spForm 2 K e w = 0) :
    epsMat e w * epsMat e (-w) = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  have h' : spForm 2 K w e = 0 := by rw [spForm_neg_left, h, neg_zero]
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, epsMat_mulVec, map_add, map_smul,
    map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, spForm_self, h, h',
    smul_eq_mul, mul_zero, add_zero, Matrix.one_mulVec]
  module

@[expose] noncomputable def epsGL (e w : Fin 2 ⊕ Fin 2 → K) (h : spForm 2 K e w = 0) :
    GL (Fin 2 ⊕ Fin 2) K where
  val := epsMat e w
  inv := epsMat e (-w)
  val_inv := epsMat_mul_neg h
  inv_val := by
    have h2 : spForm 2 K e (-w) = 0 := by rw [map_neg, h, neg_zero]
    have := epsMat_mul_neg h2
    rwa [neg_neg] at this

theorem epsGL_mulVec (e w : Fin 2 ⊕ Fin 2 → K) (h : spForm 2 K e w = 0) (x : Fin 2 ⊕ Fin 2 → K) :
    mx (epsGL e w h) *ᵥ x = x + spForm 2 K x e • w + spForm 2 K x w • e :=
  epsMat_mulVec e w x

theorem epsGL_mem (e w : Fin 2 ⊕ Fin 2 → K) (h : spForm 2 K e w = 0) :
    epsGL e w h ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff_preserves]
  intro x y
  have h' : spForm 2 K w e = 0 := by rw [spForm_neg_left, h, neg_zero]
  rw [epsGL_mulVec, epsGL_mulVec]
  have hx := spForm_neg_left x e
  have hy := spForm_neg_left y e
  have hxw := spForm_neg_left x w
  have hyw := spForm_neg_left y w
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, spForm_self, h, h',
    smul_eq_mul, mul_zero, add_zero]
  have e1 : spForm 2 K w y = - spForm 2 K y w := spForm_neg_left y w
  have e2 : spForm 2 K e y = - spForm 2 K y e := spForm_neg_left y e
  rw [e1, e2]
  ring

@[expose] noncomputable def epsS (e w : Fin 2 ⊕ Fin 2 → K) (h : spForm 2 K e w = 0) :
    StatedSp 2 K :=
  ⟨epsGL e w h, epsGL_mem e w h⟩

theorem mx_epsS_mulVec (e w : Fin 2 ⊕ Fin 2 → K) (h : spForm 2 K e w = 0) (x : Fin 2 ⊕ Fin 2 → K) :
    mx ((epsS e w h : StatedSp 2 K) : GL _ K) *ᵥ x = x + spForm 2 K x e • w + spForm 2 K x w • e :=
  epsMat_mulVec e w x

theorem cf_epsS (A : gsp 2 K) (σ : K ≃+* K) (e w : Fin 2 ⊕ Fin 2 → K) (h : spForm 2 K e w = 0)
    (h' : spForm 2 K (semi A σ e) (((multiplier 2 K A : Kˣ) : K)⁻¹ • semi A σ w) = 0) :
    cf A σ (epsS e w h) =
      epsS (semi A σ e) (((multiplier 2 K A : Kˣ) : K)⁻¹ • semi A σ w) h' := by
  apply Subtype.ext
  apply gl_ext_mulVec
  intro v
  obtain ⟨u, rfl⟩ := exists_semi_eq A σ v
  have hμ : ((multiplier 2 K A : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [cf_mulVec_semi, mx_epsS_mulVec, mx_epsS_mulVec, semi_add, semi_add, semi_smul, semi_smul,
    spForm_semi A σ u e, LinearMap.map_smul, spForm_semi A σ u w, smul_eq_mul, smul_smul]
  have e1 : ((multiplier 2 K A : Kˣ) : K) * σ (spForm 2 K u e) * ((multiplier 2 K A : Kˣ) : K)⁻¹ =
      σ (spForm 2 K u e) := by field_simp
  have e2 : ((multiplier 2 K A : Kˣ) : K)⁻¹ * (((multiplier 2 K A : Kˣ) : K) * σ (spForm 2 K u w)) =
      σ (spForm 2 K u w) := by field_simp
  rw [e1, e2]

theorem eq_of_eps_vec (h2 : (2 : K) ≠ 0) {e w w' : Fin 2 ⊕ Fin 2 → K} (he : e ≠ 0)
    (key : ∀ x, spForm 2 K x e • w + spForm 2 K x w • e =
      spForm 2 K x e • w' + spForm 2 K x w' • e) : w = w' := by
  have key' : ∀ x, spForm 2 K x e • (w - w') + spForm 2 K x (w - w') • e = 0 := by
    intro x
    have h3 := key x
    rw [map_sub, smul_sub, sub_smul]
    linear_combination (exp := 1) h3
  obtain ⟨x0, hx0⟩ := exists_spForm_ne_zero he
  have h1 := key' x0
  have h3 := congrArg (spForm 2 K x0) h1
  simp only [map_add, map_smul, smul_eq_mul, map_zero] at h3
  have h4 : spForm 2 K x0 (w - w') = 0 := by
    have : (2 * spForm 2 K x0 e) * spForm 2 K x0 (w - w') = 0 := by
      rw [map_sub] at h3 ⊢
      linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hx0)
  rw [h4, zero_smul, add_zero] at h1
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hx0)

theorem eps_vec_of_epsS_eq {e w e' w' : Fin 2 ⊕ Fin 2 → K} {h : spForm 2 K e w = 0}
    {h' : spForm 2 K e' w' = 0} (heq : epsS e w h = epsS e' w' h') (x : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K x e • w + spForm 2 K x w • e = spForm 2 K x e' • w' + spForm 2 K x w' • e' := by
  have := congrArg (fun g : StatedSp 2 K => mx (g : GL _ K) *ᵥ x) heq
  simp only [mx_epsS_mulVec] at this
  exact add_left_cancel (a := x) (by simpa only [add_assoc] using this)

@[expose] def act (x : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  mx (x : GL _ K) *ᵥ v

theorem act_mul (x y : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) : act (x * y) v = act x (act y v) := by
  unfold act
  simp only [mx, Subgroup.coe_mul, Units.val_mul]
  rw [← Matrix.mulVec_mulVec]

theorem act_one (v : Fin 2 ⊕ Fin 2 → K) : act (1 : StatedSp 2 K) v = v := by
  unfold act
  simp

theorem act_inv_act (x : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) : act x⁻¹ (act x v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (x : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) : act x (act x⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_add (x : StatedSp 2 K) (v w : Fin 2 ⊕ Fin 2 → K) :
    act x (v + w) = act x v + act x w := by
  unfold act
  rw [Matrix.mulVec_add]

theorem act_sub (x : StatedSp 2 K) (v w : Fin 2 ⊕ Fin 2 → K) :
    act x (v - w) = act x v - act x w := by
  unfold act
  rw [Matrix.mulVec_sub]

theorem act_smul (x : StatedSp 2 K) (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    act x (c • v) = c • act x v := by
  unfold act
  rw [Matrix.mulVec_smul]

theorem spForm_act (x : StatedSp 2 K) (v w : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (act x v) (act x w) = spForm 2 K v w :=
  spForm_mulVec x.2 v w

theorem act_ext {x y : StatedSp 2 K} (h : ∀ v, act x v = act y v) : x = y :=
  Subtype.ext (gl_ext_mulVec h)

theorem eq_zero_of_forall_spForm {y : Fin 2 ⊕ Fin 2 → K} (h : ∀ v, spForm 2 K v y = 0) : y = 0 :=
  spForm_separatingLeft y fun v => spForm_isRefl _ _ (h v)

@[expose] def HP (P : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Subgroup (StatedSp 2 K) where
  carrier := {h | ∀ v ∈ orth P, act h v = v}
  one_mem' := fun v _ => act_one v
  mul_mem' := fun {a b} ha hb v hv => by rw [act_mul, hb v hv, ha v hv]
  inv_mem' := fun {a} ha v hv => by
    calc act a⁻¹ v = act a⁻¹ (act a v) := by rw [ha v hv]
      _ = v := act_inv_act a v

theorem mem_HP {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} {h : StatedSp 2 K} :
    h ∈ HP P ↔ ∀ v ∈ orth P, act h v = v := Iff.rfl

theorem sq_eq_one_of_proj_eq_one {s : StatedSp 2 K} (h : proj 2 K s = 1) : s ^ 2 = 1 := by
  have h' : (QuotientGroup.mk s : StatedSp 2 K ⧸ spScalars 2 K) = 1 := h
  have hs : s ∈ spScalars 2 K := (QuotientGroup.eq_one_iff s).mp h'
  rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hs
  obtain ⟨c, hc⟩ := hs
  have hv : ∀ v : Fin 2 ⊕ Fin 2 → K, act s v = (c : K) • v := by
    intro v
    show mx (s : GL _ K) *ᵥ v = _
    rw [← hc]
    simp only [mx, GeneralLinearGroup.coe_scalar]
    simp [Matrix.scalar_apply]
  set v0 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1
  set w0 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inr 0) 1
  have hB : spForm 2 K v0 w0 = 1 := by
    rw [spForm_apply]
    simp [v0, w0, Pi.single_apply]
  have h1 := spForm_act s v0 w0
  rw [hv, hv] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, mul_one] at h1
  have hc2 : (c : K) * c = 1 := h1
  have hc2' : c * c = 1 := Units.ext (by simpa using hc2)
  have hsc : (s : GL (Fin 2 ⊕ Fin 2) K) ^ 2 = 1 := by
    rw [← hc, ← map_pow, pow_two, hc2', map_one]
  apply Subtype.ext
  exact hsc

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
