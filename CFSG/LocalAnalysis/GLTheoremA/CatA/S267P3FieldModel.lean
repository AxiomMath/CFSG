module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FormModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelB
import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
import CFSG.GroupTheory.PLayer.CentralQuotient
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {F : Type} [Field F]

structure FieldData (F : Type) [Field F] (μ : Type) [Fintype μ] [DecidableEq μ] where
  G2 : Subgroup (SpecialLinearGroup (Fin 2) F)
  Gl : Subgroup (SpecialLinearGroup (Lam μ) F)
  Gt : Subgroup (SpecialLinearGroup (Kap μ) F)
  blk_top : ∀ P ∈ G2, ∀ Y ∈ Gl, blk (Lam μ) (P, Y) ∈ Gt
  blk_lam : ∀ P ∈ G2, blk μ (P, 1) ∈ Gl
  top_inv : ∀ Y, blk (Lam μ) (1, Y) ∈ Gt → Y ∈ Gl
  c : SpecialLinearGroup (Fin 2) F
  c_mem : c ∈ G2
  c_rel : (c : Matrix (Fin 2) (Fin 2) F) * c + c + 1 = 0
  c_ne : (c : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0
  x : F
  w : SpecialLinearGroup (Fin 2) F
  w_mem : w ∈ G2
  coe_w : (w : Matrix (Fin 2) (Fin 2) F) = !![x, 0; 0, x⁻¹]
  x_sq : x ^ 2 ≠ 1
  negOne_mem : negOne ∈ G2
  σ : F ≃+* F
  σ_cube : σ ^ 3 = 1
  σ_x : σ x ≠ x
  map_Gt : ∀ g ∈ Gt, Matrix.SpecialLinearGroup.map (σ : F →+* F) g ∈ Gt
  map_c : Matrix.SpecialLinearGroup.map (σ : F →+* F) c = c

namespace FieldData

variable {μ : Type} [Fintype μ] [DecidableEq μ] (D : FieldData F μ)

abbrev Zt : Subgroup ↥D.Gt := (Subgroup.center (SpecialLinearGroup (Kap μ) F)).subgroupOf D.Gt

abbrev XD : Type := ↥D.Gt ⧸ D.Zt

noncomputable abbrev πD : ↥D.Gt →* D.XD := QuotientGroup.mk' _

theorem Zt_le_center : D.Zt ≤ Subgroup.center ↥D.Gt := fun z hz =>
  Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_center_iff.1 (Subgroup.mem_subgroupOf.1 hz) (g : _))

@[expose] def cG : ↥D.G2 := ⟨D.c, D.c_mem⟩

theorem c_pow_three : D.c ^ 3 = 1 := pow_three_of_rel D.c_rel

theorem cG_pow_three : D.cG ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact D.c_pow_three)

theorem x_ne_zero : D.x ≠ 0 := by
  intro h
  have hdet := D.w.2
  rw [D.coe_w, h, Matrix.det_fin_two_of] at hdet
  simp at hdet

theorem x_ne_inv : D.x ≠ D.x⁻¹ := by
  intro h
  apply D.x_sq
  have h0 := D.x_ne_zero
  calc D.x ^ 2 = D.x * D.x := sq _
    _ = D.x * D.x⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel₀ h0

theorem c_mul_w : D.c * D.w ≠ D.w * D.c := by
  intro h
  have h01 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, D.coe_w, Matrix.mul_apply, Fin.sum_univ_two] at h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, mul_zero, zero_mul, zero_add,
    add_zero] at h01
  have h1 : (D.c : Matrix (Fin 2) (Fin 2) F) 0 1 * (D.x⁻¹ - D.x) = 0 := by
    linear_combination h01
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact D.c_ne h2
  · exact D.x_ne_inv (sub_eq_zero.1 h2).symm

@[expose] noncomputable def ΦG : ↥D.G2 × ↥D.G2 →* ↥D.Gt :=
  (((blk (Lam μ)).comp (MonoidHom.prodMap (MonoidHom.id _) ((blk μ).comp (MonoidHom.inl _ _)))).comp
    (MonoidHom.prodMap D.G2.subtype D.G2.subtype)).codRestrict D.Gt fun x =>
      D.blk_top x.1 x.1.2 (blk μ (x.2, 1)) (D.blk_lam x.2 x.2.2)

theorem coe_ΦG (x : ↥D.G2 × ↥D.G2) :
    (D.ΦG x : SpecialLinearGroup (Kap μ) F) = blk (Lam μ) (x.1, blk μ (x.2, 1)) := rfl

theorem ΦG_injective : Function.Injective D.ΦG := by
  rintro ⟨P, Q⟩ ⟨P', Q'⟩ h
  have h' := congrArg Subtype.val h
  rw [coe_ΦG, coe_ΦG] at h'
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (blk_injective h')
  obtain ⟨h3, -⟩ := Prod.ext_iff.1 (blk_injective h2)
  simp only at h1 h3
  rw [Subtype.ext h1, Subtype.ext h3]

@[expose] noncomputable def a₁G : ↥D.Gt :=
  ⟨blk (Lam μ) (D.c, 1), D.blk_top _ D.c_mem _ (one_mem _)⟩

theorem ΦG_c : D.ΦG (D.cG, 1) = D.a₁G := Subtype.ext (by
  rw [coe_ΦG]
  change blk (Lam μ) (D.c, blk μ (1, 1)) = blk (Lam μ) (D.c, 1)
  rw [blk_one_one])

theorem a₁G_pow_three : D.a₁G ^ 3 = 1 := by
  rw [← D.ΦG_c, ← map_pow]
  simp only [Prod.pow_mk, D.cG_pow_three, one_pow]
  exact map_one _

@[expose] def Adom : Subgroup (↥D.G2 × ↥D.G2) :=
  (Subgroup.zpowers D.cG).prod (Subgroup.zpowers D.cG)

@[expose] def A1dom : Subgroup (↥D.G2 × ↥D.G2) := Subgroup.zpowers (D.cG, 1)

theorem A1dom_le_Adom : D.A1dom ≤ D.Adom := by
  rw [A1dom, Subgroup.zpowers_le]
  exact ⟨Subgroup.mem_zpowers _, Subgroup.one_mem _⟩

theorem isElemAbelian_Adom : IsElemAbelian 3 D.Adom :=
  Lin.isElemAbelian_prod (Lin.isElemAbelian_zpowers D.cG_pow_three)
    (Lin.isElemAbelian_zpowers D.cG_pow_three)

theorem orderOf_cG (h3 : (3 : F) ≠ 0) : orderOf D.cG = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime D.cG_pow_three fun h => ne_one_of_rel h3 D.c_rel (congrArg Subtype.val h)

theorem card_Adom (h3 : (3 : F) ≠ 0) : Nat.card D.Adom = 3 ^ 2 := by
  rw [Adom, Lin.card_prod_subgroup, Nat.card_zpowers, D.orderOf_cG h3]
  norm_num

theorem card_A1dom (h3 : (3 : F) ≠ 0) : Nat.card D.A1dom = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [A1dom, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · simp [D.cG_pow_three]
  · intro h
    exact ne_one_of_rel h3 D.c_rel (congrArg Subtype.val (congrArg Prod.fst h))

@[expose] noncomputable def Asub : Subgroup D.XD := D.Adom.map (D.πD.comp D.ΦG)

@[expose] noncomputable def A1sub : Subgroup D.XD := D.A1dom.map (D.πD.comp D.ΦG)

theorem A1sub_eq : D.A1sub = Subgroup.zpowers (D.πD D.a₁G) := by
  rw [A1sub, A1dom, MonoidHom.map_zpowers, MonoidHom.comp_apply, ΦG_c]

theorem A1sub_le_Asub : D.A1sub ≤ D.Asub := Subgroup.map_mono D.A1dom_le_Adom

@[expose] noncomputable def Jt : Subgroup ↥D.Gt := (blkRange (F := F) (ι := Lam μ)).subgroupOf D.Gt

@[expose] noncomputable def Jsub : Subgroup D.XD := D.Jt.map D.πD

@[expose] noncomputable def βk : ↥D.Gl →* ↥D.Gt :=
  (((blk (Lam μ)).comp (MonoidHom.inr _ _)).comp D.Gl.subtype).codRestrict D.Gt fun Y =>
    D.blk_top 1 (one_mem _) Y Y.2

theorem coe_βk (Y : ↥D.Gl) : (D.βk Y : SpecialLinearGroup (Kap μ) F) = blk (Lam μ) (1, Y) := rfl

theorem βk_injective : Function.Injective D.βk := fun _ _ h =>
  Subtype.ext (blkInr_injective (congrArg Subtype.val h))

theorem range_βk : D.βk.range = D.Jt := by
  ext y
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, rfl⟩
  · rintro ⟨Y, hY⟩
    have hYk : Y ∈ D.Gl := D.top_inv Y (by
      rw [show blk (Lam μ) (1, Y) = (y : SpecialLinearGroup (Kap μ) F) from hY]
      exact y.2)
    exact ⟨⟨Y, hYk⟩, Subtype.ext hY⟩

section NoThree

variable (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1)
include hZ3

theorem ker_Adom : ∀ x ∈ D.Adom, (D.πD.comp D.ΦG) x = 1 → x = 1 := by
  intro x hx h1
  have hc : D.ΦG x ∈ D.Zt := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : D.ΦG x ^ 3 = 1 := by rw [← map_pow, D.isElemAbelian_Adom.2 x hx, map_one]
  exact D.ΦG_injective (by rw [hZ3 _ hc h3, map_one])

theorem card_Asub (h3 : (3 : F) ≠ 0) : Nat.card D.Asub = 3 ^ 2 := by
  rw [Asub, card_map_eq_of_ker _ _ (D.ker_Adom hZ3), D.card_Adom h3]

theorem card_A1sub (h3 : (3 : F) ≠ 0) : Nat.card D.A1sub = 3 := by
  rw [A1sub, card_map_eq_of_ker _ _ fun x hx => D.ker_Adom hZ3 x (D.A1dom_le_Adom hx),
    D.card_A1dom h3]

end NoThree

theorem ker_Jt : ∀ y ∈ D.Jt, D.πD y = 1 → y = 1 := by
  rintro y ⟨Y, hY⟩ h1
  replace hY : blk (Lam μ) (1, Y) = (y : SpecialLinearGroup (Kap μ) F) := hY
  have hc : (y : SpecialLinearGroup (Kap μ) F) ∈ Subgroup.center _ :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  rw [← hY] at hc
  have hY1 : Y = 1 := eq_one_of_blk_one_mem_center (ι := Lam μ) (Y := Y) hc
  apply Subtype.ext
  rw [← hY, hY1, blk_one_one]
  rfl

theorem isQuasisimple_Jt (hl : CFSG.Open.IsQuasisimple ↥D.Gl) :
    CFSG.Open.IsQuasisimple ↥D.Jt :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    ((MulEquiv.subgroupCongr D.range_βk).symm.trans (MonoidHom.ofInjective D.βk_injective).symm) hl

theorem isQuasisimple_Jsub (hl : CFSG.Open.IsQuasisimple ↥D.Gl) :
    CFSG.Open.IsQuasisimple ↥D.Jsub :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapEquivOfKer D.πD _ D.ker_Jt) (D.isQuasisimple_Jt hl)

theorem three_dvd_Jt [Finite F] : 3 ∣ Nat.card (↥D.Jt ⧸ Subgroup.center ↥D.Jt) := by
  have hmem : ∀ Y, D.βk Y ∈ D.Jt := fun Y => D.range_βk ▸ ⟨Y, rfl⟩
  refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
    Nat.prime_three (hmem ⟨_, D.blk_lam _ D.c_mem⟩) (hmem ⟨_, D.blk_lam _ D.w_mem⟩) ?_ ?_
  · rw [← map_pow]
    have : (⟨_, D.blk_lam _ D.c_mem⟩ : ↥D.Gl) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, Prod.pow_mk, D.c_pow_three, one_pow]
      exact blk_one_one)
    rw [this, map_one]
  · intro h
    have h2 : D.βk (⟨_, D.blk_lam _ D.c_mem⟩ * ⟨_, D.blk_lam _ D.w_mem⟩) =
        D.βk (⟨_, D.blk_lam _ D.w_mem⟩ * ⟨_, D.blk_lam _ D.c_mem⟩) := by
      rw [map_mul, map_mul]
      exact h
    have h' := congrArg Subtype.val (D.βk_injective h2)
    simp only [Subgroup.coe_mul, ← map_mul] at h'
    exact D.c_mul_w (congrArg Prod.fst (blk_injective h'))

theorem three_dvd_Jsub [Finite F] : 3 ∣ Nat.card ↥D.Jsub := by
  rw [Jsub, card_map_eq_of_ker _ _ D.ker_Jt]
  exact D.three_dvd_Jt.trans (Subgroup.card_quotient_dvd_card _)

theorem Jt_le_centralizer : D.Jt ≤ Subgroup.centralizer ({D.a₁G} : Set ↥D.Gt) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (blkRange_le_centralizer' D.c hy))

theorem Jt_normal (h3 : (3 : F) ≠ 0) :
    (D.Jt.subgroupOf (Subgroup.centralizer ({D.a₁G} : Set ↥D.Gt))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : ((g : ↥D.Gt) : SpecialLinearGroup (Kap μ) F) * blk (Lam μ) (D.c, 1) =
      blk (Lam μ) (D.c, 1) * (g : ↥D.Gt) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  exact conj_mem_blkRange' h3 D.c_rel hg hn

theorem isSubnormal_Jt (h3 : (3 : F) ≠ 0) :
    CFSG.Open.IsSubnormal D.Jt (Subgroup.centralizer ({D.a₁G} : Set ↥D.Gt)) :=
  CFSG.Open.IsSubnormal.step D.Jt_le_centralizer (D.Jt_normal h3) (CFSG.Open.IsSubnormal.refl _)

section NoThree

variable (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1)
include hZ3

theorem glaPComponent_J [Finite F] (h3 : (3 : F) ≠ 0) (hl : CFSG.Open.IsQuasisimple ↥D.Gl) :
    GLAPComponent 3 (Subgroup.centralizer ((D.A1sub : Subgroup D.XD) : Set D.XD)) D.Jsub := by
  rw [D.A1sub_eq, centralizer_zpowers_eq, Jsub,
    centralizer_mk_eq _ D.Zt_le_center hZ3 D.a₁G_pow_three]
  refine (CFSG.glaPComponent_map_bijective_of_ker_le_center Nat.prime_three D.πD ?_).1 _ ?_
  · rintro y ⟨-, hy⟩ x -
    rw [QuotientGroup.ker_mk'] at hy
    exact Subgroup.mem_center_iff.1 (D.Zt_le_center hy) x
  · exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three
      (D.isSubnormal_Jt h3) (D.isQuasisimple_Jt hl) D.three_dvd_Jt

end NoThree

theorem Asub_le_normalizer (h3 : (3 : F) ≠ 0) :
    D.Asub ≤ Subgroup.normalizer ((D.Jsub : Subgroup D.XD) : Set D.XD) := by
  rintro _ ⟨x, hx, rfl⟩
  have hc : D.ΦG x ∈ Subgroup.centralizer ({D.a₁G} : Set ↥D.Gt) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← D.ΦG_c, ← map_mul, ← map_mul]
    exact congrArg D.ΦG (congrArg Subtype.val
      (D.isElemAbelian_Adom.1.is_comm.comm ⟨x, hx⟩
        ⟨_, ⟨Subgroup.mem_zpowers _, Subgroup.one_mem _⟩⟩))
  haveI := D.Jt_normal h3
  exact Subgroup.le_normalizer_map D.πD
    ⟨_, Subgroup.le_normalizer_of_normal_subgroupOf D.Jt_le_centralizer hc, rfl⟩

@[expose] noncomputable def tGt : ↥D.Gt :=
  ⟨blk (Lam μ) (negOne, 1), D.blk_top _ D.negOne_mem _ (one_mem _)⟩

theorem t_ne_one (h2 : (2 : F) ≠ 0) : D.πD D.tGt ≠ 1 := by
  intro h
  have hc : blk (Lam μ) ((negOne : SpecialLinearGroup (Fin 2) F), 1) ∈
      Subgroup.center (SpecialLinearGroup (Kap μ) F) :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [coe_blk] at hr
  have e1 := congrFun (congrFun hr (Sum.inl 0)) (Sum.inl 0)
  have e2 := congrFun (congrFun hr (Sum.inr (Sum.inl 0))) (Sum.inr (Sum.inl 0))
  simp [scalar_apply, negOne] at e1 e2
  apply h2
  linear_combination e1 - e2

theorem t_sq [Finite F] : D.πD D.tGt ^ 2 = 1 := by
  rw [← map_pow]
  have : D.tGt ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    change blk (Lam μ) (negOne, 1) ^ 2 = 1
    rw [← map_pow, Prod.pow_mk, negOne_sq, one_pow, blk_one_one])
  rw [this, map_one]

theorem Jsub_le_centralizer_t :
    D.Jsub ≤ Subgroup.centralizer ({D.πD D.tGt} : Set D.XD) := by
  rintro _ ⟨y, ⟨Y, hY⟩, rfl⟩
  replace hY : blk (Lam μ) (1, Y) = (y : SpecialLinearGroup (Kap μ) F) := hY
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hY]
  change blk (Lam μ) (1, Y) * blk (Lam μ) (negOne, 1) = blk (Lam μ) (negOne, 1) * blk (Lam μ) (1, Y)
  rw [← map_mul, ← map_mul]
  congr 1
  ext : 1 <;> simp

theorem Asub_le_centralizer_t [Finite F] :
    D.Asub ≤ Subgroup.centralizer ({D.πD D.tGt} : Set D.XD) := by
  rintro _ ⟨⟨P, Q⟩, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_ΦG]
  change blk (Lam μ) ((P : SpecialLinearGroup (Fin 2) F), _) * blk (Lam μ) (negOne, 1) =
    blk (Lam μ) (negOne, 1) * blk (Lam μ) ((P : SpecialLinearGroup (Fin 2) F), _)
  rw [← map_mul, ← map_mul]
  congr 1
  ext : 1
  · exact (negOne_mul_comm (P : SpecialLinearGroup (Fin 2) F)).symm
  · simp

theorem σ_cube_apply (y : F) : D.σ (D.σ (D.σ y)) = y := by
  have h : (D.σ ^ 3) y = (1 : F ≃+* F) y := by rw [D.σ_cube]
  exact h

theorem coe_map (f : F →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι F) :
    ((Matrix.SpecialLinearGroup.map f g : SpecialLinearGroup ι F) : Matrix ι ι F) =
      (g : Matrix ι ι F).map f := rfl

omit [Fintype μ] [DecidableEq μ] in
theorem map_blk (f : F →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : SpecialLinearGroup (Fin 2) F) (Y : SpecialLinearGroup ι F) :
    Matrix.SpecialLinearGroup.map f (blk ι (P, Y)) =
      blk ι (Matrix.SpecialLinearGroup.map f P, Matrix.SpecialLinearGroup.map f Y) := by
  apply Subtype.ext
  rw [coe_map, coe_blk, coe_blk, coe_map, coe_map, Matrix.fromBlocks_map, Matrix.map_zero _ f.map_zero,
    Matrix.map_zero _ f.map_zero]

theorem map_σ_σ_σ {ι : Type} [Fintype ι] [DecidableEq ι] (g : SpecialLinearGroup ι F) :
    Matrix.SpecialLinearGroup.map (D.σ : F →+* F) (Matrix.SpecialLinearGroup.map (D.σ : F →+* F)
      (Matrix.SpecialLinearGroup.map (D.σ : F →+* F) g)) = g := by
  apply Subtype.ext
  rw [coe_map, coe_map, coe_map, Matrix.map_map, Matrix.map_map]
  ext i j
  exact D.σ_cube_apply _

@[expose] noncomputable def σt : ↥D.Gt ≃* ↥D.Gt where
  toFun g := ⟨Matrix.SpecialLinearGroup.map (D.σ : F →+* F) g, D.map_Gt g g.2⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.map (D.σ : F →+* F) (Matrix.SpecialLinearGroup.map
      (D.σ : F →+* F) g), D.map_Gt _ (D.map_Gt g g.2)⟩
  left_inv g := Subtype.ext (D.map_σ_σ_σ (g : SpecialLinearGroup (Kap μ) F))
  right_inv g := Subtype.ext (D.map_σ_σ_σ (g : SpecialLinearGroup (Kap μ) F))
  map_mul' g h := Subtype.ext (map_mul _ _ _)

theorem coe_σt (g : ↥D.Gt) :
    ((D.σt g : ↥D.Gt) : SpecialLinearGroup (Kap μ) F) =
      Matrix.SpecialLinearGroup.map (D.σ : F →+* F) g := rfl

theorem map_mem_center {ι : Type} [Fintype ι] [DecidableEq ι] {g : SpecialLinearGroup ι F}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup ι F)) :
    Matrix.SpecialLinearGroup.map (D.σ : F →+* F) g ∈ Subgroup.center (SpecialLinearGroup ι F) := by
  rw [Subgroup.mem_center_iff] at hg ⊢
  intro h
  have e : h = Matrix.SpecialLinearGroup.map (D.σ : F →+* F) (Matrix.SpecialLinearGroup.map
      (D.σ : F →+* F) (Matrix.SpecialLinearGroup.map (D.σ : F →+* F) h)) := (D.map_σ_σ_σ h).symm
  rw [e, ← map_mul, ← map_mul, hg]

theorem map_Zt : D.Zt.map D.σt.toMonoidHom = D.Zt := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (D.map_mem_center (Subgroup.mem_subgroupOf.1 hz))
  · intro z hz
    refine ⟨D.σt (D.σt z), Subgroup.mem_subgroupOf.2 (D.map_mem_center (D.map_mem_center
      (Subgroup.mem_subgroupOf.1 hz))), Subtype.ext (D.map_σ_σ_σ (z : SpecialLinearGroup (Kap μ) F))⟩

@[expose] noncomputable def ψD : MulAut D.XD := QuotientGroup.congr D.Zt D.Zt D.σt D.map_Zt

theorem ψD_mk (g : ↥D.Gt) : D.ψD (D.πD g) = D.πD (D.σt g) :=
  QuotientGroup.congr_mk' _ _ _ D.map_Zt g

theorem ψD_pow_three : D.ψD ^ 3 = 1 := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D.Zt y
  change D.ψD (D.ψD (D.ψD (D.πD g))) = D.πD g
  rw [D.ψD_mk, D.ψD_mk, D.ψD_mk]
  congr 1
  exact Subtype.ext (D.map_σ_σ_σ (g : SpecialLinearGroup (Kap μ) F))

theorem ψD_pow_mk (k : ℕ) (g : ↥D.Gt) : (D.ψD ^ k) (D.πD g) = D.πD ((D.σt ^ k) g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, D.ψD_mk, ih, pow_succ, MulAut.mul_apply]

theorem map_zpowers_c (P : ↥D.G2) (hP : P ∈ Subgroup.zpowers D.cG) :
    Matrix.SpecialLinearGroup.map (D.σ : F →+* F) (P : SpecialLinearGroup (Fin 2) F) = P := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hP
  rw [Subgroup.coe_zpow, map_zpow]
  change Matrix.SpecialLinearGroup.map (D.σ : F →+* F) D.c ^ m = D.c ^ m
  rw [D.map_c]

theorem ψD_Asub : ∀ a ∈ D.Asub, D.ψD a = a := by
  rintro _ ⟨⟨P, Q⟩, hPQ, rfl⟩
  rw [MonoidHom.comp_apply, D.ψD_mk]
  congr 1
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.map (D.σ : F →+* F)
      (blk (Lam μ) ((P : SpecialLinearGroup (Fin 2) F), blk μ ((Q : SpecialLinearGroup (Fin 2) F), 1))) =
    blk (Lam μ) ((P : SpecialLinearGroup (Fin 2) F), blk μ ((Q : SpecialLinearGroup (Fin 2) F), 1))
  rw [map_blk, map_blk, map_one, D.map_zpowers_c P hPQ.1, D.map_zpowers_c Q hPQ.2]

theorem σt_βk (Y : ↥D.Gl) : ∃ Y' : ↥D.Gl, (Y' : SpecialLinearGroup (Lam μ) F) =
    Matrix.SpecialLinearGroup.map (D.σ : F →+* F) Y ∧ D.σt (D.βk Y) = D.βk Y' := by
  have hmem : blk (Lam μ) (1, Matrix.SpecialLinearGroup.map (D.σ : F →+* F) Y) ∈ D.Gt := by
    have h := D.map_Gt _ (D.βk Y).2
    rw [coe_βk, map_blk, map_one] at h
    exact h
  refine ⟨⟨_, D.top_inv _ hmem⟩, rfl, Subtype.ext ?_⟩
  rw [coe_σt, coe_βk, coe_βk, map_blk, map_one]

theorem map_Jt [Finite F] : D.Jt.map D.σt.toMonoidHom = D.Jt := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    rw [← D.range_βk] at hy ⊢
    obtain ⟨Y, rfl⟩ := hy
    obtain ⟨Y', -, hY'⟩ := D.σt_βk Y
    exact ⟨Y', hY'.symm⟩
  · rw [Subgroup.card_map_of_injective D.σt.injective]

theorem map_Jsub [Finite F] : D.Jsub.map D.ψD.toMonoidHom = D.Jsub := by
  rw [Jsub, Subgroup.map_map]
  have e : D.ψD.toMonoidHom.comp D.πD = D.πD.comp D.σt.toMonoidHom := by
    ext g
    exact D.ψD_mk g
  rw [e, ← Subgroup.map_map, D.map_Jt]

theorem ψD_t : D.ψD (D.πD D.tGt) = D.πD D.tGt := by
  rw [D.ψD_mk]
  congr 1
  apply Subtype.ext
  rw [coe_σt]
  change Matrix.SpecialLinearGroup.map (D.σ : F →+* F) (blk (Lam μ) (negOne, 1)) =
    blk (Lam μ) (negOne, 1)
  rw [map_blk, map_one]
  congr 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  simp [negOne, Matrix.neg_apply, Matrix.one_apply]

theorem c_trace :
    (D.c : Matrix (Fin 2) (Fin 2) F) 0 0 + (D.c : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 := by
  have h := congrFun (congrFun D.c_rel 0) 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero] at h
  have h2 : (D.c : Matrix (Fin 2) (Fin 2) F) 0 1 *
      ((D.c : Matrix (Fin 2) (Fin 2) F) 0 0 + (D.c : Matrix (Fin 2) (Fin 2) F) 1 1 + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 D.c_ne
  · linear_combination h3

theorem false_of_mul_diag {M : Matrix (Fin 2) (Fin 2) F} (h01 : M 0 1 ≠ 0) (htr : M 0 0 + M 1 1 = -1)
    {u : F} (h : M * !![u, 0; 0, u⁻¹] = !![D.x, 0; 0, D.x⁻¹] * M) : False := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, mul_zero, zero_mul, add_zero, zero_add] at e00 e01 e11
  have hux : u⁻¹ = D.x := by
    have : M 0 1 * (u⁻¹ - D.x) = 0 := by linear_combination e01
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h01)
  have hu : u = D.x⁻¹ := by rw [← hux, inv_inv]
  have hx := D.x_ne_inv
  have h0 : M 0 0 = 0 := by
    rw [hu] at e00
    have : M 0 0 * (D.x⁻¹ - D.x) = 0 := by linear_combination e00
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hx))
  have h1 : M 1 1 = 0 := by
    rw [hux] at e11
    have : M 1 1 * (D.x - D.x⁻¹) = 0 := by linear_combination e11
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hx)
  rw [h0, h1, add_zero] at htr
  exact one_ne_zero (neg_eq_zero.1 htr.symm)

theorem eq_one_of_mul_diag {Q : SpecialLinearGroup (Fin 2) F} (hQ : Q ∈ Subgroup.zpowers D.c)
    {u : F} (h : (Q : Matrix (Fin 2) (Fin 2) F) * !![u, 0; 0, u⁻¹] = !![D.x, 0; 0, D.x⁻¹] * Q) :
    Q = 1 ∧ u = D.x := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hQ
  have hc3' : D.c ^ (3 : ℤ) = 1 := by exact_mod_cast D.c_pow_three
  have hk : D.c ^ m = D.c ^ (m % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 3]
    rw [_root_.zpow_add, _root_.zpow_mul, hc3', _root_.one_zpow, mul_one]
  rw [hk] at h ⊢
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with hm | hm | hm
  · rw [hm, zpow_zero] at h ⊢
    refine ⟨rfl, ?_⟩
    have e00 := congrFun (congrFun h 0) 0
    simpa using e00
  · rw [hm, zpow_one] at h
    exact (D.false_of_mul_diag D.c_ne D.c_trace h).elim
  · rw [hm] at h
    have hcc : ((D.c ^ (2 : ℤ) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -(D.c : Matrix (Fin 2) (Fin 2) F) - 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, Matrix.SpecialLinearGroup.coe_pow, sq]
      have h : (D.c : Matrix (Fin 2) (Fin 2) F) * D.c - (-(D.c : Matrix (Fin 2) (Fin 2) F) - 1) =
          0 := by
        rw [← D.c_rel]
        abel
      exact sub_eq_zero.1 h
    rw [hcc] at h
    refine (D.false_of_mul_diag ?_ ?_ h).elim
    · simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply_ne
        (show (0 : Fin 2) ≠ 1 by decide), sub_zero, neg_ne_zero]
      exact D.c_ne
    · simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply_eq]
      linear_combination -D.c_trace

theorem eq_of_mk_mul {g₀ g₁ g₂ : ↥D.Gt} {P₀ : SpecialLinearGroup (Fin 2) F}
    {Y₀ Y₁ Y₂ : SpecialLinearGroup (Lam μ) F}
    (h₀ : (g₀ : SpecialLinearGroup (Kap μ) F) = blk (Lam μ) (P₀, Y₀))
    (h₁ : (g₁ : SpecialLinearGroup (Kap μ) F) = blk (Lam μ) (1, Y₁))
    (h₂ : (g₂ : SpecialLinearGroup (Kap μ) F) = blk (Lam μ) (1, Y₂))
    (h : D.πD g₀ * D.πD g₁ = D.πD g₂ * D.πD g₀) : Y₀ * Y₁ = Y₂ * Y₀ := by
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, h₀, h₁, h₂] at h
  rw [← map_mul, ← map_mul, ← map_inv, ← map_mul] at h
  have e : ((P₀, Y₀) * (1, Y₁))⁻¹ * ((1, Y₂) * (P₀, Y₀)) =
      ((1 : SpecialLinearGroup (Fin 2) F), (Y₀ * Y₁)⁻¹ * (Y₂ * Y₀)) :=
    Prod.ext (by simp) rfl
  rw [e] at h
  have e' : (Y₀ * Y₁)⁻¹ * (Y₂ * Y₀) = 1 := eq_one_of_blk_one_mem_center h
  rw [inv_mul_eq_one] at e'
  exact e'

theorem coe_σt_pow (k : ℕ) (g : ↥D.Gt) :
    (((D.σt ^ k) g : ↥D.Gt) : SpecialLinearGroup (Kap μ) F) =
      Matrix.SpecialLinearGroup.map ((D.σ ^ k : F ≃+* F) : F →+* F) g := by
  induction k generalizing g with
  | zero =>
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    rfl
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_σt]
    apply Subtype.ext
    rw [coe_map, coe_map, coe_map, Matrix.map_map]
    rfl

theorem eq_zero_of_pow_apply {k : ℕ} (hk : k < 3) (h : (D.σ ^ k) D.x = D.x) : k = 0 := by
  interval_cases k
  · rfl
  · exact absurd h D.σ_x
  · exfalso
    apply D.σ_x
    have h2 : D.σ (D.σ D.x) = D.x := h
    calc D.σ D.x = D.σ (D.σ (D.σ D.x)) := by rw [h2]
      _ = D.x := D.σ_cube_apply _

theorem centMod_clause [Finite F] (hl : CFSG.Open.IsQuasisimple ↥D.Gl) :
    ∀ a ∈ D.Asub, ∀ k : ℕ, k < 3 →
      (∀ j ∈ D.Jsub, j * (a * (D.ψD ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 D.Jsub) →
        k = 0 ∧ a ∈ D.A1sub := by
  rintro _ ⟨⟨P, Q⟩, hPQ, rfl⟩ k hk hj
  set a : D.XD := (D.πD.comp D.ΦG) (P, Q) with ha
  have hfix : ∀ j ∈ D.Jsub, a * (D.ψD ^ k) j * a⁻¹ = j := by
    have h := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf
      Nat.prime_three (D.isQuasisimple_Jsub hl) D.three_dvd_Jsub
      (MulAut.conj a * D.ψD ^ k).toMonoidHom fun j hj' => by
        have h1 := (GLAPPrimeCoreOf 3 D.Jsub).inv_mem (hj j hj')
        rw [_root_.mul_inv_rev, inv_inv] at h1
        change a * (D.ψD ^ k) j * a⁻¹ * j⁻¹ ∈ _
        exact h1
    intro j hj'
    exact h j hj'
  set Yw : ↥D.Gl := ⟨blk μ (D.w, 1), D.blk_lam _ D.w_mem⟩ with hYw
  have hjw : D.πD (D.βk Yw) ∈ D.Jsub := ⟨_, D.range_βk ▸ ⟨Yw, rfl⟩, rfl⟩
  have h1 := hfix _ hjw
  rw [D.ψD_pow_mk] at h1
  have h2 : a * D.πD ((D.σt ^ k) (D.βk Yw)) = D.πD (D.βk Yw) * a := by
    rw [← h1]
    group
  set w' : SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map ((D.σ ^ k : F ≃+* F) : F →+* F) D.w with hw'
  have h3 := D.eq_of_mk_mul (g₀ := D.ΦG (P, Q)) (g₁ := (D.σt ^ k) (D.βk Yw)) (g₂ := D.βk Yw)
    (P₀ := (P : SpecialLinearGroup (Fin 2) F)) (Y₀ := blk μ ((Q : SpecialLinearGroup (Fin 2) F), 1))
    (Y₁ := blk μ (w', 1)) (Y₂ := blk μ (D.w, 1)) (D.coe_ΦG _)
    (by rw [D.coe_σt_pow, coe_βk, map_blk, map_one, map_blk, map_one]) (D.coe_βk _) h2
  rw [← map_mul, ← map_mul] at h3
  have h4 := congrArg Prod.fst (blk_injective h3)
  simp only [Prod.fst_mul] at h4
  have h5 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h4
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h5
  have hw'c : ∀ τ : F ≃+* F, ((Matrix.SpecialLinearGroup.map (τ : F →+* F) D.w :
      SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![τ D.x, 0; 0, (τ D.x)⁻¹] := by
    intro τ
    rw [coe_map, D.coe_w]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_inv₀]
  rw [hw', hw'c, D.coe_w] at h5
  have hQ : (Q : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.zpowers D.c := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hPQ.2
    have hm' : D.cG ^ m = Q := hm
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← hm', Subgroup.coe_zpow]
    rfl
  obtain ⟨hQ1, hu⟩ := D.eq_one_of_mul_diag hQ h5
  refine ⟨D.eq_zero_of_pow_apply hk hu, ?_⟩
  have hQ1' : Q = 1 := Subtype.ext hQ1
  subst hQ1'
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hPQ.1
  have hm' : D.cG ^ m = P := hm
  refine ⟨(P, 1), Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩, rfl⟩
  ext : 1 <;> simp [hm']

@[expose] def Glσ : Subgroup ↥D.Gl :=
  MonoidHom.eqLocus ((Matrix.SpecialLinearGroup.map (D.σ : F →+* F)).comp D.Gl.subtype)
    D.Gl.subtype

theorem mem_Glσ {Y : ↥D.Gl} :
    Y ∈ D.Glσ ↔ Matrix.SpecialLinearGroup.map (D.σ : F →+* F) (Y : SpecialLinearGroup (Lam μ) F) =
      Y := Iff.rfl

theorem layer [Finite F] (hlay : GLAPLayer 3 D.Glσ ≠ ⊥) :
    GLAPLayer 3 (D.Jsub ⊓ fixSubgroup D.ψD) ≠ ⊥ := by
  set f : ↥D.Gl →* D.XD := D.πD.comp D.βk with hfdef
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro Y hY
    exact D.βk_injective ((D.ker_Jt _ (D.range_βk ▸ ⟨Y, rfl⟩) hY).trans (map_one _).symm)
  have hmap : D.Glσ.map f = D.Jsub ⊓ fixSubgroup D.ψD := by
    ext y
    constructor
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨⟨_, D.range_βk ▸ ⟨Y, rfl⟩, rfl⟩, ?_⟩
      show D.πD (D.βk Y) ∈ fixSubgroup D.ψD
      rw [mem_fixSubgroup]
      rw [D.ψD_mk]
      congr 1
      apply Subtype.ext
      rw [coe_σt, coe_βk, map_blk, map_one, D.mem_Glσ.1 hY]
    · rintro ⟨⟨g, hg, rfl⟩, hfix⟩
      rw [← D.range_βk] at hg
      obtain ⟨Y, rfl⟩ := hg
      refine ⟨Y, ?_, rfl⟩
      have hfix' : D.πD (D.βk Y) ∈ fixSubgroup D.ψD := hfix
      rw [mem_fixSubgroup, D.ψD_mk] at hfix'
      obtain ⟨Y', hY'1, hY'2⟩ := D.σt_βk Y
      rw [hY'2, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at hfix'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_βk] at hfix'
      rw [← map_inv, ← map_mul] at hfix'
      have e : ((1 : SpecialLinearGroup (Fin 2) F), (Y' : SpecialLinearGroup (Lam μ) F))⁻¹ *
          (1, (Y : SpecialLinearGroup (Lam μ) F)) = (1, (Y' : SpecialLinearGroup (Lam μ) F)⁻¹ * Y) :=
        Prod.ext (by simp) rfl
      rw [e] at hfix'
      have e' := eq_one_of_blk_one_mem_center hfix'
      rw [inv_mul_eq_one] at e'
      show Y ∈ D.Glσ
      rw [D.mem_Glσ, ← hY'1, e']
  rw [← hmap, ← map_glaPLayer Nat.prime_three f (by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf, Subgroup.card_bot]
    norm_num)]
  exact fun h => hlay ((Subgroup.map_eq_bot_iff_of_injective _ hf).1 h)

theorem modelB [Finite F] (h3 : (3 : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    (hl : CFSG.Open.IsQuasisimple ↥D.Gl) (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1)
    (hlay : GLAPLayer 3 D.Glσ ≠ ⊥) (hout : D.ψD ∉ (MulAut.conj : D.XD →* MulAut D.XD).range) :
    ModelB D.XD D.ψD :=
  ⟨D.ψD_pow_three, hout, D.Asub, D.A1sub, D.Jsub, D.πD D.tGt,
    CFSG.SectionRank.isElemAbelian_map D.isElemAbelian_Adom _, D.card_Asub hZ3 h3, D.ψD_Asub,
    D.A1sub_le_Asub, D.card_A1sub hZ3 h3, D.glaPComponent_J hZ3 h3 hl, D.Asub_le_normalizer h3,
    D.map_Jsub, D.centMod_clause hl, D.layer hlay, D.t_ne_one h2, D.t_sq,
    D.Jsub_le_centralizer_t, D.Asub_le_centralizer_t, D.ψD_t⟩

end FieldData

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

end
