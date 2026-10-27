module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3LinModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.GroupTheory.PLayer.CentralQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin

variable {F : Type} [Field F]

theorem eq_zero_of_mul_left' {ι : Type*} (h3 : (3 : F) ≠ 0) {c : Matrix (Fin 2) (Fin 2) F}
    (hc : c * c + c + 1 = 0) {Q : Matrix (Fin 2) ι F} (hQ : c * Q = Q) : Q = 0 := by
  have h1 : (c * c + c + 1) * Q = (3 : F) • Q := by
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hQ, hQ, Matrix.one_mul,
      show (3 : F) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [hc, Matrix.zero_mul] at h1
  ext i j
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 this.symm).resolve_left h3

theorem eq_zero_of_mul_right' {ι : Type*} (h3 : (3 : F) ≠ 0) {c : Matrix (Fin 2) (Fin 2) F}
    (hc : c * c + c + 1 = 0) {R : Matrix ι (Fin 2) F} (hR : R * c = R) : R = 0 := by
  have h1 : R * (c * c + c + 1) = (3 : F) • R := by
    rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hR, hR, Matrix.mul_one,
      show (3 : F) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [hc, Matrix.mul_zero] at h1
  ext i j
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 this.symm).resolve_left h3

theorem toBlocks_eq_zero_of_commute' {ι : Type*} [Fintype ι] [DecidableEq ι] (h3 : (3 : F) ≠ 0)
    {c : Matrix (Fin 2) (Fin 2) F} (hc : c * c + c + 1 = 0)
    {g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F}
    (hg : g * fromBlocks c 0 0 1 = fromBlocks c 0 0 1 * g) :
    g.toBlocks₁₂ = 0 ∧ g.toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks g, fromBlocks_multiply, fromBlocks_multiply] at hg
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at hg
  obtain ⟨-, h2, h3', -⟩ := Matrix.fromBlocks_inj.1 hg
  exact ⟨eq_zero_of_mul_left' h3 hc h2.symm, eq_zero_of_mul_right' h3 hc h3'⟩

theorem conj_mem_blkRange' {ι : Type} [Fintype ι] [DecidableEq ι] (h3 : (3 : F) ≠ 0)
    {cS : SpecialLinearGroup (Fin 2) F}
    (hc : (cS : Matrix (Fin 2) (Fin 2) F) * cS + cS + 1 = 0)
    {g y : SpecialLinearGroup (Fin 2 ⊕ ι) F}
    (hg : g * blk ι (cS, 1) = blk ι (cS, 1) * g) (hy : y ∈ blkRange (F := F) (ι := ι)) :
    g * y * g⁻¹ ∈ blkRange (F := F) (ι := ι) := by
  have hgi : g⁻¹ * blk ι (cS, 1) = blk ι (cS, 1) * g⁻¹ := by
    calc g⁻¹ * blk ι (cS, 1) = g⁻¹ * (blk ι (cS, 1) * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * blk ι (cS, 1)) * g⁻¹ := by rw [hg]
      _ = blk ι (cS, 1) * g⁻¹ := by group
  have cg := congrArg (fun x : SpecialLinearGroup (Fin 2 ⊕ ι) F =>
    (x : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)) hg
  have cgi := congrArg (fun x : SpecialLinearGroup (Fin 2 ⊕ ι) F =>
    (x : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)) hgi
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blk,
    Matrix.SpecialLinearGroup.coe_one] at cg cgi
  obtain ⟨g12, g21⟩ := toBlocks_eq_zero_of_commute' h3 hc cg
  obtain ⟨i12, i21⟩ := toBlocks_eq_zero_of_commute' h3 hc cgi
  obtain ⟨y11, y12, y21⟩ := mem_blkRange_iff.1 hy
  have hgg : (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 2 ⊕ ι) F) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  set G := (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)
  set Gi := ((g⁻¹ : SpecialLinearGroup (Fin 2 ⊕ ι) F) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)
  set Y := (y : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)
  have hG : G = fromBlocks G.toBlocks₁₁ 0 0 G.toBlocks₂₂ := by
    rw [← g12, ← g21, fromBlocks_toBlocks]
  have hGi : Gi = fromBlocks Gi.toBlocks₁₁ 0 0 Gi.toBlocks₂₂ := by
    rw [← i12, ← i21, fromBlocks_toBlocks]
  have hY : Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
    rw [← y11, ← y12, ← y21, fromBlocks_toBlocks]
  have h11 : G.toBlocks₁₁ * Gi.toBlocks₁₁ = 1 := by
    have := hgg
    rw [hG, hGi, fromBlocks_multiply] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at this
    exact (Matrix.fromBlocks_inj.1 (this.trans fromBlocks_one.symm)).1
  apply mem_blkRange_iff.2
  change (G * Y * Gi).toBlocks₁₁ = 1 ∧ (G * Y * Gi).toBlocks₁₂ = 0 ∧ (G * Y * Gi).toBlocks₂₁ = 0
  rw [hG, hY, hGi]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
  exact ⟨h11, trivial, trivial⟩

theorem pow_three_of_rel {cS : SpecialLinearGroup (Fin 2) F}
    (hc : (cS : Matrix (Fin 2) (Fin 2) F) * cS + cS + 1 = 0) : cS ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  have e : (cS : Matrix (Fin 2) (Fin 2) F) ^ 3 =
      ((cS : Matrix (Fin 2) (Fin 2) F) - 1) *
        ((cS : Matrix (Fin 2) (Fin 2) F) * cS + cS + 1) + 1 := by
    noncomm_ring
  rw [e, hc, Matrix.mul_zero, zero_add]
  rfl

theorem ne_one_of_rel (h3 : (3 : F) ≠ 0) {cS : SpecialLinearGroup (Fin 2) F}
    (hc : (cS : Matrix (Fin 2) (Fin 2) F) * cS + cS + 1 = 0) : cS ≠ 1 := by
  rintro rfl
  apply h3
  have h00 := congrFun (congrFun hc 0) 0
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.one_apply_eq, Matrix.zero_apply] at h00
  linear_combination h00

theorem eq_one_of_mem_zpowers_of_commute {H : Type*} [Group H] {c w P : H} (hc3 : c ^ 3 = 1)
    (hcw : c * w ≠ w * c) (hP : P ∈ Subgroup.zpowers c) (hPw : P * w = w * P) : P = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hP
  have hc3' : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  have hk : c ^ k = c ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, hc3', _root_.one_zpow, mul_one]
  rw [hk] at hPw ⊢
  have hc4 : c ^ 2 * c ^ 2 = c := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, hc3, one_mul]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hPw
    exact absurd hPw hcw
  · rw [h] at hPw
    have h2 : c ^ 2 * w = w * c ^ 2 := by exact_mod_cast hPw
    refine absurd ?_ hcw
    calc c * w = c ^ 2 * c ^ 2 * w := by rw [hc4]
      _ = c ^ 2 * (c ^ 2 * w) := mul_assoc _ _ _
      _ = c ^ 2 * (w * c ^ 2) := by rw [h2]
      _ = c ^ 2 * w * c ^ 2 := (mul_assoc _ _ _).symm
      _ = w * c ^ 2 * c ^ 2 := by rw [h2]
      _ = w * (c ^ 2 * c ^ 2) := mul_assoc _ _ _
      _ = w * c := by rw [hc4]

omit [Field F] in
theorem blkRange_le_centralizer' {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : SpecialLinearGroup (Fin 2) F) :
    blkRange (F := F) (ι := ι) ≤ Subgroup.centralizer ({blk ι (P, 1)} : Set _) := by
  rintro _ ⟨Y, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, ← map_mul]
  congr 1
  ext : 1 <;> simp

structure FormData (F : Type) [Field F] (ν : Type) [Fintype ν] [DecidableEq ν] where
  G2 : Subgroup (SpecialLinearGroup (Fin 2) F)
  Gl : Subgroup (SpecialLinearGroup (Lam ν) F)
  Gk : Subgroup (SpecialLinearGroup (Kap ν) F)
  Gt : Subgroup (SpecialLinearGroup (Lin.Top ν) F)
  blk_top : ∀ P ∈ G2, ∀ Y ∈ Gk, blk (Kap ν) (P, Y) ∈ Gt
  blk_kap : ∀ P ∈ G2, ∀ R ∈ Gl, blk (Lam ν) (P, R) ∈ Gk
  blk_lam : ∀ P ∈ G2, blk ν (P, 1) ∈ Gl
  top_inv : ∀ Y, blk (Kap ν) (1, Y) ∈ Gt → Y ∈ Gk
  kap_inv : ∀ R, blk (Lam ν) (1, R) ∈ Gk → R ∈ Gl
  c : SpecialLinearGroup (Fin 2) F
  c_mem : c ∈ G2
  c_rel : (c : Matrix (Fin 2) (Fin 2) F) * c + c + 1 = 0
  w : SpecialLinearGroup (Fin 2) F
  w_mem : w ∈ G2
  c_mul_w : c * w ≠ w * c
  negOne_mem : negOne ∈ G2

namespace FormData

variable {ν : Type} [Fintype ν] [DecidableEq ν] (D : FormData F ν)

abbrev Zt : Subgroup ↥D.Gt := (Subgroup.center (SpecialLinearGroup (Lin.Top ν) F)).subgroupOf D.Gt

abbrev XD : Type := ↥D.Gt ⧸ D.Zt

noncomputable abbrev πD : ↥D.Gt →* D.XD := QuotientGroup.mk' _

theorem Zt_le_center : D.Zt ≤ Subgroup.center ↥D.Gt := fun z hz =>
  Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_center_iff.1 (Subgroup.mem_subgroupOf.1 hz) (g : _))

@[expose] def cG : ↥D.G2 := ⟨D.c, D.c_mem⟩

@[expose] def wG : ↥D.G2 := ⟨D.w, D.w_mem⟩

theorem c_pow_three : D.c ^ 3 = 1 := pow_three_of_rel D.c_rel

theorem cG_pow_three : D.cG ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact D.c_pow_three)

theorem cG_mul_wG : D.cG * D.wG ≠ D.wG * D.cG := fun h => D.c_mul_w (congrArg Subtype.val h)

@[expose] noncomputable def ΦG : ↥D.G2 × (↥D.G2 × ↥D.G2) →* ↥D.Gt :=
  ((Lin.Φ ν).comp (MonoidHom.prodMap D.G2.subtype
    (MonoidHom.prodMap D.G2.subtype D.G2.subtype))).codRestrict D.Gt fun x =>
      D.blk_top x.1 x.1.2 (blk (Lam ν) (x.2.1, blk ν (x.2.2, 1)))
        (D.blk_kap x.2.1 x.2.1.2 _ (D.blk_lam x.2.2 x.2.2.2))

theorem coe_ΦG (x : ↥D.G2 × (↥D.G2 × ↥D.G2)) :
    (D.ΦG x : SpecialLinearGroup (Lin.Top ν) F) =
      blk (Kap ν) (x.1, blk (Lam ν) (x.2.1, blk ν (x.2.2, 1))) := rfl

theorem ΦG_injective : Function.Injective D.ΦG := by
  rintro ⟨P, Q, R⟩ ⟨P', Q', R'⟩ h
  have h' := congrArg Subtype.val h
  rw [coe_ΦG, coe_ΦG] at h'
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (blk_injective h')
  obtain ⟨h3, h4⟩ := Prod.ext_iff.1 (blk_injective h2)
  obtain ⟨h5, -⟩ := Prod.ext_iff.1 (blk_injective h4)
  simp only at h1 h3 h5
  rw [Subtype.ext h1, Subtype.ext h3, Subtype.ext h5]

@[expose] noncomputable def a₁G : ↥D.Gt :=
  ⟨blk (Kap ν) (D.c, 1), D.blk_top _ D.c_mem _ (one_mem _)⟩

@[expose] noncomputable def a₂G : ↥D.Gt :=
  ⟨blk (Kap ν) (1, blk (Lam ν) (D.c, 1)), D.blk_top _ (one_mem _) _ (D.blk_kap _ D.c_mem _
    (one_mem _))⟩

theorem ΦG_c : D.ΦG (D.cG, (1, 1)) = D.a₁G := Subtype.ext (by
  rw [coe_ΦG]
  change blk (Kap ν) (D.c, blk (Lam ν) (1, blk ν (1, 1))) = blk (Kap ν) (D.c, 1)
  rw [blk_one_one, blk_one_one])

theorem ΦG_c' : D.ΦG (1, (D.cG, 1)) = D.a₂G := Subtype.ext (by
  rw [coe_ΦG]
  change blk (Kap ν) (1, blk (Lam ν) (D.c, blk ν (1, 1))) = blk (Kap ν) (1, blk (Lam ν) (D.c, 1))
  rw [blk_one_one])

theorem a₁G_pow_three : D.a₁G ^ 3 = 1 := by
  rw [← D.ΦG_c, ← map_pow]
  simp only [Prod.pow_mk, D.cG_pow_three, one_pow]
  exact map_one _

theorem a₂G_pow_three : D.a₂G ^ 3 = 1 := by
  rw [← D.ΦG_c', ← map_pow]
  simp only [Prod.pow_mk, D.cG_pow_three, one_pow]
  exact map_one _

@[expose] def Adom : Subgroup (↥D.G2 × (↥D.G2 × ↥D.G2)) :=
  (Subgroup.zpowers D.cG).prod ((Subgroup.zpowers D.cG).prod (Subgroup.zpowers D.cG))

@[expose] def A12dom : Subgroup (↥D.G2 × (↥D.G2 × ↥D.G2)) :=
  (Subgroup.zpowers D.cG).prod ((Subgroup.zpowers D.cG).prod ⊥)

@[expose] def A1dom : Subgroup (↥D.G2 × (↥D.G2 × ↥D.G2)) := Subgroup.zpowers (D.cG, (1, 1))

theorem A1dom_le_A12dom : D.A1dom ≤ D.A12dom := by
  rw [A1dom, Subgroup.zpowers_le]
  exact ⟨Subgroup.mem_zpowers _, Subgroup.one_mem _, Subgroup.one_mem _⟩

theorem A12dom_le_Adom : D.A12dom ≤ D.Adom :=
  Subgroup.prod_mono le_rfl (Subgroup.prod_mono le_rfl bot_le)

theorem isElemAbelian_Adom : IsElemAbelian 3 D.Adom :=
  Lin.isElemAbelian_prod (Lin.isElemAbelian_zpowers D.cG_pow_three)
    (Lin.isElemAbelian_prod (Lin.isElemAbelian_zpowers D.cG_pow_three)
      (Lin.isElemAbelian_zpowers D.cG_pow_three))

theorem orderOf_cG (h3 : (3 : F) ≠ 0) : orderOf D.cG = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime D.cG_pow_three fun h => ne_one_of_rel h3 D.c_rel (congrArg Subtype.val h)

theorem card_Adom (h3 : (3 : F) ≠ 0) : Nat.card D.Adom = 3 ^ 3 := by
  rw [Adom, Lin.card_prod_subgroup, Lin.card_prod_subgroup, Nat.card_zpowers, D.orderOf_cG h3]
  norm_num

theorem card_A12dom (h3 : (3 : F) ≠ 0) : Nat.card D.A12dom = 3 ^ 2 := by
  rw [A12dom, Lin.card_prod_subgroup, Lin.card_prod_subgroup, Nat.card_zpowers, D.orderOf_cG h3,
    Subgroup.card_bot]
  norm_num

theorem card_A1dom (h3 : (3 : F) ≠ 0) : Nat.card D.A1dom = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [A1dom, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · simp [D.cG_pow_three]
  · intro h
    exact ne_one_of_rel h3 D.c_rel (congrArg Subtype.val (congrArg Prod.fst h))

@[expose] noncomputable def Asub : Subgroup D.XD := D.Adom.map (D.πD.comp D.ΦG)

@[expose] noncomputable def A12sub : Subgroup D.XD := D.A12dom.map (D.πD.comp D.ΦG)

@[expose] noncomputable def A1sub : Subgroup D.XD := D.A1dom.map (D.πD.comp D.ΦG)

theorem A1sub_eq : D.A1sub = Subgroup.zpowers (D.πD D.a₁G) := by
  rw [A1sub, A1dom, MonoidHom.map_zpowers, MonoidHom.comp_apply, ΦG_c]

theorem A1sub_le_A12sub : D.A1sub ≤ D.A12sub := Subgroup.map_mono D.A1dom_le_A12dom

theorem A12sub_le_Asub : D.A12sub ≤ D.Asub := Subgroup.map_mono D.A12dom_le_Adom

@[expose] noncomputable def Jt : Subgroup ↥D.Gt := (blkRange (F := F) (ι := Kap ν)).subgroupOf D.Gt

@[expose] noncomputable def Jsub : Subgroup D.XD := D.Jt.map D.πD

@[expose] noncomputable def J2t : Subgroup ↥D.Gt :=
  ((blkRange (F := F) (ι := Lam ν)).map ((blk (Kap ν)).comp (MonoidHom.inr _ _))).subgroupOf D.Gt

@[expose] noncomputable def J2sub : Subgroup D.XD := D.J2t.map D.πD

@[expose] noncomputable def βk : ↥D.Gk →* ↥D.Gt :=
  (((blk (Kap ν)).comp (MonoidHom.inr _ _)).comp D.Gk.subtype).codRestrict D.Gt fun Y =>
    D.blk_top 1 (one_mem _) Y Y.2

theorem βk_injective : Function.Injective D.βk := fun _ _ h =>
  Subtype.ext (blkInr_injective (congrArg Subtype.val h))

theorem range_βk : D.βk.range = D.Jt := by
  ext y
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, rfl⟩
  · rintro ⟨Y, hY⟩
    have hYk : Y ∈ D.Gk := D.top_inv Y (by
      rw [show blk (Kap ν) (1, Y) = (y : SpecialLinearGroup (Lin.Top ν) F) from hY]
      exact y.2)
    exact ⟨⟨Y, hYk⟩, Subtype.ext hY⟩

@[expose] noncomputable def βl : ↥D.Gl →* ↥D.Gt :=
  (((blk (Kap ν)).comp (MonoidHom.inr _ _)).comp (((blk (Lam ν)).comp (MonoidHom.inr _ _)).comp
    D.Gl.subtype)).codRestrict D.Gt fun R =>
      D.blk_top 1 (one_mem _) _ (D.blk_kap 1 (one_mem _) R R.2)

theorem βl_injective : Function.Injective D.βl := fun _ _ h =>
  Subtype.ext (blkInr_injective (blkInr_injective (congrArg Subtype.val h)))

theorem range_βl : D.βl.range = D.J2t := by
  ext y
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨_, ⟨R, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨R, rfl⟩, hy⟩
    have hk : blk (Lam ν) (1, R) ∈ D.Gk := D.top_inv _ (by
      rw [show blk (Kap ν) (1, blk (Lam ν) (1, R)) = (y : SpecialLinearGroup (Lin.Top ν) F) from hy]
      exact y.2)
    exact ⟨⟨R, D.kap_inv R hk⟩, Subtype.ext hy⟩

theorem J2t_le_Jt : D.J2t ≤ D.Jt := by
  rintro y ⟨Z, -, hZ⟩
  exact ⟨Z, hZ⟩

theorem J2sub_le_Jsub : D.J2sub ≤ D.Jsub := Subgroup.map_mono D.J2t_le_Jt

section NoThree

variable (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1)
include hZ3

theorem ker_Adom : ∀ x ∈ D.Adom, (D.πD.comp D.ΦG) x = 1 → x = 1 := by
  intro x hx h1
  have hc : D.ΦG x ∈ D.Zt := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : D.ΦG x ^ 3 = 1 := by rw [← map_pow, D.isElemAbelian_Adom.2 x hx, map_one]
  exact D.ΦG_injective (by rw [hZ3 _ hc h3, map_one])

theorem card_Asub (h3 : (3 : F) ≠ 0) : Nat.card D.Asub = 3 ^ 3 := by
  rw [Asub, card_map_eq_of_ker _ _ (D.ker_Adom hZ3), D.card_Adom h3]

theorem card_A12sub (h3 : (3 : F) ≠ 0) : Nat.card D.A12sub = 3 ^ 2 := by
  rw [A12sub, card_map_eq_of_ker _ _ fun x hx => D.ker_Adom hZ3 x (D.A12dom_le_Adom hx),
    D.card_A12dom h3]

theorem card_A1sub (h3 : (3 : F) ≠ 0) : Nat.card D.A1sub = 3 := by
  rw [A1sub, card_map_eq_of_ker _ _ fun x hx =>
    D.ker_Adom hZ3 x (D.A12dom_le_Adom (D.A1dom_le_A12dom hx)), D.card_A1dom h3]

end NoThree

theorem ker_Jt : ∀ y ∈ D.Jt, D.πD y = 1 → y = 1 := by
  rintro y ⟨Y, hY⟩ h1
  replace hY : blk (Kap ν) (1, Y) = (y : SpecialLinearGroup (Lin.Top ν) F) := hY
  have hc : (y : SpecialLinearGroup (Lin.Top ν) F) ∈ Subgroup.center _ :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  rw [← hY] at hc
  have hY1 : Y = 1 := eq_one_of_blk_one_mem_center (ι := Kap ν) (Y := Y) hc
  apply Subtype.ext
  rw [← hY, hY1, blk_one_one]
  rfl

theorem isQuasisimple_Jt (hk : CFSG.Open.IsQuasisimple ↥D.Gk) :
    CFSG.Open.IsQuasisimple ↥D.Jt :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    ((MulEquiv.subgroupCongr D.range_βk).symm.trans (MonoidHom.ofInjective D.βk_injective).symm) hk

theorem isQuasisimple_Jsub (hk : CFSG.Open.IsQuasisimple ↥D.Gk) :
    CFSG.Open.IsQuasisimple ↥D.Jsub :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapEquivOfKer D.πD _ D.ker_Jt) (D.isQuasisimple_Jt hk)

theorem blk_mem_Gk {P : SpecialLinearGroup (Fin 2) F} (hP : P ∈ D.G2) :
    blk (Lam ν) (P, 1) ∈ D.Gk := D.blk_kap P hP 1 (one_mem _)

theorem three_dvd_Jt [Finite F] : 3 ∣ Nat.card (↥D.Jt ⧸ Subgroup.center ↥D.Jt) := by
  have hmem : ∀ Y, D.βk Y ∈ D.Jt := fun Y => D.range_βk ▸ ⟨Y, rfl⟩
  refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
    Nat.prime_three (hmem ⟨_, D.blk_mem_Gk D.c_mem⟩) (hmem ⟨_, D.blk_mem_Gk D.w_mem⟩) ?_ ?_
  · rw [← map_pow]
    have : (⟨_, D.blk_mem_Gk D.c_mem⟩ : ↥D.Gk) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, Prod.pow_mk, D.c_pow_three, one_pow]
      exact blk_one_one)
    rw [this, map_one]
  · intro h
    have h2 : D.βk (⟨_, D.blk_mem_Gk D.c_mem⟩ * ⟨_, D.blk_mem_Gk D.w_mem⟩) =
        D.βk (⟨_, D.blk_mem_Gk D.w_mem⟩ * ⟨_, D.blk_mem_Gk D.c_mem⟩) := by
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
  have hg : ((g : ↥D.Gt) : SpecialLinearGroup (Lin.Top ν) F) * blk (Kap ν) (D.c, 1) =
      blk (Kap ν) (D.c, 1) * (g : ↥D.Gt) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  exact conj_mem_blkRange' h3 D.c_rel hg hn

theorem isSubnormal_Jt (h3 : (3 : F) ≠ 0) :
    CFSG.Open.IsSubnormal D.Jt (Subgroup.centralizer ({D.a₁G} : Set ↥D.Gt)) :=
  CFSG.Open.IsSubnormal.step D.Jt_le_centralizer (D.Jt_normal h3) (CFSG.Open.IsSubnormal.refl _)

section NoThree

variable (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1)
include hZ3

theorem glaPComponent_J [Finite F] (h3 : (3 : F) ≠ 0) (hk : CFSG.Open.IsQuasisimple ↥D.Gk) :
    GLAPComponent 3 (Subgroup.centralizer ((D.A1sub : Subgroup D.XD) : Set D.XD)) D.Jsub := by
  rw [D.A1sub_eq, centralizer_zpowers_eq, Jsub,
    centralizer_mk_eq _ D.Zt_le_center hZ3 D.a₁G_pow_three]
  refine (CFSG.glaPComponent_map_bijective_of_ker_le_center Nat.prime_three D.πD ?_).1 _ ?_
  · rintro y ⟨-, hy⟩ x -
    rw [QuotientGroup.ker_mk'] at hy
    exact Subgroup.mem_center_iff.1 (D.Zt_le_center hy) x
  · exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three
      (D.isSubnormal_Jt h3) (D.isQuasisimple_Jt hk) D.three_dvd_Jt

end NoThree

theorem Asub_le_normalizer (h3 : (3 : F) ≠ 0) :
    D.Asub ≤ Subgroup.normalizer ((D.Jsub : Subgroup D.XD) : Set D.XD) := by
  rintro _ ⟨x, hx, rfl⟩
  have hc : D.ΦG x ∈ Subgroup.centralizer ({D.a₁G} : Set ↥D.Gt) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← D.ΦG_c, ← map_mul, ← map_mul]
    exact congrArg D.ΦG (congrArg Subtype.val
      (D.isElemAbelian_Adom.1.is_comm.comm ⟨x, hx⟩
        ⟨_, ⟨Subgroup.mem_zpowers _, Subgroup.one_mem _, Subgroup.one_mem _⟩⟩))
  haveI := D.Jt_normal h3
  exact Subgroup.le_normalizer_map D.πD
    ⟨_, Subgroup.le_normalizer_of_normal_subgroupOf D.Jt_le_centralizer hc, rfl⟩

theorem commute_of_mk {P₀ : SpecialLinearGroup (Fin 2) F} {Y Y₀ : SpecialLinearGroup (Kap ν) F}
    (hY : blk (Kap ν) (1, Y) ∈ D.Gt) (hφ : blk (Kap ν) (P₀, Y₀) ∈ D.Gt)
    (h : D.πD ⟨_, hφ⟩ * D.πD ⟨_, hY⟩ = D.πD ⟨_, hY⟩ * D.πD ⟨_, hφ⟩) : Y * Y₀ = Y₀ * Y := by
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [← map_mul, ← map_mul, ← map_inv, ← map_mul] at h
  have e : ((P₀, Y₀) * (1, Y))⁻¹ * ((1, Y) * (P₀, Y₀)) =
      ((1 : SpecialLinearGroup (Fin 2) F), (Y₀ * Y)⁻¹ * (Y * Y₀)) :=
    Prod.ext (by simp) rfl
  rw [e] at h
  have e' : (Y₀ * Y)⁻¹ * (Y * Y₀) = 1 := eq_one_of_blk_one_mem_center h
  rw [inv_mul_eq_one] at e'
  exact e'.symm

theorem centMod_Asub [Finite F] (hk : CFSG.Open.IsQuasisimple ↥D.Gk) :
    ∀ x ∈ D.Asub, CentMod 3 D.Jsub x → x ∈ D.A1sub := by
  rintro _ ⟨⟨P₀, Q₀, R₀⟩, hy, rfl⟩ hc
  have hcent := mem_centralizer_of_centMod (D.isQuasisimple_Jsub hk) D.three_dvd_Jsub hc
  set Y₀ : SpecialLinearGroup (Kap ν) F := blk (Lam ν) (Q₀, blk ν (R₀, 1)) with hY₀
  have hφ : blk (Kap ν) ((P₀ : SpecialLinearGroup (Fin 2) F), Y₀) ∈ D.Gt := (D.ΦG (P₀, Q₀, R₀)).2
  have hcomm : ∀ Y ∈ D.Gk, Y * Y₀ = Y₀ * Y := fun Y hYk => by
    have hY : blk (Kap ν) (1, Y) ∈ D.Gt := D.blk_top 1 (one_mem _) Y hYk
    refine D.commute_of_mk hY hφ ?_
    exact (Subgroup.mem_centralizer_iff.1 hcent _ ⟨⟨_, hY⟩, ⟨Y, rfl⟩, rfl⟩).symm
  have hQ : Q₀ * D.wG = D.wG * Q₀ := by
    have e := hcomm _ (D.blk_mem_Gk D.w_mem)
    rw [hY₀, ← map_mul, ← map_mul] at e
    exact Subtype.ext (congrArg Prod.fst (blk_injective e)).symm
  have hR : R₀ * D.wG = D.wG * R₀ := by
    have e := hcomm _ (D.blk_kap 1 (one_mem _) _ (D.blk_lam _ D.w_mem))
    rw [hY₀, ← map_mul, ← map_mul] at e
    have e2 := congrArg Prod.snd (blk_injective e)
    simp only [Prod.snd_mul, ← map_mul] at e2
    exact Subtype.ext (congrArg Prod.fst (blk_injective e2)).symm
  have hQ1 : Q₀ = 1 :=
    eq_one_of_mem_zpowers_of_commute D.cG_pow_three D.cG_mul_wG hy.2.1 hQ
  have hR1 : R₀ = 1 :=
    eq_one_of_mem_zpowers_of_commute D.cG_pow_three D.cG_mul_wG hy.2.2 hR
  subst hQ1 hR1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hy.1
  replace hm : D.cG ^ m = P₀ := hm
  have e : (D.cG, ((1 : ↥D.G2), (1 : ↥D.G2))) ^ m = (P₀, (1, 1)) := by
    rw [← hm]
    ext : 1 <;> simp
  exact ⟨_, Subgroup.zpow_mem_zpowers _ m, by rw [e]⟩

theorem J2sub_le_centralizer :
    D.J2sub ≤ Subgroup.centralizer ((D.A12sub : Subgroup D.XD) : Set D.XD) := by
  rintro _ ⟨y, ⟨_, ⟨R, rfl⟩, hy⟩, rfl⟩
  replace hy : blk (Kap ν) (1, blk (Lam ν) (1, R)) = (y : SpecialLinearGroup (Lin.Top ν) F) := hy
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨⟨P, Q, R'⟩, hz, rfl⟩
  have hR' : R' = 1 := Subgroup.mem_bot.1 hz.2.2
  subst hR'
  rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hy, coe_ΦG]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
  change blk (Kap ν) (P, blk (Lam ν) (Q, blk ν (1, 1))) * blk (Kap ν) (1, blk (Lam ν) (1, R)) =
    blk (Kap ν) (1, blk (Lam ν) (1, R)) * blk (Kap ν) (P, blk (Lam ν) (Q, blk ν (1, 1)))
  rw [blk_one_one, ← map_mul, ← map_mul]
  congr 1
  ext : 1
  · simp
  · simp only [Prod.snd_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    ext : 1 <;> simp

section NoThree

variable (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1)
include hZ3

theorem J2sub_normal (h3 : (3 : F) ≠ 0) :
    (D.J2sub.subgroupOf (D.Jsub ⊓
      Subgroup.centralizer ((D.A12sub : Subgroup D.XD) : Set D.XD))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hgJ, hgC⟩ := g.2
  obtain ⟨y₀, ⟨Y, hY₀⟩, hgY⟩ := hgJ
  have ha₂ : D.πD D.a₂G ∈ D.A12sub :=
    ⟨(1, (D.cG, 1)), ⟨Subgroup.one_mem _, Subgroup.mem_zpowers _, Subgroup.one_mem _⟩, by
      rw [MonoidHom.comp_apply, ΦG_c']⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 hgC _ ha₂
  rw [← hgY] at hcomm
  have hlift := mem_centralizer_of_mk_mem _ D.Zt_le_center hZ3 D.a₂G_pow_three
    (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have hY : Y * blk (Lam ν) (D.c, 1) = blk (Lam ν) (D.c, 1) * Y := by
    have hY₀' : blk (Kap ν) (1, Y) = (y₀ : SpecialLinearGroup (Lin.Top ν) F) := hY₀
    have e := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hlift)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hY₀'] at e
    change blk (Kap ν) (1, Y) * blk (Kap ν) (1, blk (Lam ν) (D.c, 1)) =
      blk (Kap ν) (1, blk (Lam ν) (D.c, 1)) * blk (Kap ν) (1, Y) at e
    rw [← map_mul, ← map_mul] at e
    simpa using congrArg Prod.snd (blk_injective e)
  obtain ⟨n₀, ⟨Z, hZ, hZn⟩, hnR⟩ := hn
  have hconj := conj_mem_blkRange' h3 D.c_rel hY hZ
  refine ⟨y₀ * n₀ * y₀⁻¹, ⟨Y * Z * Y⁻¹, hconj, ?_⟩, ?_⟩
  · simp only [map_mul, map_inv]
    rw [hY₀, hZn]
  · simp only [map_mul, map_inv]
    rw [hgY, hnR]
    rfl

end NoThree

theorem ker_J2t : ∀ y ∈ D.J2t, D.πD y = 1 → y = 1 := fun y hy => D.ker_Jt y (D.J2t_le_Jt hy)

theorem isQuasisimple_J2sub (hl : CFSG.Open.IsQuasisimple ↥D.Gl) :
    CFSG.Open.IsQuasisimple ↥D.J2sub :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    ((mapEquivOfKer D.πD _ D.ker_J2t).trans
      ((MulEquiv.subgroupCongr D.range_βl).symm.trans (MonoidHom.ofInjective D.βl_injective).symm))
    hl

theorem three_dvd_J2sub [Finite F] : 3 ∣ Nat.card (↥D.J2sub ⧸ Subgroup.center ↥D.J2sub) := by
  have hinj : Function.Injective (D.πD.comp D.βl) := by
    rw [injective_iff_map_eq_one]
    intro R hR
    exact D.βl_injective ((D.ker_J2t _ (D.range_βl ▸ ⟨R, rfl⟩) hR).trans (map_one _).symm)
  have hmem : ∀ R, (D.πD.comp D.βl) R ∈ D.J2sub := fun R => ⟨_, D.range_βl ▸ ⟨R, rfl⟩, rfl⟩
  refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
    Nat.prime_three (hmem ⟨_, D.blk_lam _ D.c_mem⟩) (hmem ⟨_, D.blk_lam _ D.w_mem⟩) ?_ ?_
  · rw [← map_pow]
    have : (⟨_, D.blk_lam _ D.c_mem⟩ : ↥D.Gl) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, Prod.pow_mk, D.c_pow_three, one_pow]
      exact blk_one_one)
    rw [this, map_one]
  · intro h
    have h2 : (D.πD.comp D.βl) (⟨_, D.blk_lam _ D.c_mem⟩ * ⟨_, D.blk_lam _ D.w_mem⟩) =
        (D.πD.comp D.βl) (⟨_, D.blk_lam _ D.w_mem⟩ * ⟨_, D.blk_lam _ D.c_mem⟩) := by
      rw [map_mul, map_mul]
      exact h
    have h' := congrArg Subtype.val (hinj h2)
    simp only [Subgroup.coe_mul, ← map_mul] at h'
    exact D.c_mul_w (congrArg Prod.fst (blk_injective h'))

theorem layer_ne_bot [Finite F] (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1) (h3 : (3 : F) ≠ 0)
    (hl : CFSG.Open.IsQuasisimple ↥D.Gl) :
    GLAPLayer 3 (D.Jsub ⊓
      Subgroup.centralizer ((D.A12sub : Subgroup D.XD) : Set D.XD)) ≠ ⊥ :=
  CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three
    (le_inf D.J2sub_le_Jsub D.J2sub_le_centralizer) (D.J2sub_normal hZ3 h3)
    (D.isQuasisimple_J2sub hl) D.three_dvd_J2sub

@[expose] noncomputable def tGt : ↥D.Gt :=
  ⟨blk (Kap ν) (negOne, 1), D.blk_top _ D.negOne_mem _ (one_mem _)⟩

theorem t_ne_one [Finite F] (h2 : (2 : F) ≠ 0) : D.πD D.tGt ≠ 1 := fun h =>
  tG_not_mem_center ν h2 (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))

theorem t_sq [Finite F] : D.πD D.tGt ^ 2 = 1 := by
  rw [← map_pow]
  have : D.tGt ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    change blk (Kap ν) (negOne, 1) ^ 2 = 1
    rw [← map_pow, Prod.pow_mk, negOne_sq, one_pow, blk_one_one])
  rw [this, map_one]

theorem Jsub_le_centralizer_t :
    D.Jsub ≤ Subgroup.centralizer ({D.πD D.tGt} : Set D.XD) := by
  rintro _ ⟨y, ⟨Y, hY⟩, rfl⟩
  replace hY : blk (Kap ν) (1, Y) = (y : SpecialLinearGroup (Lin.Top ν) F) := hY
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hY]
  change blk (Kap ν) (1, Y) * blk (Kap ν) (negOne, 1) = blk (Kap ν) (negOne, 1) * blk (Kap ν) (1, Y)
  rw [← map_mul, ← map_mul]
  congr 1
  ext : 1 <;> simp

theorem Asub_le_centralizer_t [Finite F] :
    D.Asub ≤ Subgroup.centralizer ({D.πD D.tGt} : Set D.XD) := by
  rintro _ ⟨⟨P, Q, R⟩, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_ΦG]
  change blk (Kap ν) ((P : SpecialLinearGroup (Fin 2) F), _) * blk (Kap ν) (negOne, 1) =
    blk (Kap ν) (negOne, 1) * blk (Kap ν) ((P : SpecialLinearGroup (Fin 2) F), _)
  rw [← map_mul, ← map_mul]
  congr 1
  ext : 1
  · exact (negOne_mul_comm (P : SpecialLinearGroup (Fin 2) F)).symm
  · simp

theorem modelA [Finite F] (h3 : (3 : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    (hk : CFSG.Open.IsQuasisimple ↥D.Gk) (hl : CFSG.Open.IsQuasisimple ↥D.Gl)
    (hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1) : ModelA D.XD :=
  ⟨D.Asub, D.A1sub, D.A12sub, D.Jsub, D.πD D.tGt,
    CFSG.SectionRank.isElemAbelian_map D.isElemAbelian_Adom _, D.card_Asub hZ3 h3,
    D.A1sub_le_A12sub, D.A12sub_le_Asub, D.card_A1sub hZ3 h3, D.card_A12sub hZ3 h3,
    D.glaPComponent_J hZ3 h3 hk, D.Asub_le_normalizer h3, D.centMod_Asub hk,
    D.layer_ne_bot hZ3 h3 hl, D.t_ne_one h2, D.t_sq, D.Jsub_le_centralizer_t,
    D.Asub_le_centralizer_t⟩

end FormData

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form

end
