module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Model
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Transv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X8

public section

noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48

abbrev KF : Type := CFSG.RankThree.PartTwo.KFacts.KS21.U58.K

theorem hKF : UnitaryFieldData 2 3 KF := CFSG.RankThree.PartTwo.KFacts.KS21.U58.hK

theorem bar_pow (c : KF) : hKF.bar c = c ^ 8 :=
  CFSG.RankThree.PartTwo.KFacts.KS21.U58.bar_eq_pow c

theorem bar_map (φ : KF ≃+* KF) (c : KF) : hKF.bar (φ c) = φ (hKF.bar c) := by
  rw [bar_pow, bar_pow, map_pow]

theorem SU4_eq_gramSU' :
    CFSG.LieType.Universal.Unitary.SUid σ4 4 =
      CFSG.ClassicalGroups.UnitaryFlag.gramSU hKF (1 : Matrix (Fin 4) (Fin 4) KF) := by
  rw [SU4_eq_gramSU, Units.val_one]

theorem SU4_unitary (g : SU4) :
    (((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF).map hKF.bar)ᵀ *
      ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = 1 := by
  have hg : (g : GL (Fin 4) KF) ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU hKF
      (1 : Matrix (Fin 4) (Fin 4) KF) := by
    rw [← SU4_eq_gramSU']
    exact g.2
  have h1 := (CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU.1 hg).1
  simpa [Matrix.mul_one] using h1

@[expose] def Fv (φ : KF ≃+* KF) (w : Fin 4 → KF) : Fin 4 → KF := fun i => φ (w i)

theorem Fv_ne_zero (φ : KF ≃+* KF) {w : Fin 4 → KF} (hw : w ≠ 0) : Fv φ w ≠ 0 := by
  intro h
  apply hw
  ext i
  have := congrFun h i
  simpa [Fv] using this

theorem tvMat_map (φ : KF ≃+* KF) (w : Fin 4 → KF) (c : KF) :
    (tvMat hKF w c).map φ = tvMat hKF (Fv φ w) (φ c) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [tvMat, wMat, Fv, bar_map]
  · simp [tvMat, wMat, Fv, bar_map, hij]

theorem vnorm_Fv (φ : KF ≃+* KF) (w : Fin 4 → KF) : vnorm hKF (Fv φ w) = φ (vnorm hKF w) := by
  simp [vnorm, Fv, bar_map, map_sum, map_mul]

theorem vnorm_eq_dotB (w : Fin 4 → KF) :
    vnorm hKF w = CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8.dotB hKF w w := by
  simp [vnorm, CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8.dotB, mul_comm]

theorem vnorm_mulVec (g : GL (Fin 4) KF)
    (hg : ((g : Matrix (Fin 4) (Fin 4) KF).map hKF.bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) KF) = 1)
    (u : Fin 4 → KF) :
    vnorm hKF ((g : Matrix (Fin 4) (Fin 4) KF) *ᵥ u) = vnorm hKF u := by
  rw [vnorm_eq_dotB, vnorm_eq_dotB]
  exact CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8.dotB_act hKF hg u u

theorem tvMat_add (w : Fin 4 → KF) (hw : vnorm hKF w = 0) (c d : KF) :
    tvMat hKF w c * tvMat hKF w d = tvMat hKF w (c + d) := by
  have hWW : wMat hKF w * wMat hKF w = 0 := by
    rw [wMat_mul_wMat, hw, zero_smul]
  unfold tvMat
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hWW, smul_zero, add_zero, zero_add, add_smul]
  abel

theorem tvMat_zero (w : Fin 4 → KF) : tvMat hKF w 0 = 1 := by
  simp [tvMat]

theorem wMat_ne_zero {w : Fin 4 → KF} (hw : w ≠ 0) : wMat hKF w ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (funext hc)
  have h1 := congrFun (congrFun h i) i
  simp only [wMat, Matrix.of_apply, Matrix.zero_apply] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact hi h2
  · rw [bar_pow] at h2
    exact hi (by simpa using h2)

@[expose] def rootGL (w : Fin 4 → KF) (hw : vnorm hKF w = 0) : Subgroup (GL (Fin 4) KF) where
  carrier := {g | ∃ c : KF, hKF.bar c = c ∧ (g : Matrix (Fin 4) (Fin 4) KF) = tvMat hKF w c}
  mul_mem' := by
    rintro _ _ ⟨c, hc, hgc⟩ ⟨d, hd, hgd⟩
    refine ⟨c + d, by rw [map_add, hc, hd], ?_⟩
    rw [Units.val_mul, hgc, hgd, tvMat_add w hw]
  one_mem' := ⟨0, map_zero _, by rw [Units.val_one, tvMat_zero]⟩
  inv_mem' := by
    rintro g ⟨c, hc, hgc⟩
    refine ⟨-c, by rw [map_neg, hc], ?_⟩
    have h1 : ((g⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) * (g : Matrix (Fin 4) (Fin 4) KF) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (g : Matrix (Fin 4) (Fin 4) KF) * tvMat hKF w (-c) = 1 := by
      rw [hgc]
      exact tvMat_mul_tvMat hKF w c hw
    calc ((g⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF)
        = ((g⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
            ((g : Matrix (Fin 4) (Fin 4) KF) * tvMat hKF w (-c)) := by rw [h2, mul_one]
      _ = (((g⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) * (g : Matrix (Fin 4) (Fin 4) KF)) *
            tvMat hKF w (-c) := by rw [Matrix.mul_assoc]
      _ = tvMat hKF w (-c) := by rw [h1, Matrix.one_mul]

@[expose] def rootSU (w : Fin 4 → KF) (hw : vnorm hKF w = 0) : Subgroup SU4 :=
  (rootGL w hw).comap (CFSG.LieType.Universal.Unitary.SUid σ4 4).subtype

theorem mem_rootSU {w : Fin 4 → KF} {hw : vnorm hKF w = 0} {x : SU4} :
    x ∈ rootSU w hw ↔ ∃ c : KF, hKF.bar c = c ∧
      ((x : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = tvMat hKF w c :=
  Iff.rfl

@[expose] def tvSU (w : Fin 4 → KF) (hw : vnorm hKF w = 0) (c : KF) (hc : hKF.bar c = c) : SU4 :=
  ⟨tvGL hKF w c hw, by
    rw [SU4_eq_gramSU']
    exact tvGL_mem hKF hw hc⟩

theorem coe_tvSU (w : Fin 4 → KF) (hw : vnorm hKF w = 0) (c : KF) (hc : hKF.bar c = c) :
    (((tvSU w hw c hc : SU4) : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = tvMat hKF w c :=
  coe_tvGL hKF w c hw

theorem tvSU_mem (w : Fin 4 → KF) (hw : vnorm hKF w = 0) (c : KF) (hc : hKF.bar c = c) :
    tvSU w hw c hc ∈ rootSU w hw :=
  mem_rootSU.2 ⟨c, hc, coe_tvSU w hw c hc⟩

theorem card_rootSU {w : Fin 4 → KF} (hw : IsIsoVec hKF w) : Nat.card (rootSU w hw.2) = 8 := by
  have hcard : Nat.card hKF.fixedField = 8 := by
    rw [UnitaryFieldData.card_fixedField hKF]
    norm_num
  rw [← hcard]
  let f : hKF.fixedField → rootSU w hw.2 := fun c =>
    ⟨tvSU w hw.2 c.1 ((hKF.mem_fixedField).1 c.2), tvSU_mem w hw.2 c.1 ((hKF.mem_fixedField).1 c.2)⟩
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    have h1 : tvMat hKF w c = tvMat hKF w d := by
      have := congrArg (fun x : rootSU w hw.2 =>
        (((x : SU4) : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF)) hcd
      simpa [f, coe_tvSU] using this
    have h2 : (c - d) • wMat hKF w = 0 := by
      have h3 : c • wMat hKF w = d • wMat hKF w := by
        have := congrArg (fun M : Matrix (Fin 4) (Fin 4) KF => M - 1) h1
        simpa [tvMat, sub_eq_add_neg] using this
      rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.1 h2 with h4 | h4
    · have : c = d := sub_eq_zero.1 h4
      subst this
      rfl
    · exact absurd h4 (wMat_ne_zero hw.1)
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc, hxc⟩ := mem_rootSU.1 hx
    refine ⟨⟨c, (hKF.mem_fixedField).2 hc⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact (coe_tvSU w hw.2 c hc).trans hxc.symm

theorem sq_rootSU {w : Fin 4 → KF} {hw : vnorm hKF w = 0} {x : SU4} (hx : x ∈ rootSU w hw) :
    x ^ 2 = 1 := by
  haveI : CharP KF 2 := hKF.charP
  obtain ⟨c, hc, hxc⟩ := mem_rootSU.1 hx
  have h2 : c + c = 0 := CharTwo.add_self_eq_zero c
  have hm : ((x : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((x : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = 1 := by
    rw [hxc, tvMat_add w hw c c, h2, tvMat_zero]
  have hGL : (x : GL (Fin 4) KF) ^ 2 = 1 := Units.ext (by
    rw [pow_two, Units.val_mul, hm, Units.val_one])
  exact Subtype.ext (by simpa using hGL)

@[expose] def e4 : SU4 ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 3 KF 4 :=
  MulEquiv.subgroupCongr (SU4_eq_gramSU'.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU hKF 4).symm)

theorem cenIn_rootSU {w : Fin 4 → KF} (hw : IsIsoVec hKF w) {x : SU4} (hx : x ∈ rootSU w hw.2)
    (hx1 : x ≠ 1) : CenIn 2 x := by
  haveI : CharP KF 2 := hKF.charP
  obtain ⟨c, hc, hxc⟩ := mem_rootSU.1 hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    apply Units.ext
    simp [hxc, tvMat_zero]
  have h1 : CenIn 2 (e4 x) :=
    (cenIn_two_iff hKF (e4 x)).2 (Or.inr ⟨w, c, hw, hc0, hc, hxc⟩)
  have h2 := CenIn.congr e4.symm h1
  rwa [MulEquiv.symm_apply_apply] at h2

theorem rootSU_smul {w : Fin 4 → KF} (hw : vnorm hKF w = 0) {μ : KF} (hμ : μ ≠ 0)
    (hμw : vnorm hKF (μ • w) = 0) : rootSU (μ • w) hμw = rootSU w hw := by
  have hN : hKF.bar (μ * hKF.bar μ) = μ * hKF.bar μ := by
    rw [map_mul, hKF.bar_bar, mul_comm]
  have hN0 : μ * hKF.bar μ ≠ 0 :=
    mul_ne_zero hμ (by rw [bar_pow]; exact pow_ne_zero _ hμ)
  ext x
  rw [mem_rootSU, mem_rootSU]
  constructor
  · rintro ⟨c, hc, hxc⟩
    refine ⟨c * (μ * hKF.bar μ), by rw [map_mul, hc, hN], ?_⟩
    rw [hxc, tvMat_smul_vec]
  · rintro ⟨c, hc, hxc⟩
    refine ⟨c * (μ * hKF.bar μ)⁻¹, by rw [map_mul, hc, map_inv₀, hN], ?_⟩
    rw [hxc, tvMat_smul_vec, inv_mul_cancel_right₀ hN0]

@[expose] def sF (g : SU4) (φ : KF ≃+* KF) (w : Fin 4 → KF) : Fin 4 → KF :=
  ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *ᵥ Fv φ w

theorem sF_ne_zero (g : SU4) (φ : KF ≃+* KF) {w : Fin 4 → KF} (hw : w ≠ 0) : sF g φ w ≠ 0 := by
  intro h
  apply Fv_ne_zero φ hw
  have h1 : (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = 1 := Units.inv_mul _
  have h2 : (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *ᵥ
      (((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *ᵥ Fv φ w) = Fv φ w := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [← h2]
  change (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *ᵥ sF g φ w = 0
  rw [h, Matrix.mulVec_zero]

theorem isIsoVec_sF (g : SU4) (φ : KF ≃+* KF) {w : Fin 4 → KF} (hw : IsIsoVec hKF w) :
    IsIsoVec hKF (sF g φ w) := by
  refine ⟨sF_ne_zero g φ hw.1, ?_⟩
  rw [sF, vnorm_mulVec _ (SU4_unitary g), vnorm_Fv, hw.2, map_zero]

theorem coe_semilinear (g : SU4) (φ : KF ≃+* KF) (y : SU4) :
    (((g : GL (Fin 4) KF) * glAut φ (y : GL (Fin 4) KF) * (g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) :
      Matrix (Fin 4) (Fin 4) KF) =
    ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((y : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF).map φ *
      (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) := by
  rw [Units.val_mul, Units.val_mul, coe_glAut]

theorem conj_tvMat (g : SU4) (u : Fin 4 → KF) (c : KF) :
    ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) * tvMat hKF u c *
      (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) =
    tvMat hKF (((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *ᵥ u) c := by
  rw [mul_tvMat_eq hKF _ (SU4_unitary g) u c, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem rootSU_map (α : MulAut SU4) (g : SU4) (φ : KF ≃+* KF)
    (hα : ∀ x : SU4, ((α x : SU4) : GL (Fin 4) KF) =
      (g : GL (Fin 4) KF) * glAut φ (x : GL (Fin 4) KF) * (g : GL (Fin 4) KF)⁻¹)
    {w : Fin 4 → KF} (hw : IsIsoVec hKF w) :
    (rootSU w hw.2).map α.toMonoidHom = rootSU (sF g φ w) (isIsoVec_sF g φ hw).2 := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hyc⟩ := mem_rootSU.1 hy
    refine mem_rootSU.2 ⟨φ c, by rw [bar_map, hc], ?_⟩
    change (((α y : SU4) : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = _
    rw [hα y, coe_semilinear, hyc, tvMat_map, conj_tvMat]
    rfl
  · intro hx
    obtain ⟨d, hd, hxd⟩ := mem_rootSU.1 hx
    have hc : hKF.bar (φ.symm d) = φ.symm d := by rw [bar_map, hd]
    refine ⟨tvSU w hw.2 (φ.symm d) hc, tvSU_mem w hw.2 _ hc, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (((α (tvSU w hw.2 (φ.symm d) hc) : SU4) : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = _
    rw [hα, coe_semilinear, coe_tvSU, tvMat_map, conj_tvMat, RingEquiv.apply_symm_apply, hxd]
    rfl

end CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R
