module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Anti

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal val_of_mem_scal)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem map_X1 (l : K) : (X1 l).map h.bar = X1 (h.bar l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1]

theorem toSU_smul_mem_scal {c : K} (hd : ((c • 1 : Matrix (Fin 4) (Fin 4) K)).det = 1)
    (hu : uStar h (c • 1 : Matrix (Fin 4) (Fin 4) K) * (c • 1) = 1) :
    toSU h (c • 1 : Matrix (Fin 4) (Fin 4) K) hd hu ∈ scal p f K := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, det_zero] at hd
    exact zero_ne_one hd
  change ((toSU h (c • 1 : Matrix (Fin 4) (Fin 4) K) hd hu : unitarySU p f K 4) : GL (Fin 4) K) ∈
    StatedScalars (Fin 4) K
  refine ⟨Units.mk0 c hc, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_toSU, Units.val_mk0, Matrix.smul_one_eq_diagonal]
  rfl

variable {H : Type} [Group H] [Finite H]

theorem false_of_anti [Finite K] [(generalizedFitting H).Normal] (c : Sp4Rec.Config H)
    (φ : ↥(generalizedFitting H) ≃* StatedProj (StatedSU 4 (p ^ f) K))
    {ρ : H →* MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : ↥(generalizedFitting H), ρ w = MulAut.conj (φ w))
    (hρg : ∀ (g : H) (w : ↥(generalizedFitting H)), ρ g (φ w) = φ (MulAut.conjNormal g w))
    {g₀ : unitarySU p f K 4} {l : K} (hl : h.bar l * l = 1) (hl4 : l ^ 4 = 1)
    (hg₀ : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l)
    (hφb : φ ⟨c.b, c.b_mem_G⟩ = QuotientGroup.mk g₀)
    (hfac : ((c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom = factorUL h ∧
        ((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map φ.toMonoidHom =
          factorUR h) ∨
      ((c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom = factorUR h ∧
        ((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map φ.toMonoidHom =
          factorUL h))
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, ρ c.a (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {z : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      z • 1) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set KP := (c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom with hKP
  set KaP := ((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map φ.toMonoidHom with hKaP
  have ha2 : c.a * c.a = 1 := by rw [← pow_two, ← c.orderOf_a, pow_orderOf_eq_one]
  have hmapK : ∀ y ∈ KP, ρ c.a y ∈ KaP := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hρg]
    refine ⟨MulAut.conjNormal c.a w, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, Sp4Rec.mem_conjugate_iff]
    have hw' : (w : H) ∈ c.K := mem_subgroupOf.mp (SetLike.mem_coe.mp hw)
    have e : c.a * ((MulAut.conjNormal c.a w : generalizedFitting H) : H) * c.a⁻¹ = w := by
      change c.a * (c.a * (w : H) * c.a⁻¹) * c.a⁻¹ = w
      have hai : c.a⁻¹ = c.a := inv_eq_of_mul_eq_one_right ha2
      rw [hai, ← mul_assoc, ← mul_assoc, ha2, one_mul, mul_assoc, ha2, mul_one]
    rw [e]
    exact hw'
  have hmapKa : ∀ y ∈ KaP, ρ c.a y ∈ KP := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hρg]
    refine ⟨MulAut.conjNormal c.a w, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact Sp4Rec.mem_conjugate_iff.mp (mem_subgroupOf.mp (SetLike.mem_coe.mp hw))
  have hLR : ∀ y ∈ factorUL h, ρ c.a y ∈ factorUR h := by
    rcases hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro y hy
      rw [← h1] at hy
      rw [← h2]
      exact hmapK y hy
    · intro y hy
      rw [← h2] at hy
      rw [← h1]
      exact hmapKa y hy
  have hRL : ∀ y ∈ factorUR h, ρ c.a y ∈ factorUL h := by
    rcases hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro y hy
      rw [← h2] at hy
      rw [← h1]
      exact hmapKa y hy
    · intro y hy
      rw [← h1] at hy
      rw [← h2]
      exact hmapK y hy
  have hAAi : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hψA' : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (A : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := by
    intro g
    rw [hψA, Matrix.mul_assoc, hAiA, Matrix.mul_one]
  have hq2 : 2 ≤ p ^ f := by
    have := h.prime.two_le
    exact this.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  obtain ⟨t, ht, ht2⟩ := RankThree.PartOne.KCUnitary.exists_norm_one_sq_ne_one h hq2
  have ht0 : t ≠ 0 := ne_zero_of_norm h ht
  have htinv : t⁻¹ ≠ t := by
    intro e
    apply ht2
    have : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    rw [e] at this
    rw [pow_two]
    exact this
  have hbL : ∀ U : unitarySU p f K 2, ∃ (c' : K) (W : Matrix (Fin 2) (Fin 2) K),
      (A : Matrix (Fin 4) (Fin 4) K) * (bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1).map
        h.bar = c' • bd 1 W * (A : Matrix (Fin 4) (Fin 4) K) := by
    intro U
    have hm := hLR _ ⟨U, rfl⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hψ] at hm
    obtain ⟨c', W, hcW⟩ := exists_smul_bdUR_of_mem h hm
    refine ⟨c', W, ?_⟩
    rw [← coe_bdUL h U, ← hψA', hcW]
  have hbR : ∀ U : unitarySU p f K 2, ∃ (c' : K) (W : Matrix (Fin 2) (Fin 2) K),
      (A : Matrix (Fin 4) (Fin 4) K) * (bd 1 ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map
        h.bar = c' • bd W 1 * (A : Matrix (Fin 4) (Fin 4) K) := by
    intro U
    have hm := hRL _ ⟨U, rfl⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hψ] at hm
    obtain ⟨c', W, hcW⟩ := exists_smul_bdUL_of_mem h hm
    refine ⟨c', W, ?_⟩
    rw [← coe_bdUR h U, ← hψA', hcW]
  have hone : (1 : Matrix (Fin 2) (Fin 2) K).map h.bar = 1 :=
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar)
  have e1 := hbL (dgSU h ht)
  have e2 := hbL (jjSU h)
  have e3 := hbR (dgSU h ht)
  have e4 := hbR (jjSU h)
  rw [coe_dgSU, map_bd, map_dg h ht, hone] at e1
  rw [coe_jjSU, map_bd, map_jj, hone] at e2
  rw [coe_dgSU, map_bd, map_dg h ht, hone] at e3
  rw [coe_jjSU, map_bd, map_jj, hone] at e4
  obtain ⟨h00, h01, h10, h11⟩ := ul_eq_zero_of_swapU htinv e1 e2
  obtain ⟨h22, h23, h32, h33⟩ := lr_eq_zero_of_swapU htinv e3 e4
  obtain ⟨s, hs, hdet⟩ := antiblock_sq h h00 h01 h10 h11 h22 h23 h32 h33 hAu hAA
  set Mm := Mmat s with hMm
  set Xm := (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * Mm with hXm
  have hbb : ∀ Y : Matrix (Fin 4) (Fin 4) K, (Y.map h.bar).map h.bar = Y := fun Y => by
    ext i j
    simp [h.bar_bar]
  have hXdet : Xm.det = 1 := by
    have h1 := congrArg Matrix.det hAiA
    rw [det_mul, det_one, hdet] at h1
    rw [hXm, det_mul, det_Mmat, h1]
  have hXu : uStar h Xm * Xm = 1 := unitary_mul h (unitary_inv h hAu) (unitary_Mmat h hs)
  have hWdet : (Xm.map h.bar).det = 1 := by
    have e : (Xm.map h.bar).det = h.bar Xm.det := by
      rw [RingHom.map_det]
      rfl
    rw [e, hXdet, map_one]
  have hWu : uStar h (Xm.map h.bar) * Xm.map h.bar = 1 := by
    rw [uStar_map_mul, hXu, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  set W := toSU h (Xm.map h.bar) hWdet hWu with hWdef
  set w := φ.symm (QuotientGroup.mk W) with hw
  set x := c.a * (w : H) with hx
  have hcancel : ∀ Y Z : Matrix (Fin 4) (Fin 4) K, Y * Mm = Z * Mm → Y = Z := by
    intro Y Z hYZ
    have hMu := Mmat_mul_uStar h hs
    calc Y = Y * Mm * uStar h Mm := by rw [Matrix.mul_assoc, hMu, Matrix.mul_one]
      _ = Z * Mm * uStar h Mm := by rw [hYZ]
      _ = Z := by rw [Matrix.mul_assoc, hMu, Matrix.mul_one]
  have key : ∀ g : unitarySU p f K 4, ∃ Y : unitarySU p f K 4,
      ρ x (QuotientGroup.mk g) = QuotientGroup.mk Y ∧
        ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Mm =
          Mm * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := by
    intro g
    refine ⟨ψ (W * g * W⁻¹), ?_, ?_⟩
    · rw [hx, map_mul, MulAut.mul_apply, hρW, hw, MulEquiv.apply_symm_apply, MulAut.conj_apply,
        ← hψ]
      rfl
    · set Wi := (((W⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      have hWiW : Wi * Xm.map h.bar = 1 := by
        change (((W⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (((W : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      have hWW : Wi.map h.bar * Xm = 1 := by
        have := congrArg (Matrix.map · h.bar) hWiW
        rw [Matrix.map_mul, hbb, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at this
        exact this
      have hmat : (((W * g * W⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) =
          Xm.map h.bar * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Wi := rfl
      calc (((ψ (W * g * W⁻¹) : unitarySU p f K 4) : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K) * Mm =
          ((ψ (W * g * W⁻¹) : unitarySU p f K 4) : GL (Fin 4) K) *
            (A : Matrix (Fin 4) (Fin 4) K) * ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * Mm) := by
            rw [Matrix.mul_assoc _ (A : Matrix (Fin 4) (Fin 4) K), ← Matrix.mul_assoc
              (A : Matrix (Fin 4) (Fin 4) K), hAAi, Matrix.one_mul]
        _ = (A : Matrix (Fin 4) (Fin 4) K) *
            (Xm * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar * Wi.map h.bar) *
              Xm := by
            rw [hψA', hmat, Matrix.map_mul, Matrix.map_mul, hbb]
        _ = ((A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) * Mm *
            ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar * (Wi.map h.bar * Xm) := by
            rw [hXm]
            simp only [Matrix.mul_assoc]
        _ = Mm * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := by
            rw [hAAi, hWW, Matrix.one_mul, Matrix.mul_one]
  have hfixL : ∀ U : unitarySU p f K 2,
      ρ x (QuotientGroup.mk (bdUL h U)) = QuotientGroup.mk (bdUL h U) := by
    intro U
    obtain ⟨Y, hY1, hY2⟩ := key (bdUL h U)
    rw [coe_bdUL, Mmat_bdL h s (unitary_SU h U) (det_SU h U)] at hY2
    rw [hY1, SU_ext (hcancel _ _ (hY2.trans (by rw [coe_bdUL h U])))]
  have hfixR : ∀ U : unitarySU p f K 2,
      ρ x (QuotientGroup.mk (bdUR h U)) = QuotientGroup.mk (bdUR h U) := by
    intro U
    obtain ⟨Y, hY1, hY2⟩ := key (bdUR h U)
    rw [coe_bdUR, Mmat_bdR h s (unitary_SU h U) (det_SU h U)] at hY2
    rw [hY1, SU_ext (hcancel _ _ (hY2.trans (by rw [coe_bdUR h U])))]
  have hfixb : ρ x (QuotientGroup.mk g₀) = QuotientGroup.mk g₀ := by
    obtain ⟨Y, hY1, hY2⟩ := key g₀
    rw [hg₀, map_X1, Mmat_X1] at hY2
    have hY : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 (h.bar l) := hcancel _ _ hY2
    have hl0 : l ≠ 0 := ne_zero_of_norm h hl
    have hbl : h.bar l = l⁻¹ := bar_inv_of_norm h hl
    have hzd : ((l ^ 2) • 1 : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      rw [det_smul, det_one, mul_one, Fintype.card_fin, ← pow_mul]
      norm_num [show l ^ 8 = (l ^ 4) ^ 2 by ring, hl4]
    have hzu : uStar h ((l ^ 2) • 1 : Matrix (Fin 4) (Fin 4) K) * ((l ^ 2) • 1) = 1 := by
      rw [uStar_smul, uStar_one, smul_mul_smul_comm, Matrix.one_mul, map_pow, ← mul_pow, hl,
        one_pow, one_smul]
    set zs := toSU h ((l ^ 2) • 1 : Matrix (Fin 4) (Fin 4) K) hzd hzu
    have hzs : zs ∈ scal p f K := toSU_smul_mem_scal h hzd hzu
    have hYz : Y * zs = g₀ := by
      apply SU_ext
      change ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((l ^ 2) • 1) = _
      rw [hY, hg₀, hbl, Matrix.mul_smul, Matrix.mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [X1, pow_two, hl0]
    rw [hY1, ← hYz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff zs).mpr hzs, mul_one]
  have hinv : ∀ y, ρ x (ρ x y) = y := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨Y, hY1, hY2⟩ := key g
    obtain ⟨Y', hY'1, hY'2⟩ := key Y
    rw [hY1, hY'1]
    congr 1
    apply SU_ext
    have hYb := congrArg (Matrix.map · h.bar) hY2
    rw [Matrix.map_mul, Matrix.map_mul, hbb] at hYb
    have hMM := Mmat_mul_map h hs
    have e : ((Y' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Mm * Mm.map h.bar) =
        (Mm * Mm.map h.bar) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      calc ((Y' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Mm * Mm.map h.bar) =
          (((Y' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Mm) * Mm.map h.bar := by
            rw [Matrix.mul_assoc]
        _ = Mm * (((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar * Mm.map h.bar) := by
            rw [hY'2, Matrix.mul_assoc]
        _ = (Mm * Mm.map h.bar) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
            rw [hYb, Matrix.mul_assoc]
    rw [hMM, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul] at e
    exact neg_injective e
  have hx2 : x ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one, pow_two]
    exact MulEquiv.ext hinv
  have hR : ρ x (QuotientGroup.mk (RSU h ht)) ≠ QuotientGroup.mk (RSU h ht) := by
    obtain ⟨Y, hY1, hY2⟩ := key (RSU h ht)
    rw [coe_RSU, Mmat_R h s ht] at hY2
    have hY : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Rmat' t := hcancel _ _ hY2
    rw [hY1]
    intro he
    rw [QuotientGroup.eq] at he
    obtain ⟨d, hd⟩ := val_of_mem_scal he
    apply Rmat_ne_smul htinv (d : K)
    have e : (((RSU h ht : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (((Y⁻¹ * RSU h ht : unitarySU p f K 4) : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K) := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [← coe_RSU h ht, e, hd, hY, Matrix.mul_smul, Matrix.mul_one]
  have hbR : ρ c.b (QuotientGroup.mk (RSU h ht)) = QuotientGroup.mk (RSU h ht) := by
    rw [show c.b = ((⟨c.b, c.b_mem_G⟩ : generalizedFitting H) : H) from rfl, hρW, hφb,
      MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply SU_ext
    have hcomm : (((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * Rmat t =
        Rmat t * ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [hg₀, Rmat]
      exact (bd_comm_X1 _ _ l).symm
    change ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Rmat t *
      (((g₀⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Rmat t
    rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    exact Matrix.mul_one _
  have hx1 : x ≠ 1 := fun h1 => hR (by rw [h1, map_one, MulAut.one_apply])
  have hxb : x ≠ c.b := fun h1 => hR (by rw [h1, hbR])
  have hcomm_of_fix : ∀ g : generalizedFitting H, ρ x (φ g) = φ g →
      x * (g : H) = (g : H) * x := by
    intro g hg
    have h1 : ρ (x * (g : H) * x⁻¹) = ρ g := by
      rw [map_mul, map_mul, map_inv, hρW, Catalog7L4.mul_conj_mul_inv, hg]
    have h2 := hinj h1
    calc x * (g : H) = x * (g : H) * x⁻¹ * x := by group
      _ = (g : H) * x := by rw [h2]
  have hxbc : x * c.b = c.b * x :=
    hcomm_of_fix ⟨c.b, c.b_mem_G⟩ (by rw [hφb]; exact hfixb)
  have hfixF : ∀ g : generalizedFitting H, φ g ∈ factorUL h ∨ φ g ∈ factorUR h →
      ρ x (φ g) = φ g := by
    rintro g (⟨U, hU⟩ | ⟨U, hU⟩)
    · rw [← hU]
      exact hfixL U
    · rw [← hU]
      exact hfixR U
  have hKF : ∀ g : generalizedFitting H, (g : H) ∈ c.K → φ g ∈ factorUL h ∨ φ g ∈ factorUR h := by
    intro g hg
    have hmem : φ g ∈ KP := ⟨g, mem_subgroupOf.mpr hg, rfl⟩
    rcases hfac with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (h1 ▸ hmem)
    · exact Or.inr (h1 ▸ hmem)
  have hKaF : ∀ g : generalizedFitting H, (g : H) ∈ conjugate c.K c.a →
      φ g ∈ factorUL h ∨ φ g ∈ factorUR h := by
    intro g hg
    have hmem : φ g ∈ KaP := ⟨g, mem_subgroupOf.mpr hg, rfl⟩
    rcases hfac with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr (h2 ▸ hmem)
    · exact Or.inl (h2 ▸ hmem)
  refine Catalog7L4.false_of_outer_klein c hx2 hx1 hxb hxbc (fun g hg => ?_) (fun g hg => ?_)
  · exact hcomm_of_fix ⟨g, c.K_le_G hg⟩ (hfixF _ (hKF ⟨g, c.K_le_G hg⟩ hg))
  · exact hcomm_of_fix ⟨g, c.conjugate_K_le_G hg⟩
      (hfixF _ (hKaF ⟨g, c.conjugate_K_le_G hg⟩ hg))

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
