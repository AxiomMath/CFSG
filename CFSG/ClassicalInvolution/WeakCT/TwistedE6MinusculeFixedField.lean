module

public import CFSG.ClassicalInvolution.WeakCT.E6MinusculeFixedField
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LocalAnalysis.StandardType.GGLangRootSym3
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public noncomputable section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement

theorem sigma_comp_sigma {k : Type} [Field k] (θ : k →+* k) :
    (CFSG.LieType.Steinberg.TwistedE6.sigma k θ).comp
        (CFSG.LieType.Steinberg.TwistedE6.sigma k θ) =
      minBC e6Data_valid (θ.comp θ) := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top e6Data_valid k) ?_
  rintro _ ⟨i, c, rfl | rfl⟩
  · simp only [MonoidHom.comp_apply]
    rw [CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single,
      CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single,
      CFSG.LieType.Steinberg.TwistedE6.rhoPerm_apply_rhoPerm,
      CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm]
    rfl
  · simp only [MonoidHom.comp_apply]
    rw [CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single,
      CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single,
      CFSG.LieType.Steinberg.TwistedE6.rhoPerm_apply_rhoPerm,
      CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm]
    rfl

theorem ggFrobT_ggRatEmb (f : ℕ) :
    (ggFrobT f).comp (ggRatEmb (2 * f)) =
      (ggRatEmb (2 * f)).comp (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) := by
  ext c
  rw [RingHom.comp_apply, RingHom.comp_apply, ggFrobT_apply,
    CFSG.LieType.Steinberg.Exceptional.frobQ_apply, map_pow]

theorem sigma_minBC_naturality {k k' : Type} [Field k] [Field k']
    (ι : k →+* k') (θ : k →+* k) (θ' : k' →+* k')
    (hθ : θ'.comp ι = ι.comp θ) (g : e6Data_valid.minGroup k) :
    CFSG.LieType.Steinberg.TwistedE6.sigma k' θ' (minBC e6Data_valid ι g) =
      minBC e6Data_valid ι (CFSG.LieType.Steinberg.TwistedE6.sigma k θ g) := by
  have hh : (CFSG.LieType.Steinberg.TwistedE6.sigma k' θ').comp
        (minBC e6Data_valid ι) =
      (minBC e6Data_valid ι).comp
        (CFSG.LieType.Steinberg.TwistedE6.sigma k θ) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top e6Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply]
      rw [CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm,
        CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single,
        CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single,
        CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm]
      exact congrArg (e6Data_valid.xm k' (Pi.single
        (CFSG.LieType.Steinberg.TwistedE6.rhoPerm i) 1))
        (RingHom.congr_fun hθ c)
    · simp only [MonoidHom.comp_apply]
      rw [CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm,
        CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single,
        CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single,
        CFSG.ClassicalInvolution.Phan.PhanE.minBC_xm]
      exact congrArg (e6Data_valid.xm k' (-Pi.single
        (CFSG.LieType.Steinberg.TwistedE6.rhoPerm i) 1))
        (RingHom.congr_fun hθ c)
  exact DFunLike.congr_fun hh g

theorem sigma_square_ggFrob {f : ℕ} (g : e6Data_valid.minGroup GGL) :
    CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f)
        (CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f) g) =
      minBC e6Data_valid (ggFrobT (2 * f)) g := by
  have hcomp : (ggFrobT f).comp (ggFrobT f) = ggFrobT (2 * f) := by
    ext c
    rw [RingHom.comp_apply, ggFrobT_apply, ggFrobT_apply, ggFrobT_apply,
      ← pow_mul, ← pow_add, show f + f = 2 * f by omega]
  have h := DFunLike.congr_fun (sigma_comp_sigma (k := GGL) (ggFrobT f)) g
  rw [hcomp] at h
  exact h

theorem twisted_fixed_mem_minBC_range {f : ℕ} (hf : 1 ≤ f)
    {g : e6Data_valid.minGroup GGL}
    (hfix : CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f) g = g) :
    g ∈ (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField 2 (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).map
        (minBC e6Data_valid (ggRatEmb (2 * f))) := by
  have hf2 : 1 ≤ 2 * f := by omega
  have hfix2 : minBC e6Data_valid (ggFrobT (2 * f)) g = g := by
    rw [← sigma_square_ggFrob (f := f) g, hfix, hfix]
  have hmem := fixed_mem_minBC_range (f := 2 * f) hf2 hfix2
  obtain ⟨h, hh⟩ := hmem
  have hnatural := sigma_minBC_naturality (k := GaloisField 2 (2 * f)) (k' := GGL)
    (ι := ggRatEmb (2 * f)) (θ := CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)
    (θ' := ggFrobT f) (ggFrobT_ggRatEmb f) h
  have hfixFin : CFSG.LieType.Steinberg.TwistedE6.sigma
      (GaloisField 2 (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) h = h := by
    apply CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
      e6Data_valid (ggRatEmb (2 * f))
    rw [← hnatural, hh, hfix]
  have hfixMem : h ∈ CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField 2 (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) := by
    rw [CFSG.LieType.Steinberg.TwistedE6.mem_fixedGroup]
    exact hfixFin
  exact Subgroup.mem_map.2 ⟨h, hfixMem, hh⟩

theorem exists_twisted_fixed_field_hom {f : ℕ} [NeZero f] (hf : 1 ≤ f)
    (θ : Su (actualQuadraticSubfield f) 2 f 3 →* e6Data_valid.minGroup GGL)
    (hθ : ∀ A, CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f) (θ A) = θ A) :
    ∃ lamFin : Su (actualQuadraticSubfield f) 2 f 3 →*
        CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f,
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp
          lamFin = θ := by
  let π : CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f →*
      e6Data_valid.minGroup GGL :=
    (minBC e6Data_valid (ggRatEmb (2 * f))).comp
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
        (GaloisField 2 (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype
  have hπinj : Function.Injective π :=
    (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
      e6Data_valid (ggRatEmb (2 * f))).comp
      (Subgroup.subtype_injective (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
        (GaloisField 2 (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)))
  have hchoice : ∀ A, ∃ h : CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f,
      minBC e6Data_valid (ggRatEmb (2 * f)) (h : e6Data_valid.minGroup
        (GaloisField 2 (2 * f))) = θ A := by
    intro A
    obtain ⟨x, hx, hval⟩ :=
      Subgroup.mem_map.1 (twisted_fixed_mem_minBC_range (f := f) hf (hθ A))
    exact ⟨⟨x, hx⟩, hval⟩
  let lamFun : Su (actualQuadraticSubfield f) 2 f 3 →
      CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f :=
    fun A => Classical.choose (hchoice A)
  have hlam : ∀ A, π (lamFun A) = θ A :=
    fun A => Classical.choose_spec (hchoice A)
  let lamFin : Su (actualQuadraticSubfield f) 2 f 3 →*
      CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f :=
  { toFun := lamFun
    map_one' := by
      apply hπinj
      rw [hlam 1, map_one]
      exact (map_one π).symm
    map_mul' := by
      intro A B
      apply hπinj
      rw [hlam (A * B), map_mul, map_mul, hlam A, hlam B] }
  refine ⟨lamFin, ?_⟩
  apply MonoidHom.ext
  intro A
  exact hlam A

noncomputable def twistedA2Actor (f : ℕ) [NeZero f] :
    SL(3, actualQuadraticSubfield f) →*
      SL(3, actualQuadraticSubfield f) :=
  (inverseTransposeSL 3 (actualQuadraticSubfield f)).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map
      (unitaryInvolution (actualQuadraticSubfield f) 2 f))

theorem twistedA2Actor_fixes_su (f : ℕ) [NeZero f] :
    ∀ A : Su (actualQuadraticSubfield f) 2 f 3,
      twistedA2Actor f
        (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) =
      CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A := by
  let F := actualQuadraticSubfield f
  let σ : F ≃+* F := unitaryInvolution F 2 f
  intro A
  change inverseTransposeSL 3 F
      (Matrix.SpecialLinearGroup.map (σ : F →+* F) (CFSG.ClassicalInvolution.Models.suToSL σ 3 A)) = CFSG.ClassicalInvolution.Models.suToSL σ 3 A
  have hC : Matrix.transpose
      ((↑(A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ) *
      (↑(A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    simpa only [conjTr] using A.2.2
  have hGL := CFSG.GH74.Generic.BProg.B2.GenLocL3NFAux.map_inverseTranspose_eq_of_unitary
    (φ := σ) (C := (A : GL (Fin 3) F)) hC
  have hGL' : Matrix.GeneralLinearGroup.inverseTranspose
      (Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin 3) F)) = (A : GL (Fin 3) F) := by
    simpa only [Matrix.GeneralLinearGroup.map_inverseTranspose] using hGL
  have hdet : (((Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin 3) F)) :
      GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    change ((↑(Matrix.SpecialLinearGroup.map (σ : F →+* F)
      (CFSG.ClassicalInvolution.Models.suToSL σ 3 A)) : Matrix (Fin 3) (Fin 3) F)).det = 1
    exact (Matrix.SpecialLinearGroup.map (σ : F →+* F) (CFSG.ClassicalInvolution.Models.suToSL σ 3 A)).2
  have hAdj : Matrix.adjugate
      (((Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin 3) F)) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin 3) F))⁻¹ :
        GL (Fin 3) F) := by
    have h := TauCeti.adjugateGL_eq_inv
      (g := Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin 3) F)) hdet
    simpa [TauCeti.adjugateGL_val] using
      congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  have hleft : (↑(inverseTransposeSL 3 F
      (Matrix.SpecialLinearGroup.map (σ : F →+* F) (CFSG.ClassicalInvolution.Models.suToSL σ 3 A))) :
      Matrix (Fin 3) (Fin 3) F) = (↑(CFSG.ClassicalInvolution.Models.suToSL σ 3 A) : Matrix (Fin 3) (Fin 3) F) := by
    rw [inverseTransposeSL_apply]
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
    change (Matrix.adjugate
      (((Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin 3) F)) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).transpose =
      (↑(CFSG.ClassicalInvolution.Models.suToSL σ 3 A) : Matrix (Fin 3) (Fin 3) F)
    rw [hAdj]
    have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hGL'
    simpa only [Matrix.GeneralLinearGroup.coe_inverseTranspose,
      CFSG.ClassicalInvolution.Models.coe_suToSL,
      CFSG.ClassicalInvolution.Models.suMat] using hmat
  exact Subtype.ext hleft

set_option maxHeartbeats 1000000 in
theorem exists_twisted_common_lang_of_full_marking
    {f p : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (lam : SL(3, actualQuadraticSubfield f) →* e6Data_valid.minGroup GGL)
    (hadj : ∀ A : SL(3, actualQuadraticSubfield f),
      e6IsogenyAlgebraic (lam (twistedA2Actor f A)) =
        M.D.step (e6IsogenyAlgebraic (lam A))) :
    ∃ c : e6Data_valid.minGroup GGL,
      e6IsogenyAlgebraic c = M.D.g0 ∧
      ∀ A : Su (actualQuadraticSubfield f) 2 f 3,
        CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f)
            (c * lam (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹) =
          c * lam (CFSG.ClassicalInvolution.Models.suToSL
            (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹ := by
  classical
  have hg0 : M.D.g0 ∈ (e6IsogenyAlgebraic (Ω := GGL)).range := by
    have hr := range_e6IsogenyAlgebraic (Ω := GGL)
    exact hr.symm ▸ M.D.g0_mem
  obtain ⟨c, hc⟩ := hg0
  have hphi : M.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f) := by
    rw [M.hΦ]
    rfl
  let clam := (MulAut.conj c).toMonoidHom.comp lam
  let mu := (CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f)).comp clam
  let nu := clam.comp (twistedA2Actor f)
  have heq : mu = nu := by
    apply algebraic_lift_unique_of_isogeny_eq
    intro A
    change e6IsogenyAlgebraic (Ω := GGL)
        (CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f)
          (c * lam A * c⁻¹)) =
      e6IsogenyAlgebraic (Ω := GGL) (c * lam (twistedA2Actor f A) * c⁻¹)
    rw [CFSG.LieType.Steinberg.Minuscule.e6IsogenyAlgebraic_sigma
      (Ω := GGL) (Fr := ggFrobT f), ← hphi]
    have hnaturality {H : Type} [Group H] (phi : H →* H) (g n a a' : H)
        (hg : phi g = g * n) (ha : a' = n * phi a * n⁻¹) :
        phi (g * a * g⁻¹) = g * a' * g⁻¹ := by
      simp only [map_mul, map_inv]
      rw [hg, ha]
      group
    have hconj (z : e6Data_valid.minGroup GGL) :
        e6IsogenyAlgebraic (c * z * c⁻¹) =
          e6IsogenyAlgebraic c * e6IsogenyAlgebraic z * (e6IsogenyAlgebraic c)⁻¹ := by
      simp only [map_mul, map_inv]
    have h0 := (hconj (lam A)).trans (congrArg
      (fun z : ModGL Tag.E6 GGL => z * e6IsogenyAlgebraic (lam A) * z⁻¹) hc)
    have h1 := (hconj (lam (twistedA2Actor f A))).trans (congrArg
      (fun z : ModGL Tag.E6 GGL =>
        z * e6IsogenyAlgebraic (lam (twistedA2Actor f A)) * z⁻¹) hc)
    have hstep : M.D.step (e6IsogenyAlgebraic (lam A)) =
        M.D.n * M.D.Φ (e6IsogenyAlgebraic (lam A)) * M.D.n⁻¹ := by
      change (MulAut.conj M.D.n) (M.D.Φ (e6IsogenyAlgebraic (lam A))) =
        M.D.n * M.D.Φ (e6IsogenyAlgebraic (lam A)) * M.D.n⁻¹
      rw [MulAut.conj_apply]
    have ha : e6IsogenyAlgebraic (lam (twistedA2Actor f A)) =
        M.D.n * M.D.Φ (e6IsogenyAlgebraic (lam A)) * M.D.n⁻¹ :=
      (hadj A).trans hstep
    have h := hnaturality (H := ModGL (langTag .twistedE6) GGL)
      M.D.Φ M.D.g0 M.D.n (e6IsogenyAlgebraic (lam A))
      (e6IsogenyAlgebraic (lam (twistedA2Actor f A))) M.D.lang ha
    exact (congrArg M.D.Φ h0).trans (h.trans h1.symm)
  refine ⟨c, hc, ?_⟩
  intro A
  have h := DFunLike.congr_fun heq
    (CFSG.ClassicalInvolution.Models.suToSL
      (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A)
  change CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f)
      (c * lam (CFSG.ClassicalInvolution.Models.suToSL
        (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹) =
    c * lam (twistedA2Actor f
      (CFSG.ClassicalInvolution.Models.suToSL
        (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A)) * c⁻¹ at h
  rw [twistedA2Actor_fixes_su (f := f)] at h
  exact h

set_option maxHeartbeats 2000000 in
theorem exists_twisted_donor_common_lang_and_finite_hom
    {f p : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →* e6Data_valid.minGroup
      (actualQuadraticSubfield f))
    (hadj : ∀ A : SL(3, actualQuadraticSubfield f),
      e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
            (twistedA2Actor f A)) =
        M.D.step (e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A))) :
    ∃ (c : e6Data_valid.minGroup GGL)
      (lamFin : Su (actualQuadraticSubfield f) 2 f 3 →*
        CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f),
      e6IsogenyAlgebraic c = M.D.g0 ∧
      (∀ A : Su (actualQuadraticSubfield f) 2 f 3,
        CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f)
            (c * ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹) =
          c * ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹) ∧
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp lamFin =
        (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) := by
  classical
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)
  let lam := (minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ
  obtain ⟨c, hc, hfix⟩ :=
    exists_twisted_common_lang_of_full_marking (M := M) lam hadj
  let theta : Su (actualQuadraticSubfield f) 2 f 3 →*
      e6Data_valid.minGroup GGL :=
    (MulAut.conj c).toMonoidHom.comp
      (lam.comp (CFSG.ClassicalInvolution.Models.suToSL
        (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))
  have htheta : ∀ A : Su (actualQuadraticSubfield f) 2 f 3,
      CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f) (theta A) = theta A := by
    intro A
    simpa only [theta, lam, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using hfix A
  obtain ⟨lamFin, hlamFin⟩ :=
    exists_twisted_fixed_field_hom (f := f) hf theta htheta
  refine ⟨c, lamFin, hc, ?_, ?_⟩
  · simpa only [lam] using hfix
  · simpa only [theta] using hlamFin

theorem ggIotaK_twistedE6_eq_isogeny_minBC (n f : ℕ) (hf : 1 ≤ f)
    (k : (ggU .twistedE6 n f).K) :
    ggIotaK .twistedE6 n f hf k =
      e6IsogenyAlgebraic (minBC e6Data_valid (ggRatEmb (2 * f))
        ((show CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f from k) :
          e6Data_valid.minGroup (GaloisField 2 (2 * f)))) := by
  change ggIota .twistedE6 n f hf (QuotientGroup.mk k) = _
  rw [ggIota_twistedE6_mk]
  exact (e6IsogenyAlgebraic_minBC (Ω := GGL)
    (GaloisField 2 (2 * f)) (ggRatEmb (2 * f))
    ((show CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f from k) :
      e6Data_valid.minGroup (GaloisField 2 (2 * f)))).symm

theorem exists_twisted_donor_originalU_canonical_square
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →* e6Data_valid.minGroup
      (actualQuadraticSubfield f))
    (hΨ : Function.Injective Ψ)
    (hadj : ∀ A : SL(3, actualQuadraticSubfield f),
      e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
            (twistedA2Actor f A)) =
        M.D.step (e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A))) :
    ∃ (c : e6Data_valid.minGroup GGL)
      (lamU : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K),
      Function.Injective lamU ∧ e6IsogenyAlgebraic c = M.D.g0 ∧
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp lamU =
        (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) ∧
      (ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp lamU =
        (MulAut.conj M.D.g0).toMonoidHom.comp
          (e6IsogenyAlgebraic.comp
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)
  obtain ⟨c, lamFin, hc, _hfix, hlam⟩ :=
    exists_twisted_donor_common_lang_and_finite_hom M Ψ hadj
  let lamU : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K := lamFin
  let πF := (minBC e6Data_valid (ggRatEmb (2 * f))).comp
    (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField 2 (2 * f))
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype
  have hcomp : πF.comp lamU =
      (MulAut.conj c).toMonoidHom.comp
        (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
          (CFSG.ClassicalInvolution.Models.suToSL
            (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) := hlam
  have hinj : Function.Injective lamU := by
    have hright : Function.Injective
        ((MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))) :=
      (MulAut.conj c).injective.comp
        ((CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
          e6Data_valid (actualQuadraticSubfield f).subtype).comp
            (hΨ.comp (CFSG.ClassicalInvolution.Models.suToSL_injective)))
    have hleft : Function.Injective (πF.comp lamU) := hcomp.symm ▸ hright
    intro A B hAB
    exact hleft (congrArg πF hAB)
  refine ⟨c, lamU, hinj, hc, hcomp, ?_⟩
  ext A
  rw [MonoidHom.comp_apply, ggIotaK_twistedE6_eq_isogeny_minBC]
  have hA := DFunLike.congr_fun hcomp A
  change minBC e6Data_valid (ggRatEmb (2 * f))
      ((show CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f from lamU A) :
        e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
    c * ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
      (CFSG.ClassicalInvolution.Models.suToSL
        (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹ at hA
  rw [hA, map_mul, map_mul, map_inv, hc]
  rfl

theorem unitaryInvolution_actual_subtype (f : ℕ) [NeZero f]
    (c : actualQuadraticSubfield f) :
    (actualQuadraticSubfield f).subtype
        (unitaryInvolution (actualQuadraticSubfield f) 2 f c) =
      ggFrobT f ((actualQuadraticSubfield f).subtype c) := by
  rw [unitaryInvolution_apply, ggFrobT_apply]
  exact map_pow (actualQuadraticSubfield f).subtype c (2 ^ f)

theorem twistedA2Actor_blk (f : ℕ) [NeZero f] (i : Fin 2)
    (B : SL(2, actualQuadraticSubfield f)) :
    twistedA2Actor f (blk (actualQuadraticSubfield f) i B) =
      blk (actualQuadraticSubfield f) i
        (inverseTransposeSL 2 (actualQuadraticSubfield f)
          (Matrix.SpecialLinearGroup.map
            (unitaryInvolution (actualQuadraticSubfield f) 2 f) B)) := by
  change inverseTransposeSL 3 (actualQuadraticSubfield f)
      (Matrix.SpecialLinearGroup.map
        (unitaryInvolution (actualQuadraticSubfield f) 2 f)
        (blk (actualQuadraticSubfield f) i B)) = _
  rw [CFSG.ClassicalInvolution.WeakCT.map_blk, inverseTransposeSL_blk]

theorem e6_donor_comparison_of_reversal
    {f : ℕ} [NeZero f] (D : LangDatum Tag.E6 GGL) (hq : D.q = 2 ^ f)
    {ρF : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hFrob : FrobRootMap D ρF)
    (v : Fin 2 → Fin Tag.E6.rank → ℤ)
    (hv : ∀ i, IsRoot Tag.E6 (v i)) (hrev : ∀ i, ρF (v i) = -(v i))
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hblk : ∀ i : Fin 2,
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) i) =
        CFSG.LieType.Chevalley.rootSL2 Tag.E6 (actualQuadraticSubfield f) (v i)) :
    ∀ A : SL(3, actualQuadraticSubfield f),
      e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
            (twistedA2Actor f A)) =
        D.step (e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A)) := by
  let F := actualQuadraticSubfield f
  let σ : F →+* F := (unitaryInvolution F 2 f).toRingHom
  let lam := (minBC e6Data_valid F.subtype).comp Ψ
  have hsq : e6IsogenyAlgebraic.comp lam =
      (baseChangeGL F.subtype).comp ((adjointGroup Tag.E6 F).subtype.comp ρ) :=
    e6IsogenyAlgebraic_minBC_algebraic_square_actualQuadraticSubfield Ψ ρ hρ
  have hsqA (A : SL(3, F)) : e6IsogenyAlgebraic (lam A) =
      baseChangeGL F.subtype ((adjointGroup Tag.E6 F).subtype (ρ A)) :=
    DFunLike.congr_fun hsq A
  have hblkA (i : Fin 2) (B : SL(2, F)) :
      (adjointGroup Tag.E6 F).subtype (ρ (blk F i B)) =
        CFSG.LieType.Chevalley.rootSL2 Tag.E6 F (v i) B :=
    DFunLike.congr_fun (hblk i) B
  have hmapFr (B : SL(2, F)) :
      Matrix.SpecialLinearGroup.map F.subtype (Matrix.SpecialLinearGroup.map σ B) =
        Matrix.SpecialLinearGroup.map (ggFrobT f)
          (Matrix.SpecialLinearGroup.map F.subtype B) := by
    apply Subtype.ext
    ext i j
    exact unitaryInvolution_actual_subtype f (B i j)
  have hFr : ∀ c, ggFrobT f c = c ^ D.q := by
    intro c
    rw [ggFrobT_apply, hq]
  have hblocks (i : Fin 2) (B : SL(2, F)) :
      e6IsogenyAlgebraic (lam (twistedA2Actor f (blk F i B))) =
        D.step (e6IsogenyAlgebraic (lam (blk F i B))) := by
    rw [twistedA2Actor_blk, hsqA, hsqA, hblkA, hblkA,
      rootSL2_inverseTransposeSL (hv i)]
    have hbcneg := CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field
      (τ := Tag.E6) F.subtype (-(v i)) (Matrix.SpecialLinearGroup.map σ B)
    have hbcpos := CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field
      (τ := Tag.E6) F.subtype (v i) B
    have hstep := CFSG.StandardType.LangRat.step_rootSL2_of_charTwo_of_frobRootMap
      D hFrob (hv i) (ggFrobT f) hFr (Matrix.SpecialLinearGroup.map F.subtype B)
    rw [hrev i] at hstep
    exact hbcneg.trans ((congrArg
      (CFSG.LieType.Chevalley.rootSL2 Tag.E6 GGL (-(v i)))
        (hmapFr B)).trans (hstep.symm.trans (congrArg D.step hbcpos.symm)))
  let mu := (e6IsogenyAlgebraic.comp lam).comp (twistedA2Actor f)
  let nu := D.step.comp (e6IsogenyAlgebraic.comp lam)
  have h0 : mu.comp (blk F 0) = nu.comp (blk F 0) :=
    MonoidHom.ext (hblocks 0)
  have h1 : mu.comp (blk F 1) = nu.comp (blk F 1) :=
    MonoidHom.ext (hblocks 1)
  have heq : mu = nu := CFSG.ClassicalInvolution.WeakCT.hom_ext_sl3 h0 h1
  intro A
  exact DFunLike.congr_fun heq A

theorem twisted_rho_neg_of_plus
    {f p : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1)
    {ρF : Equiv.Perm (Fin (langTag .twistedE6).rank → ℤ)}
    (hFrob : FrobRootMap M.D ρF) {v : Fin (langTag .twistedE6).rank → ℤ}
    (hv : IsRoot (langTag .twistedE6) v) : ρF v = -v := by
  have hneg : eps p f = -1 :=
    (eps_eq_neg_one_iff hp hp2 f (Or.inr hplus)).mpr hplus
  let D : LangDatum TwistTag.E6.tag GGL := M.D
  let w : WeylGroup TwistTag.E6.tag := M.w
  let ρ' : Equiv.Perm (Fin TwistTag.E6.tag.rank → ℤ) := ρF
  let v' : Fin TwistTag.E6.tag.rank → ℤ := v
  have hFrob' : FrobRootMap D ρ' := hFrob
  have hv' : IsRoot TwistTag.E6.tag v' := hv
  let π' : Equiv.Perm (Fin TwistTag.E6.tag.rank) :=
    (finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)
  have hπ : π' = 1 := by
    dsimp only [π']
    rw [piB_twistedE6_of_dvd f hplus]
    exact Equiv.permCongr_refl _
  have hw : ∀ u : Fin TwistTag.E6.tag.rank → ℤ,
      w • permLattice (TwistTag.perm .E6) u = eps p f • permLattice π' u := by
    change GGWeylLaw .twistedE6 p f ht M.w
    exact M.hw
  have hΦ : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f) := by
    change M.D.Φ = _
    rw [M.hΦ]
    rfl
  have h := ggRho_tw D w hΦ M.hn π' hw ρ' hFrob' hv'
  rw [hneg, hπ] at h
  have hid : permLattice (1 : Equiv.Perm (Fin TwistTag.E6.tag.rank)) v' = v' := by
    ext i
    rfl
  rw [hid, neg_one_zsmul] at h
  exact h

theorem twisted_donor_comparison_of_reversal
    {f p : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    {ρF : Equiv.Perm (Fin (langTag .twistedE6).rank → ℤ)} (hFrob : FrobRootMap M.D ρF)
    (v : Fin 2 → Fin (langTag .twistedE6).rank → ℤ)
    (hv : ∀ i, IsRoot (langTag .twistedE6) (v i))
    (hrev : ∀ i, ρF (v i) = -(v i))
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hblk : ∀ i : Fin 2,
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) i) =
        CFSG.LieType.Chevalley.rootSL2 Tag.E6 (actualQuadraticSubfield f) (v i)) :
    ∀ A : SL(3, actualQuadraticSubfield f),
      e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
            (twistedA2Actor f A)) =
        M.D.step (e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A)) := by
  exact e6_donor_comparison_of_reversal M.D M.hq hFrob v hv hrev Ψ ρ hρ hblk

theorem twisted_donor_comparison_of_plus
    {f p : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    {ρF : Equiv.Perm (Fin (langTag .twistedE6).rank → ℤ)} (hFrob : FrobRootMap M.D ρF)
    (v : Fin 2 → Fin (langTag .twistedE6).rank → ℤ)
    (hv : ∀ i, IsRoot (langTag .twistedE6) (v i))
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hblk : ∀ i : Fin 2,
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) i) =
        CFSG.LieType.Chevalley.rootSL2 Tag.E6 (actualQuadraticSubfield f) (v i)) :
    ∀ A : SL(3, actualQuadraticSubfield f),
      e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
            (twistedA2Actor f A)) =
        M.D.step (e6IsogenyAlgebraic
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A)) := by
  exact twisted_donor_comparison_of_reversal M hFrob v hv
    (fun i => twisted_rho_neg_of_plus M hp hp2 hplus hFrob (hv i)) Ψ ρ hρ hblk

set_option maxHeartbeats 2000000 in
theorem exists_twisted_originalU_minuscule_marked_pair_of_plus
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1) :
    ∃ (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
      (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup Tag.E6 (actualQuadraticSubfield f))
      (c : e6Data_valid.minGroup GGL)
      (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K),
      ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ ∧
      CFSG.RankThree.PartOne.KF4.IsA2Frame
        ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ)
        (fun i j => CFSG.RankThree.E6.chainRoot
          CFSG.RankThree.E6.chain13 i j) ∧
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) =
        e6rhoA2₁ (actualQuadraticSubfield f) ∧
      Function.Injective theta ∧ e6IsogenyAlgebraic c = M.D.g0 ∧
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp theta =
        (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) ∧
      (ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta =
        (MulAut.conj M.D.g0).toMonoidHom.comp
          (e6IsogenyAlgebraic.comp
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))) ∧
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f' : ℕ),
        Nat.card K = (2 ^ f') ^ 2 →
        Nat.card ((B12 (actualQuadraticSubfield f) 2 f).map theta) =
          2 ^ f' * ((2 ^ f') ^ 2 - 1) →
        UnitaryBlockStandardPair K 2 f' theta.range
          ((B12 (actualQuadraticSubfield f) 2 f).map theta)
          ((B23 (actualQuadraticSubfield f) 2 f).map theta) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)
  obtain ⟨ρF, hFrob⟩ := frobeniusOnRoots_proved (langTag .twistedE6) GGL M.D
  obtain ⟨Ψ, ρ, hΨ, _hρinj, hρ, hframe, heq, hblk0, hblk1⟩ :=
    exists_e6Sl3_adjoint_frame_actualQuadraticSubfield_both (f := f)
  let v : Fin 2 → Fin (langTag .twistedE6).rank → ℤ :=
    ![Pi.single 0 1, Pi.single 2 1]
  have hv : ∀ i, IsRoot (langTag .twistedE6) (v i) := by
    intro i
    fin_cases i <;> exact CFSG.Blueprint.Chevalley.isRoot_single _ _
  have hblk : ∀ i : Fin 2,
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) i) =
        CFSG.LieType.Chevalley.rootSL2 Tag.E6 (actualQuadraticSubfield f) (v i) := by
    intro i
    fin_cases i
    · change _ = CFSG.LieType.Chevalley.rootSL2 Tag.E6
        (actualQuadraticSubfield f) (Pi.single 0 1)
      exact hblk0
    · change _ = CFSG.LieType.Chevalley.rootSL2 Tag.E6
        (actualQuadraticSubfield f) (Pi.single 2 1)
      exact hblk1
  have hadj := twisted_donor_comparison_of_plus M hp hp2 hplus hFrob v hv Ψ ρ hρ hblk
  obtain ⟨c, theta, hinj, hc, hmin, hcanonical⟩ :=
    exists_twisted_donor_originalU_canonical_square (n := n) M Ψ hΨ hadj
  have hker : theta.ker ≤ Subgroup.center (Su (actualQuadraticSubfield f) 2 f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff theta).mpr hinj]
    exact bot_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker rfl rfl
  refine ⟨Ψ, ρ, c, theta, hρ, hframe, heq, hinj, hc, hmin, hcanonical, ?_⟩
  intro K _ _ _ f' hK horder
  exact ggPhanNSAPairAux_stdPair_of_card (card_actualQuadraticSubfield hf) hK hpair horder

set_option maxHeartbeats 2000000 in
theorem exists_twisted_originalU_minuscule_marked_pair_at_a2_pair
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    {α β : Fin Tag.E6.rank → ℤ} (hpair : IsA2Pair α β) :
    ∃ (w : WeylGroup Tag.E6) (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
      (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup Tag.E6 (actualQuadraticSubfield f))
      (c : e6Data_valid.minGroup GGL)
      (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K),
      ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ ∧
      CFSG.RankThree.PartOne.KF4.IsA2Frame
        ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ)
        (fun i j => w • CFSG.RankThree.E6.chainRoot
          CFSG.RankThree.E6.chain13 i j) ∧
      w • chainRoot chain13 0 1 = α ∧ w • chainRoot chain13 1 2 = β ∧
      Function.Injective theta ∧ e6IsogenyAlgebraic c = M.D.g0 ∧
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp theta =
        (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) ∧
      (ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta =
        (MulAut.conj M.D.g0).toMonoidHom.comp
          (e6IsogenyAlgebraic.comp
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))) ∧
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f' : ℕ),
        Nat.card K = (2 ^ f') ^ 2 →
        Nat.card ((B12 (actualQuadraticSubfield f) 2 f).map theta) =
          2 ^ f' * ((2 ^ f') ^ 2 - 1) →
        UnitaryBlockStandardPair K 2 f' theta.range
          ((B12 (actualQuadraticSubfield f) 2 f).map theta)
          ((B23 (actualQuadraticSubfield f) 2 f).map theta) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)
  obtain ⟨ρF, hFrob⟩ := frobeniusOnRoots_proved (langTag .twistedE6) GGL M.D
  obtain ⟨w, Ψ, ρ, hΨ, _hρinj, hρ, hframe, hwα, hwβ, hblk0, hblk1⟩ :=
    exists_e6Sl3_adjoint_frame_at_a2_pair (f := f) hpair
  let v : Fin 2 → Fin (langTag .twistedE6).rank → ℤ :=
    ![α, β]
  have hv : ∀ i, IsRoot (langTag .twistedE6) (v i) := by
    intro i
    fin_cases i
    · exact hpair.isRoot_fst
    · exact hpair.isRoot_snd
  have hblk : ∀ i : Fin 2,
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ).comp
          (blk (actualQuadraticSubfield f) i) =
        CFSG.LieType.Chevalley.rootSL2 Tag.E6 (actualQuadraticSubfield f) (v i) := by
    intro i
    fin_cases i
    · change _ = CFSG.LieType.Chevalley.rootSL2 Tag.E6
        (actualQuadraticSubfield f) α
      exact hblk0
    · change _ = CFSG.LieType.Chevalley.rootSL2 Tag.E6
        (actualQuadraticSubfield f) β
      exact hblk1
  have hadj := twisted_donor_comparison_of_plus M hp hp2 hplus hFrob v hv Ψ ρ hρ hblk
  obtain ⟨c, theta, hinj, hc, hmin, hcanonical⟩ :=
    exists_twisted_donor_originalU_canonical_square (n := n) M Ψ hΨ hadj
  have hker : theta.ker ≤ Subgroup.center (Su (actualQuadraticSubfield f) 2 f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff theta).mpr hinj]
    exact bot_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker rfl rfl
  refine ⟨w, Ψ, ρ, c, theta, hρ, hframe, hwα, hwβ, hinj, hc, hmin, hcanonical, ?_⟩
  intro K _ _ _ f' hK horder
  exact ggPhanNSAPairAux_stdPair_of_card (card_actualQuadraticSubfield hf) hK hpair horder

set_option maxHeartbeats 2000000 in
theorem e6IsogenyAlgebraic_mem_frameRootSpan_actualQuadraticSubfield
    {f : ℕ} [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) σ)
    (A : SL(3, actualQuadraticSubfield f)) :
    e6IsogenyAlgebraic
        (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A) ∈
      rootSpan Tag.E6 GGL
        (frameRoots σ) := by
  let F := actualQuadraticSubfield f
  have hsq : e6IsogenyAlgebraic.comp
        ((minBC e6Data_valid F.subtype).comp Ψ) =
      (baseChangeGL F.subtype).comp
        ((adjointGroup Tag.E6 F).subtype.comp ρ) :=
    e6IsogenyAlgebraic_minBC_algebraic_square_actualQuadraticSubfield Ψ ρ hρ
  have hA : ((adjointGroup Tag.E6 F).subtype.comp ρ) A ∈
      rootSpan Tag.E6 F
        (frameRoots σ) := by
    change ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) A ∈
      rootSpan Tag.E6 (actualQuadraticSubfield f)
        {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j}
    rw [← hframe.range]
    exact ⟨A, rfl⟩
  change (e6IsogenyAlgebraic.comp
      ((minBC e6Data_valid F.subtype).comp Ψ)) A ∈
    rootSpan Tag.E6 GGL (frameRoots σ)
  rw [DFunLike.congr_fun hsq A]
  exact CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan F.subtype hA

set_option maxHeartbeats 2000000 in
theorem twisted_donor_adjoint_image_centralizes_rootDiag
    {f : ℕ} [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) σ)
    (a : Fin Tag.E6.rank → GGLˣ)
    (hα : rootChar a (σ 0 1) = 1)
    (hβ : rootChar a (σ 1 2) = 1) :
    ∀ A : SL(3, actualQuadraticSubfield f),
      rootDiagUnit Tag.E6 a *
          e6IsogenyAlgebraic
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A) =
        e6IsogenyAlgebraic
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A) *
          rootDiagUnit Tag.E6 a := by
  intro A
  have hneg : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = 1 → rootChar a (-v) = 1 := by
    intro v hv
    rw [show -v = 0 - v by simp, rootChar_sub, rootChar_zero, hv, inv_one, mul_one]
  have h10 : rootChar a (σ 1 0) = 1 := by
    rw [hframe.neg 0 1]
    exact hneg _ hα
  have h21 : rootChar a (σ 2 1) = 1 := by
    rw [hframe.neg 1 2]
    exact hneg _ hβ
  have h02 : rootChar a (σ 0 2) = 1 := by
    rw [← hframe.add 0 1 2, rootChar_add, hα, hβ, one_mul]
  have h20 : rootChar a (σ 2 0) = 1 := by
    rw [hframe.neg 0 2]
    exact hneg _ h02
  have hroot : ∀ i j : Fin 3, i ≠ j → rootChar a (σ i j) = 1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hsubset : frameRoots σ ⊆ rootCharKernel a := by
    rintro γ ⟨i, j, hij, rfl⟩
    exact ⟨hframe.isRoot i j hij, hroot i j hij⟩
  have hz : e6IsogenyAlgebraic
        (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A) ∈
      Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 GGL)) :=
    (rootSpan_le_centralizer (τ := Tag.E6) (K := GGL) a hsubset)
      (e6IsogenyAlgebraic_mem_frameRootSpan_actualQuadraticSubfield Ψ ρ σ hρ hframe A)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hz).symm

set_option maxHeartbeats 2000000 in
theorem e6_donor_minuscule_image_centralizes_toral_lift
    {f : ℕ} [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) σ)
    (a : Fin Tag.E6.rank → GGLˣ)
    (hα : rootChar a (σ 0 1) = 1) (hβ : rootChar a (σ 1 2) = 1)
    (d : e6Data_valid.minGroup GGL) (hd : e6IsogenyAlgebraic d = rootDiagUnit Tag.E6 a) :
    ∀ A : SL(3, actualQuadraticSubfield f),
      d * ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A =
        ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) A * d := by
  let lam := (minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ
  have hcent := twisted_donor_adjoint_image_centralizes_rootDiag
    Ψ ρ σ hρ hframe a hα hβ
  have heq : (MulAut.conj d).toMonoidHom.comp lam = lam := by
    apply algebraic_lift_unique_of_isogeny_eq
    intro A
    change e6IsogenyAlgebraic (d * lam A * d⁻¹) = e6IsogenyAlgebraic (lam A)
    rw [map_mul, map_mul, map_inv, hd, hcent A]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    rfl
  intro A
  have h := DFunLike.congr_fun heq A
  change d * lam A * d⁻¹ = lam A at h
  calc
    d * lam A = (d * lam A * d⁻¹) * d := by group
    _ = lam A * d := by rw [h]

set_option maxHeartbeats 2000000 in
theorem e6_common_lang_compact_image_centralizes_toral_lift
    {f : ℕ} [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) σ)
    (a : Fin Tag.E6.rank → GGLˣ)
    (hα : rootChar a (σ 0 1) = 1) (hβ : rootChar a (σ 1 2) = 1)
    (d c : e6Data_valid.minGroup GGL)
    (hd : e6IsogenyAlgebraic d = rootDiagUnit Tag.E6 a) :
    ∀ A : Su (actualQuadraticSubfield f) 2 f 3,
      (c * d * c⁻¹) * (c *
        ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
          (CFSG.ClassicalInvolution.Models.suToSL
            (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹) =
        (c * ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)
          (CFSG.ClassicalInvolution.Models.suToSL
            (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A) * c⁻¹) *
          (c * d * c⁻¹) := by
  intro A
  let B := CFSG.ClassicalInvolution.Models.suToSL
    (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3 A
  let lam := (minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ
  have h := e6_donor_minuscule_image_centralizes_toral_lift Ψ ρ σ hρ hframe a hα hβ d hd B
  change d * lam B = lam B * d at h
  change (c * d * c⁻¹) * (c * lam B * c⁻¹) =
    (c * lam B * c⁻¹) * (c * d * c⁻¹)
  calc
    _ = c * (d * lam B) * c⁻¹ := by group
    _ = c * (lam B * d) * c⁻¹ := by rw [h]
    _ = _ := by group

theorem twisted_originalU_compact_quotient_injective
    {f n : ℕ} [NeZero f] {Y : Type} [Group Y]
    (mu : (ggU .twistedE6 n f).K →* Y)
    (hmu : mu.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K)
    (hadj : Function.Injective
      ((ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta)) :
    Function.Injective (mu.comp theta) := by
  apply (MonoidHom.ker_eq_bot_iff (mu.comp theta)).mp
  apply le_antisymm _ bot_le
  intro A hA
  change A = 1
  apply hadj
  have hcent := hmu hA
  have hi : theta A ∈
      (ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).ker := by
    rw [ggIotaK_twistedE6_ker_eq_center]
    exact hcent
  change ggIotaK .twistedE6 n f _ (theta A) = ggIotaK .twistedE6 n f _ (theta 1)
  rw [map_one, map_one]
  exact MonoidHom.mem_ker.mp hi

theorem exists_twisted_originalU_marked_pair_mod_central
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    {Y : Type} [Group Y] (mu : (ggU .twistedE6 n f).K →* Y)
    (hmu : mu.ker ≤ Subgroup.center (ggU .twistedE6 n f).K) :
    ∃ (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
      (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup Tag.E6 (actualQuadraticSubfield f))
      (c : e6Data_valid.minGroup GGL)
      (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K),
      ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ ∧
      CFSG.RankThree.PartOne.KF4.IsA2Frame
        ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ)
        (fun i j => CFSG.RankThree.E6.chainRoot
          CFSG.RankThree.E6.chain13 i j) ∧
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) =
        e6rhoA2₁ (actualQuadraticSubfield f) ∧
      Function.Injective theta ∧ e6IsogenyAlgebraic c = M.D.g0 ∧
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp theta =
        (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) ∧
      (ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta =
        (MulAut.conj M.D.g0).toMonoidHom.comp
          (e6IsogenyAlgebraic.comp
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))) ∧
      Function.Injective (mu.comp theta) ∧
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f' : ℕ),
        Nat.card K = (2 ^ f') ^ 2 →
        Nat.card ((B12 (actualQuadraticSubfield f) 2 f).map (mu.comp theta)) =
          2 ^ f' * ((2 ^ f') ^ 2 - 1) →
        UnitaryBlockStandardPair K 2 f' (mu.comp theta).range
          ((B12 (actualQuadraticSubfield f) 2 f).map (mu.comp theta))
          ((B23 (actualQuadraticSubfield f) 2 f).map (mu.comp theta)) := by
  obtain ⟨Psi, rho, c, theta, hrho, hframe, heq, hinjTheta, hc, hmin, hcanonical, _hpair⟩ :=
    exists_twisted_originalU_minuscule_marked_pair_of_plus (n := n) M hp hp2 hplus
  have hsq := e6IsogenyAlgebraic_minBC_algebraic_square_actualQuadraticSubfield Psi rho hrho
  have hadj : Function.Injective
      ((ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta) := by
    rw [hcanonical]
    change Function.Injective ((MulAut.conj M.D.g0).toMonoidHom.comp
      ((e6IsogenyAlgebraic.comp
        ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Psi)).comp
        (CFSG.ClassicalInvolution.Models.suToSL
          (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)))
    rw [hsq]
    exact (MulAut.conj M.D.g0).injective.comp
      ((baseChangeGL_injective (actualQuadraticSubfield f).subtype).comp
        (hframe.injective.comp CFSG.ClassicalInvolution.Models.suToSL_injective))
  have hinj := twisted_originalU_compact_quotient_injective mu hmu theta hadj
  have hker : (mu.comp theta).ker ≤
      Subgroup.center (Su (actualQuadraticSubfield f) 2 f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker rfl rfl
  refine ⟨Psi, rho, c, theta, hrho, hframe, heq, hinjTheta, hc, hmin, hcanonical, hinj, ?_⟩
  intro K _ _ _ f' hK horder
  exact ggPhanNSAPairAux_stdPair_of_card
    (card_actualQuadraticSubfield (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))) hK hpair horder

theorem e6_donor_compact_block_images_le_rootSpans
    {f : ℕ} [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ) σ) :
    let mu := (e6IsogenyAlgebraic.comp
      ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ)).comp
        (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)
    (B12 (actualQuadraticSubfield f) 2 f).map mu ≤
      rootSpan Tag.E6 GGL {σ 0 1, -σ 0 1} ∧
    (B23 (actualQuadraticSubfield f) 2 f).map mu ≤
      rootSpan Tag.E6 GGL {σ 1 2, -σ 1 2} := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := actualQuadraticSubfield f
  have hsq := e6IsogenyAlgebraic_minBC_algebraic_square_actualQuadraticSubfield Ψ ρ hρ
  dsimp only
  constructor
  · rintro x ⟨y, ⟨A, rfl⟩, rfl⟩
    change (e6IsogenyAlgebraic.comp ((minBC e6Data_valid F.subtype).comp Ψ))
      (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution F 2 f) 3
        (embSUid (unitaryInvolution F 2 f) 2 A)) ∈ _
    rw [hsq]
    rw [embSUid_two_eq_blockEmb, suToSL_blockEmb]
    apply CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan F.subtype
    rw [← IsA2Frame.block0_rootSpan hframe]
    exact ⟨CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution F 2 f) 2 A, rfl⟩
  · rintro x ⟨y, ⟨A, rfl⟩, rfl⟩
    change (e6IsogenyAlgebraic.comp ((minBC e6Data_valid F.subtype).comp Ψ))
      (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution F 2 f) 3
        (embSUid (unitaryInvolution F 2 f) 0 A)) ∈ _
    rw [hsq]
    rw [embSUid_zero_eq_blockEmb, suToSL_blockEmb]
    apply CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan F.subtype
    rw [← IsA2Frame.block1_rootSpan hframe]
    exact ⟨CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution F 2 f) 2 A, rfl⟩

theorem twisted_donor_compact_block_images_eq_gamma
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (w : WeylGroup Tag.E6)
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ)
      (fun i j => w • chainRoot chain13 i j))
    (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K)
    (hsquare : (ggIotaK .twistedE6 n f
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta =
      (MulAut.conj M.D.g0).toMonoidHom.comp
        (e6IsogenyAlgebraic.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))))
    (ρF : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hFrob : FrobRootMap M.D ρF)
    (hrev : ∀ i j : Fin 3, i ≠ j →
      ρF (w • chainRoot chain13 i j) = w • chainRoot chain13 j i) :
    let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
      ((ggIotaK .twistedE6 n f
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta)
    Function.Injective phi ∧ phi.range ≤ M.D.Γ ∧
      phi.range = rootSpan Tag.E6 GGL
        (frameRoots (fun i j => w • chainRoot chain13 i j)) ⊓ M.D.Γ ∧
      (B12 (actualQuadraticSubfield f) 2 f).map phi =
        rootSpan Tag.E6 GGL
          {w • chainRoot chain13 0 1, -(w • chainRoot chain13 0 1)} ⊓ M.D.Γ ∧
      (B23 (actualQuadraticSubfield f) 2 f).map phi =
        rootSpan Tag.E6 GGL
          {w • chainRoot chain13 1 2, -(w • chainRoot chain13 1 2)} ⊓ M.D.Γ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)
  let F := actualQuadraticSubfield f
  let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
    ((ggIotaK .twistedE6 n f hf).comp theta)
  let mu := (e6IsogenyAlgebraic.comp
    ((minBC e6Data_valid F.subtype).comp Ψ)).comp
      (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution F 2 f) 3)
  have hphi : phi = mu := by
    apply MonoidHom.ext
    intro A
    change (MulAut.conj M.D.g0).symm
      (((ggIotaK .twistedE6 n f hf).comp theta) A) = mu A
    rw [DFunLike.congr_fun hsquare]
    exact (MulAut.conj M.D.g0).symm_apply_apply (mu A)
  have hinj : Function.Injective phi := by
    rw [hphi]
    dsimp only [mu]
    rw [e6IsogenyAlgebraic_minBC_algebraic_square_actualQuadraticSubfield Ψ ρ hρ]
    exact (baseChangeGL_injective F.subtype).comp
      (hframe.injective.comp CFSG.ClassicalInvolution.Models.suToSL_injective)
  have hΓ : phi.range ≤ M.D.Γ := by
    have hconj := M.map_conj_Γ_eq_ggIotaK_range (n := n) hf hp hp2 hreg
    rintro x ⟨A, rfl⟩
    have hx : ggIotaK .twistedE6 n f hf (theta A) ∈
        M.D.Γ.map (MulAut.conj M.D.g0).toMonoidHom := by
      rw [hconj]
      exact ⟨theta A, rfl⟩
    obtain ⟨y, hy, heq⟩ := hx
    change (MulAut.conj M.D.g0).symm
      (ggIotaK .twistedE6 n f hf (theta A)) ∈ M.D.Γ
    rw [← heq]
    change M.D.g0⁻¹ * (M.D.g0 * y * M.D.g0⁻¹) * M.D.g0 ∈ M.D.Γ
    have he : M.D.g0⁻¹ * (M.D.g0 * y * M.D.g0⁻¹) * M.D.g0 = y := by group
    rw [he]
    exact hy
  have hroot := e6_donor_compact_block_images_le_rootSpans Ψ ρ
    (fun i j => w • chainRoot chain13 i j) hρ hframe
  change (B12 F 2 f).map mu ≤ _ ∧ (B23 F 2 f).map mu ≤ _ at hroot
  have hwhole : mu.range ≤ rootSpan Tag.E6 GGL
      (frameRoots (fun i j => w • chainRoot chain13 i j)) := by
    rintro x ⟨A, rfl⟩
    exact e6IsogenyAlgebraic_mem_frameRootSpan_actualQuadraticSubfield Ψ ρ
      (fun i j => w • chainRoot chain13 i j) hρ hframe
        (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution F 2 f) 3 A)
  have hfr := (e6_base_frame (L := GGL)).transport w
  obtain ⟨psi, hpsi, hrange, hB0, hB1⟩ := compactA2Pair_of_LangDatum
    (τ := langTag .twistedE6)
    hf _ _ hfr M.D ρF hFrob hrev M.hq F
      (mem_actualQuadraticSubfield_iff f) (card_actualQuadraticSubfield hf)
  have hpsiΓ : psi.range ≤ M.D.Γ :=
    M.ggSu_range_le_model_Γ (n := n) hf hp hp2 hreg
      (card_actualQuadraticSubfield hf) psi (hrange.le.trans inf_le_right)
  have hΓmodel : M.D.Γ ≤ M.D.model := Subgroup.commutator_le_self M.D.model
  have hpsiSpan : psi.range = rootSpan Tag.E6 GGL
      (frameRoots (fun i j => w • chainRoot chain13 i j)) ⊓ M.D.Γ := by
    refine le_antisymm (le_inf (hrange.le.trans inf_le_left) hpsiΓ) ?_
    intro x hx
    exact hrange.ge ⟨hx.1, hΓmodel hx.2⟩
  have hleWhole : phi.range ≤ psi.range := by
    rw [hpsiSpan]
    exact le_inf (by rw [hphi]; exact hwhole) hΓ
  let : Finite psi.range := Finite.of_equiv (Su F 2 f 3)
    (MonoidHom.ofInjective hpsi).toEquiv
  have heqWhole : phi.range = psi.range :=
    Subgroup.eq_of_le_of_card_ge hleWhole (le_of_eq (Nat.card_congr
      ((MonoidHom.ofInjective hpsi).symm.trans (MonoidHom.ofInjective hinj)).toEquiv))
  have hB0Γ : (B12 F 2 f).map psi ≤ M.D.Γ := by
    rintro x ⟨y, _, rfl⟩
    exact hpsiΓ ⟨y, rfl⟩
  have hB1Γ : (B23 F 2 f).map psi ≤ M.D.Γ := by
    rintro x ⟨y, _, rfl⟩
    exact hpsiΓ ⟨y, rfl⟩
  have hB0' : (B12 F 2 f).map psi = rootSpan Tag.E6 GGL
      {w • chainRoot chain13 0 1, -(w • chainRoot chain13 0 1)} ⊓ M.D.Γ := by
    refine le_antisymm (le_inf (hB0.le.trans inf_le_left) hB0Γ) ?_
    intro x hx
    exact hB0.ge ⟨hx.1, hΓmodel hx.2⟩
  have hB1' : (B23 F 2 f).map psi = rootSpan Tag.E6 GGL
      {w • chainRoot chain13 1 2, -(w • chainRoot chain13 1 2)} ⊓ M.D.Γ := by
    refine le_antisymm (le_inf (hB1.le.trans inf_le_left) hB1Γ) ?_
    intro x hx
    exact hB1.ge ⟨hx.1, hΓmodel hx.2⟩
  have hphi0Γ : (B12 F 2 f).map phi ≤ M.D.Γ := by
    rintro x ⟨y, _, rfl⟩
    exact hΓ ⟨y, rfl⟩
  have hphi1Γ : (B23 F 2 f).map phi ≤ M.D.Γ := by
    rintro x ⟨y, _, rfl⟩
    exact hΓ ⟨y, rfl⟩
  have hle0 : (B12 F 2 f).map phi ≤ (B12 F 2 f).map psi := by
    rw [hB0']
    exact le_inf (by rw [hphi]; exact hroot.1) hphi0Γ
  have hle1 : (B23 F 2 f).map phi ≤ (B23 F 2 f).map psi := by
    rw [hB1']
    exact le_inf (by rw [hphi]; exact hroot.2) hphi1Γ
  let : Finite ((B12 F 2 f).map psi) := Finite.of_equiv (B12 F 2 f)
    ((B12 F 2 f).equivMapOfInjective psi hpsi).toEquiv
  let : Finite ((B23 F 2 f).map psi) := Finite.of_equiv (B23 F 2 f)
    ((B23 F 2 f).equivMapOfInjective psi hpsi).toEquiv
  have heq0 : (B12 F 2 f).map phi = (B12 F 2 f).map psi :=
    Subgroup.eq_of_le_of_card_ge hle0 (by
      rw [Subgroup.card_map_of_injective hpsi, Subgroup.card_map_of_injective hinj])
  have heq1 : (B23 F 2 f).map phi = (B23 F 2 f).map psi :=
    Subgroup.eq_of_le_of_card_ge hle1 (by
      rw [Subgroup.card_map_of_injective hpsi, Subgroup.card_map_of_injective hinj])
  exact ⟨hinj, hΓ, heqWhole.trans hpsiSpan, heq0.trans hB0', heq1.trans hB1'⟩

theorem exists_twisted_originalU_model_marked_pair_at_a2_pair
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    (hreg : GGExcRegime p f)
    {α β : Fin Tag.E6.rank → ℤ} (hpair : IsA2Pair α β) :
    ∃ (w : WeylGroup Tag.E6) (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
      (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup Tag.E6 (actualQuadraticSubfield f))
      (c : e6Data_valid.minGroup GGL)
      (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K),
      ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ ∧
      CFSG.RankThree.PartOne.KF4.IsA2Frame
        ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ)
        (fun i j => w • chainRoot chain13 i j) ∧
      w • chainRoot chain13 0 1 = α ∧ w • chainRoot chain13 1 2 = β ∧
      Function.Injective theta ∧ e6IsogenyAlgebraic c = M.D.g0 ∧
      ((minBC e6Data_valid (ggRatEmb (2 * f))).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype).comp theta =
        (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3)) ∧
      (ggIotaK .twistedE6 n f (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta =
        (MulAut.conj M.D.g0).toMonoidHom.comp
          (e6IsogenyAlgebraic.comp
            (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))) ∧
      let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
        ((ggIotaK .twistedE6 n f
          (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta)
      Function.Injective phi ∧ phi.range ≤ M.D.Γ ∧
        phi.range = rootSpan Tag.E6 GGL
          (frameRoots (fun i j => w • chainRoot chain13 i j)) ⊓ M.D.Γ ∧
        (B12 (actualQuadraticSubfield f) 2 f).map phi =
          rootSpan Tag.E6 GGL {α, -α} ⊓ M.D.Γ ∧
        (B23 (actualQuadraticSubfield f) 2 f).map phi =
          rootSpan Tag.E6 GGL {β, -β} ⊓ M.D.Γ ∧
        ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f' : ℕ),
          Nat.card K = (2 ^ f') ^ 2 →
          Nat.card ((B12 (actualQuadraticSubfield f) 2 f).map theta) =
            2 ^ f' * ((2 ^ f') ^ 2 - 1) →
          UnitaryBlockStandardPair K 2 f' theta.range
            ((B12 (actualQuadraticSubfield f) 2 f).map theta)
            ((B23 (actualQuadraticSubfield f) 2 f).map theta) := by
  obtain ⟨w, Ψ, ρ, c, theta, hρ, hframe, hwα, hwβ, hinj, hc, hmin, hcanonical, hfields⟩ :=
    exists_twisted_originalU_minuscule_marked_pair_at_a2_pair (n := n) M hp hp2 hplus hpair
  obtain ⟨ρF, hFrob⟩ := frobeniusOnRoots_proved (langTag .twistedE6) GGL M.D
  have hrev : ∀ i j : Fin 3, i ≠ j →
      ρF (w • chainRoot chain13 i j) = w • chainRoot chain13 j i := by
    intro i j hij
    rw [twisted_rho_neg_of_plus M hp hp2 hplus hFrob (hframe.isRoot i j hij)]
    exact (hframe.neg i j).symm
  obtain ⟨hphi, hΓ, hwhole, hB0, hB1⟩ :=
    twisted_donor_compact_block_images_eq_gamma M hp hp2 hreg w Ψ ρ
      hρ hframe theta hcanonical ρF hFrob hrev
  rw [hwα] at hB0
  rw [hwβ] at hB1
  exact ⟨w, Ψ, ρ, c, theta, hρ, hframe, hwα, hwβ, hinj, hc, hmin, hcanonical,
    hphi, hΓ, hwhole, hB0, hB1, hfields⟩

theorem twisted_donor_compact_blocks_eq_model_residuals
    {f p n : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) [NeZero f]
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (w : WeylGroup Tag.E6)
    (Ψ : SL(3, actualQuadraticSubfield f) →*
      e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
      adjointGroup Tag.E6 (actualQuadraticSubfield f))
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ)
    (hframe : CFSG.RankThree.PartOne.KF4.IsA2Frame
      ((adjointGroup Tag.E6 (actualQuadraticSubfield f)).subtype.comp ρ)
      (fun i j => w • chainRoot chain13 i j))
    (theta : Su (actualQuadraticSubfield f) 2 f 3 →* (ggU .twistedE6 n f).K)
    (hsquare : (ggIotaK .twistedE6 n f
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta =
      (MulAut.conj M.D.g0).toMonoidHom.comp
        (e6IsogenyAlgebraic.comp
          (((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL (unitaryInvolution (actualQuadraticSubfield f) 2 f) 3))))
    (ρF : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hFrob : FrobRootMap M.D ρF)
    (hrev : ∀ i j : Fin 3, i ≠ j →
      ρF (w • chainRoot chain13 i j) = w • chainRoot chain13 j i)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin Tag.E6.rank → GGLˣ)
    (a₁ : I₁ → Fin Tag.E6.rank → GGLˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) =
      {w • chainRoot chain13 0 1, -(w • chainRoot chain13 0 1)})
    (hk₁ : famKernel (Set.range a₁) =
      {w • chainRoot chain13 1 2, -(w • chainRoot chain13 1 2)}) :
    let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
      ((ggIotaK .twistedE6 n f
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta)
    ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
      (Set.range fun i => rootDiagUnit Tag.E6 (a₀ i))) =
        (B12 (actualQuadraticSubfield f) 2 f).map phi ∧
    ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
      (Set.range fun i => rootDiagUnit Tag.E6 (a₁ i))) =
        (B23 (actualQuadraticSubfield f) 2 f).map phi := by
  let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
    ((ggIotaK .twistedE6 n f
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))).comp theta)
  dsimp only
  obtain ⟨_hinj, _hΓ, _hwhole, hB₀, hB₁⟩ :=
    twisted_donor_compact_block_images_eq_gamma M hp hp2 hreg w Ψ ρ hρ hframe
      theta hsquare ρF hFrob hrev
  have hΓadj : M.D.Γ ≤ adjointGroup Tag.E6 GGL :=
    (Subgroup.commutator_le_self M.D.model).trans inf_le_left
  let theta₀ : Su (actualQuadraticSubfield f) 2 f 2 →* ModGL Tag.E6 GGL := phi.comp (embSUid (unitaryInvolution (actualQuadraticSubfield f) 2 f) 2)
  let theta₁ : Su (actualQuadraticSubfield f) 2 f 2 →* ModGL Tag.E6 GGL := phi.comp (embSUid (unitaryInvolution (actualQuadraticSubfield f) 2 f) 0)
  have hr₀ : theta₀.range = (B12 (actualQuadraticSubfield f) 2 f).map phi := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨embSUid (unitaryInvolution (actualQuadraticSubfield f) 2 f) 2 u,
        ⟨u, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  have hr₁ : theta₁.range = (B23 (actualQuadraticSubfield f) 2 f).map phi := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨embSUid (unitaryInvolution (actualQuadraticSubfield f) 2 f) 0 u,
        ⟨u, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  constructor
  · rw [← hr₀]
    apply LayerSixE.oTwoPrime_famCentralizer_eq_su_range_of_rootSpan hp hp2 a₀ ha₀
      M.D.Γ hΓadj
      (card_actualQuadraticSubfield (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)))
      (by decide : 2 ≤ 2) theta₀
    rw [hr₀, hk₀]
    exact hB₀
  · rw [← hr₁]
    apply LayerSixE.oTwoPrime_famCentralizer_eq_su_range_of_rootSpan hp hp2 a₁ ha₁
      M.D.Γ hΓadj
      (card_actualQuadraticSubfield (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f)))
      (by decide : 2 ≤ 2) theta₁
    rw [hr₁, hk₁]
    exact hB₁

end CFSG.StandardType.GGFinModel
