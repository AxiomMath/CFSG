module

public import CFSG.ClassicalInvolution.Q3.Q3TWWKlein
public import CFSG.ClassicalInvolution.Q3.Q3TWWBElt
public import CFSG.ClassicalInvolution.Q3.Q3TWWAutB
public import CFSG.ClassicalInvolution.Q3.Q3ZAutAbs
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjMain
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
public import CFSG.LieType.TitsSimplicity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT.SU4
open scoped MatrixGroups

structure TwistedLayer (H : Type) [Group H] where
  lbZ : SL(2, ZMod 3) →* H
  S : Subgroup H
  e : Fin 12 → H
  rels : RelsHold e su4Words
  e2 : e 2 = lbZ autXp
  e3 : e 3 = lbZ autXm
  eS6 : e 6 ∈ S
  eS7 : e 7 ∈ S
  eS8 : e 8 ∈ S
  eS9 : e 9 ∈ S
  B : H
  B_lb : ∀ A, B⁻¹ * lbZ A * B = lbZ ((absD 0)⁻¹ * A * absD 0)
  B_S : ∀ s ∈ S, B * s * B⁻¹ ∈ S
  B_S' : ∀ s ∈ S, B⁻¹ * s * B ∈ S

section Model

variable
  {F K : Type} [Field F] [Finite F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (D : KleinData F K σ₀ b c)
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem PhiSU_lb_tv01 :
    D.PhiSU hirr h2 (minusLongBlock b c (tv 0 1 1)) =
      sulong σ₀ 1 (by decide) D.ε D.σ_ε := by
  refine Subtype.ext (Units.ext ?_)
  rw [KleinData.coe_PhiSU D hirr h2, minusLongBlock_tv01, D.PhiMon_long_e0f1]
  show longRootMatrix 1 (algebraMap F K 1 * D.ε) = longRootMatrix 1 D.ε
  rw [map_one, one_mul]

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem PhiSU_lb_tv10 :
    D.PhiSU hirr h2 (minusLongBlock b c (tv 1 0 1)) =
      sulong σ₀ 2 (by decide) D.δ D.σ_δ := by
  refine Subtype.ext (Units.ext ?_)
  rw [KleinData.coe_PhiSU D hirr h2, minusLongBlock_tv10, D.PhiMon_long_e1f0]
  show longRootMatrix 2 (algebraMap F K 1 * D.δ) = longRootMatrix 2 D.δ
  rw [map_one, one_mul]

theorem PhiSU_sb_tv01 (t : ShortField b c) :
    D.PhiSU hirr h2 (shortBlock hirr 3 finOne (tv 0 1 t)) =
      suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide)
        (-(D.δ * (algebraMap F K (fieldCoord t 0) - algebraMap F K (fieldCoord t 1) * D.ω))) := by
  refine Subtype.ext (Units.ext ?_)
  rw [KleinData.coe_PhiSU D hirr h2, shortBlock_tv01]
  exact D.PhiMon_short_e1 hirr (fieldCoord t)

theorem PhiSU_sb_tv10 (t : ShortField b c) :
    D.PhiSU hirr h2 (shortBlock hirr 3 finOne (tv 1 0 t)) =
      suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide)
        (D.ε * (algebraMap F K (starCoord t 0) + algebraMap F K (starCoord t 1) *
          algebraMap F K b + algebraMap F K (starCoord t 1) * D.ω)) := by
  refine Subtype.ext (Units.ext ?_)
  rw [KleinData.coe_PhiSU D hirr h2, shortBlock_tv10]
  exact D.PhiMon_short_f1 hirr (starCoord t)

theorem exists_sb_tv01 (c'' : K) : ∃ t : ShortField b c,
    D.PhiSU hirr h2 (shortBlock hirr 3 finOne (tv 0 1 t)) =
      suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide) c'' := by
  obtain ⟨u, v, hx⟩ := D.span (-(c'' * D.ε))
  obtain ⟨t, ht⟩ := exists_fieldCoord_eq (b := b) (c := c) ![u, v]
  refine ⟨t, ?_⟩
  rw [PhiSU_sb_tv01 D hirr h2 t, ht]
  have : -(D.δ * (algebraMap F K (![u, v] 0) - algebraMap F K (![u, v] 1) * D.ω)) = c'' := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hx]
    linear_combination c'' * D.δ_mul_ε
  rw [this]

theorem exists_sb_tv10 (c'' : K) : ∃ t : ShortField b c,
    D.PhiSU hirr h2 (shortBlock hirr 3 finOne (tv 1 0 t)) =
      suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide) c'' := by
  obtain ⟨u, v, hy⟩ := D.span (c'' * D.δ)
  obtain ⟨t, ht⟩ := exists_starCoord_eq (b := b) (c := c) ![u + v * b, -v]
  refine ⟨t, ?_⟩
  rw [PhiSU_sb_tv10 D hirr h2 t, ht]
  have : D.ε * (algebraMap F K (![u + v * b, -v] 0) + algebraMap F K (![u + v * b, -v] 1) *
      algebraMap F K b + algebraMap F K (![u + v * b, -v] 1) * D.ω) = c'' := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, map_neg]
    have h3 : algebraMap F K u + algebraMap F K v * algebraMap F K b +
        -algebraMap F K v * algebraMap F K b + -algebraMap F K v * D.ω = c'' * D.δ := by
      rw [hy]
      ring
    rw [h3]
    linear_combination c'' * D.δ_mul_ε
  rw [this]

theorem sb_conj_mem (g : spinGroup (quadMinus 3 F b c))
    (hg01 : ∀ c'', D.PhiSU hirr h2 g * suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide) c'' *
      (D.PhiSU hirr h2 g)⁻¹ = suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide) (-σ₀ c''))
    (hg10 : ∀ c'', D.PhiSU hirr h2 g * suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide) c'' *
      (D.PhiSU hirr h2 g)⁻¹ = suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide) (-σ₀ c''))
    (s : spinGroup (quadMinus 3 F b c)) (hs : s ∈ (shortBlock hirr 3 finOne).range) :
    g * s * g⁻¹ ∈ (shortBlock hirr 3 finOne).range := by
  have hinj := D.PhiSU_injective hirr h2
  obtain ⟨A, rfl⟩ := hs
  refine sl2_mem_of_tv ((MulAut.conj g).toMonoidHom.comp (shortBlock hirr 3 finOne))
    (H := (shortBlock hirr 3 finOne).range) (fun t => ?_) (fun t => ?_) A
  · obtain ⟨t', ht'⟩ := exists_sb_tv10 D hirr h2
      (-σ₀ (-(D.δ * (algebraMap F K (fieldCoord t 0) -
        algebraMap F K (fieldCoord t 1) * D.ω))))
    refine ⟨tv 1 0 t', hinj ?_⟩
    rw [ht']
    show _ = D.PhiSU hirr h2 (g * shortBlock hirr 3 finOne (tv 0 1 t) * g⁻¹)
    rw [(D.PhiSU hirr h2).map_mul, (D.PhiSU hirr h2).map_mul, (D.PhiSU hirr h2).map_inv,
      PhiSU_sb_tv01 D hirr h2 t]
    exact (hg01 _).symm
  · obtain ⟨t', ht'⟩ := exists_sb_tv01 D hirr h2
      (-σ₀ (D.ε * (algebraMap F K (starCoord t 0) + algebraMap F K (starCoord t 1) *
        algebraMap F K b + algebraMap F K (starCoord t 1) * D.ω)))
    refine ⟨tv 0 1 t', hinj ?_⟩
    rw [ht']
    show _ = D.PhiSU hirr h2 (g * shortBlock hirr 3 finOne (tv 1 0 t) * g⁻¹)
    rw [(D.PhiSU hirr h2).map_mul, (D.PhiSU hirr h2).map_mul, (D.PhiSU hirr h2).map_inv,
      PhiSU_sb_tv10 D hirr h2 t]
    exact (hg10 _).symm

section LayerOf

variable [CharP K 3]

theorem exists_twistedLayer_of (hσ : ∀ x, σ₀ x = x ^ 3) (hε : D.ε ^ 2 = -1) (hδ : D.δ = -D.ε)
    (hsurj : Function.Surjective (D.PhiSU hirr h2))
    (lbZ : SL(2, ZMod 3) →* spinGroup (quadMinus 3 F b c))
    (hlbp : lbZ autXp = minusLongBlock b c (tv 0 1 1))
    (hlbm : lbZ autXm = minusLongBlock b c (tv 1 0 1)) :
    ∃ L : TwistedLayer (spinGroup (quadMinus 3 F b c)),
      L.lbZ = lbZ ∧ L.S = (shortBlock hirr 3 finOne).range := by
  classical
  have hinj := D.PhiSU_injective hirr h2
  let ePhi : spinGroup (quadMinus 3 F b c) ≃* SU σ₀ 4 :=
    MulEquiv.ofBijective (D.PhiSU hirr h2) ⟨hinj, hsurj⟩
  have hsymm : ∀ (g : SU σ₀ 4) (x : spinGroup (quadMinus 3 F b c)),
      g = D.PhiSU hirr h2 x → ePhi.symm g = x := fun g x h => (MulEquiv.symm_apply_eq ePhi).2 h
  have hPB : D.PhiSU hirr h2 (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε)) = suB σ₀ hσ D.σσ D.ε hε :=
    ePhi.apply_symm_apply _
  have hE2 : ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 2) = lbZ autXp := by
    refine hsymm _ _ ?_
    rw [hlbp]
    exact (PhiSU_lb_tv01 D hirr h2).symm
  have hE3 : ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 3) = lbZ autXm := by
    refine hsymm _ _ ?_
    rw [hlbm, PhiSU_lb_tv10 D hirr h2]
    refine Subtype.ext (Units.ext ?_)
    show longRootMatrix 2 (-D.ε) = longRootMatrix 2 D.δ
    rw [hδ]
  have hB2 : ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 2) * ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) =
      ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) * (ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 3) *
        ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 3)) := by
    have := congrArg ePhi.symm (suLetter_conj2 σ₀ hσ D.σσ D.ε hε)
    simpa only [map_mul] using this
  have hB3 : ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 3) * ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) =
      ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) * (ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 2) *
        ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε 2)) := by
    have := congrArg ePhi.symm (suLetter_conj3 σ₀ hσ D.σσ D.ε hε)
    simpa only [map_mul] using this
  have hcube : ∀ j, ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j) *
      ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j) * ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j) = 1 := by
    intro j
    have := congrArg ePhi.symm (suLetter_cube σ₀ hσ D.σσ D.ε hε j)
    simpa only [map_mul, map_one] using this
  have hinv : ∀ j, (ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j))⁻¹ =
      ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j) * ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j) :=
    fun j => inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hcube j)
  have hconj2 : (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹ * lbZ autXp *
      ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) = (lbZ autXm)⁻¹ := by
    rw [← hE2, ← hE3, hinv, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact hB2
  have hconj3 : (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹ * lbZ autXm *
      ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) = (lbZ autXp)⁻¹ := by
    rw [← hE2, ← hE3, hinv, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact hB3
  have hBlb : ∀ A, (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹ * lbZ A *
      ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) = lbZ ((absD 0)⁻¹ * A * absD 0) := by
    intro A
    have key : (MulAut.conj (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹).toMonoidHom.comp lbZ =
        lbZ.comp (MulAut.conj (absD 0)⁻¹).toMonoidHom := by
      refine hom_ext_of_gens ?_ ?_
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [absD0_inv_conj_xp, map_inv]
        exact hconj2
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [absD0_inv_conj_xm, map_inv]
        exact hconj3
    have := DFunLike.congr_fun key A
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      this
  have hBS : ∀ s ∈ (shortBlock hirr 3 finOne).range,
      ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) * s * (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹ ∈
        (shortBlock hirr 3 finOne).range := fun s hs =>
    sb_conj_mem D hirr h2 _ (fun c'' => by rw [hPB]; exact suB_conj01 σ₀ hσ D.σσ D.ε hε c'')
      (fun c'' => by rw [hPB]; exact suB_conj10 σ₀ hσ D.σσ D.ε hε c'') s hs
  have hBS' : ∀ s ∈ (shortBlock hirr 3 finOne).range,
      (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹ * s * ePhi.symm (suB σ₀ hσ D.σσ D.ε hε) ∈
        (shortBlock hirr 3 finOne).range := fun s hs => by
    have h := sb_conj_mem D hirr h2 (ePhi.symm (suB σ₀ hσ D.σσ D.ε hε))⁻¹
      (fun c'' => by
        rw [map_inv, hPB, inv_inv]
        exact suB_inv_conj01 σ₀ hσ D.σσ D.ε hε c'')
      (fun c'' => by
        rw [map_inv, hPB, inv_inv]
        exact suB_inv_conj10 σ₀ hσ D.σσ D.ε hε c'') s hs
    rwa [inv_inv] at h
  obtain ⟨t6, h6⟩ := exists_sb_tv01 D hirr h2 1
  obtain ⟨t7, h7⟩ := exists_sb_tv01 D hirr h2 D.ε
  obtain ⟨t8, h8⟩ := exists_sb_tv10 D hirr h2 1
  obtain ⟨t9, h9⟩ := exists_sb_tv10 D hirr h2 D.ε
  refine ⟨{ lbZ := lbZ, S := (shortBlock hirr 3 finOne).range,
            e := fun j => ePhi.symm (suLetter σ₀ hσ D.σσ D.ε hε j),
            rels := relsHold_hom (ePhi.symm : SU σ₀ 4 →* spinGroup (quadMinus 3 F b c))
              (relsHold_suLetter σ₀ hσ D.σσ D.ε hε),
            e2 := hE2, e3 := hE3,
            eS6 := ⟨tv 0 1 t6, (hsymm _ _ h6.symm).symm⟩,
            eS7 := ⟨tv 0 1 t7, (hsymm _ _ h7.symm).symm⟩,
            eS8 := ⟨tv 1 0 t8, (hsymm _ _ h8.symm).symm⟩,
            eS9 := ⟨tv 1 0 t9, (hsymm _ _ h9.symm).symm⟩,
            B := ePhi.symm (suB σ₀ hσ D.σσ D.ε hε), B_lb := hBlb, B_S := hBS, B_S' := hBS' },
    rfl, rfl⟩

end LayerOf

end Model

end CFSG.ClassicalInvolution.Q3.Q3TW
