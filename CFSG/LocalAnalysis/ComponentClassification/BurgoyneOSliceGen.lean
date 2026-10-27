module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceAct
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNorm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat commute_signMat_iff
  mul_conj_mul_inv)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem slice_conj_propAConclusionIn (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    (hd : 5 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K}
    (hW : OSliceW (by omega : 4 ≤ d) w α a)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {t : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))} (ht : orderOf t = 2)
    {Pt : GL (Fin 2) K}
    (htP : ∀ x, t * conjProjH (matrixDerived (oQ (diagGL hw)))
        (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW x) * t⁻¹ =
      conjProjH (matrixDerived (oQ (diagGL hw)))
        (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW (conjSL Pt x)))
    (hPt : conjSL Pt unipSL1 ≠ unipSL1)
    (hcore : ∀ y ∈ oddCoreIn B t, ∃ P : GL (Fin 2) K,
      (∀ x, y * conjProjH (matrixDerived (oQ (diagGL hw)))
          (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW x) * y⁻¹ =
        conjProjH (matrixDerived (oQ (diagGL hw)))
          (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW (conjSL P x))) ∧
      ((∃ c : Kˣ, P = GeneralLinearGroup.scalar (Fin 2) c) → y = 1))
    {Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B t) : PropAConclusionIn B t Y := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd4 : 4 ≤ d := by omega
  have hK4 : 4 ≤ Nat.card K := by omega
  have hHeq : matrixDerived (oQ (diagGL hw)) = ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  have hHI : ∀ h : matrixDerived (oQ (diagGL hw)),
      (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) :=
    fun h => Subgroup.commutator_le_self _ (by rw [← hHeq]; exact h.2)
  set f := oSliceH h2 hK4 hd4 hw hW with hf
  have hfinj := oSliceH_injective h2 hK4 hd4 hw hW
  have hfm : ∀ x, ((f x : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
      oSlice K h2 hd4 hW.ha x := fun x => rfl
  set u₀ := f (-1) with hu₀
  have hu₀m : (((u₀ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = embed4 K hd4 (-1) := by
    rw [hu₀, hfm, coe_oSlice]
    congr 1
    exact qLambda_neg_one h2 hW.ha
  set e : f.range ≃* SL(2, K) := (MonoidHom.ofInjective hfinj).symm with he
  have he1 : ((e ⟨u₀, ⟨-1, rfl⟩⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    have : e ⟨u₀, ⟨-1, rfl⟩⟩ = -1 := by
      rw [he, MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    simp
  have hLZ : ∀ g ∈ f.range, g ∈ (StatedScalars (Fin d) K).subgroupOf
      (matrixDerived (oQ (diagGL hw))) → g = 1 := by
    rintro _ ⟨x, rfl⟩ ⟨c, hc⟩
    have hc' : GeneralLinearGroup.scalar (Fin d) c =
        ((f x : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) := hc
    have e44 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)
      ⟨4, by omega⟩ ⟨4, by omega⟩) hc'
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e44
    change (c : K) = (embed4 K hd4 (qLamMat h2 hW.ha x)) _ _ at e44
    rw [embed4_apply_of hd4 _ (Or.inl (by simp))] at e44
    simp only [↓reduceIte] at e44
    apply Subtype.ext
    rw [← hc', Subgroup.coe_one]
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, e44, Units.val_one, Matrix.scalar_apply, diagonal_one]
  have hLu : ∀ g ∈ f.range, g * u₀ = u₀ * g := by
    rintro _ ⟨x, rfl⟩
    rw [hu₀, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one,
      Matrix.one_mul]
  set M := (oBlock K hw wSet).subgroupOf (matrixDerived (oQ (diagGL hw))) with hM
  have hLM : f.range ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact mem_subgroupOf.2 (oSlice_mem_oBlock h2 hK4 hd4 hw hW x)
  have hcomm_u₀ : ∀ h : matrixDerived (oQ (diagGL hw)),
      (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        embed4 K hd4 (-1) = embed4 K hd4 (-1) *
          (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
      h * u₀ = u₀ * h := by
    intro h hh
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hu₀m]
    exact hh
  have hMu : ∀ g ∈ M, g * u₀ = u₀ * g := fun g hg => hcomm_u₀ g
    (commute_embed4_of_mem h2 hd4 hw (oBlock_le_oIsoBlock hw wSet (mem_subgroupOf.1 hg)))
  have hLn : ∀ m ∈ M, ∀ g ∈ f.range, m * g * m⁻¹ ∈ f.range := by
    rintro m hm _ ⟨x, rfl⟩
    have hnm := oBlock_le_normalizer h2 hd4 hw hW (mem_subgroupOf.1 hm)
    obtain ⟨x', hx'⟩ := (mem_normalizer_iff.1 hnm (oSlice K h2 hd4 hW.ha x)).1 ⟨x, rfl⟩
    exact ⟨x', Subtype.ext hx'⟩
  have hnorm : ∀ h : matrixDerived (oQ (diagGL hw)), h * u₀ = u₀ * h →
      ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
    intro h hh m hm
    have hhm : (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * embed4 K hd4 (-1) = embed4 K hd4 (-1) *
          (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have := congrArg (fun g : matrixDerived (oQ (diagGL hw)) => ((g : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)) hh
      simpa only [Subgroup.coe_mul, Units.val_mul, hu₀m] using this
    rw [embed4_neg_one] at hhm
    have hc := (commute_signMat_iff h2 _ _).1 hhm.symm
    exact mem_subgroupOf.2 (conj_mem_oBlock hw (hHI h) hc (mem_subgroupOf.1 hm))
  have hsl : ∀ b, b ∈ slice f.range ↔
      ∃ x, b = conjProjH (matrixDerived (oQ (diagGL hw))) (f x) := by
    intro b
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  have hinjS := conjProjH_injective_of_inf hinj hLZ
  have hfeq : ∀ x x', conjProjH (matrixDerived (oQ (diagGL hw))) (f x) =
      conjProjH (matrixDerived (oQ (diagGL hw))) (f x') → x = x' := by
    intro x x' h
    have := @hinjS ⟨f x, ⟨x, rfl⟩⟩ ⟨f x', ⟨x', rfl⟩⟩ h
    exact hfinj (congrArg Subtype.val this)
  have hnormS : ∀ s : MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))), ∀ P : GL (Fin 2) K,
      (∀ x, s * conjProjH (matrixDerived (oQ (diagGL hw))) (f x) * s⁻¹ =
        conjProjH (matrixDerived (oQ (diagGL hw))) (f (conjSL P x))) →
      s ∈ normalizer (slice f.range : Set (MulAut (StatedProj
        (matrixDerived (oQ (diagGL hw)))))) := by
    intro s P hs
    have hfwd : ∀ b ∈ slice f.range, s * b * s⁻¹ ∈ slice f.range := by
      intro b hb
      obtain ⟨x, rfl⟩ := (hsl b).1 hb
      rw [hs]
      exact (hsl _).2 ⟨_, rfl⟩
    have hbwd : ∀ b ∈ slice f.range, s⁻¹ * b * s⁻¹⁻¹ ∈ slice f.range := by
      intro b hb
      obtain ⟨x, rfl⟩ := (hsl b).1 hb
      refine (hsl _).2 ⟨conjSL P⁻¹ x, ?_⟩
      have hx : conjSL P (conjSL P⁻¹ x) = x := by
        apply Subtype.ext
        rw [coe_conjSL, coe_conjSL, inv_inv]
        calc (P : Matrix (Fin 2) (Fin 2) K) * (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            (x : Matrix (Fin 2) (Fin 2) K) * P) * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
            = ((P * P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
                (x : Matrix (Fin 2) (Fin 2) K) *
              ((P * P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
              simp only [Units.val_mul, Matrix.mul_assoc]
          _ = (x : Matrix (Fin 2) (Fin 2) K) := by
              rw [mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      conv_lhs => rw [← hx, ← hs]
      group
    rw [mem_normalizer_iff]
    intro b
    refine ⟨hfwd b, fun hb => ?_⟩
    have := hbwd _ hb
    simpa [mul_assoc] using this
  have htN := hnormS t Pt htP
  have htC : ∃ b ∈ slice f.range, t * b ≠ b * t := by
    refine ⟨_, (hsl _).2 ⟨unipSL1, rfl⟩, fun h => hPt (hfeq _ _ ?_)⟩
    rw [← htP, h, mul_inv_cancel_right]
  have hON : oddCoreIn B t ≤ normalizer (slice f.range : Set (MulAut (StatedProj
      (matrixDerived (oQ (diagGL hw)))))) := by
    intro y hy
    obtain ⟨P, hP, -⟩ := hcore y hy
    exact hnormS y P hP
  have hOC : ∀ y ∈ oddCoreIn B t, (∀ b ∈ slice f.range, y * b = b * y) → y = 1 := by
    intro y hy hcomm
    obtain ⟨P, hP, hP1⟩ := hcore y hy
    refine hP1 (eq_scalar_of_conjSL_eq fun x => ?_)
    apply hfeq
    rw [← hP x, hcomm _ ((hsl _).2 ⟨x, rfl⟩), mul_inv_cancel_right]
  exact slice_propAConclusionIn₂ hinj hB hLZ hK hK4 ⟨-1, rfl⟩ e he1 hLu hLM hMu hLn hnorm ht
    hY hYO htN htC hON hOC

end CFSG.ComponentClassification.Burgoyne.O
