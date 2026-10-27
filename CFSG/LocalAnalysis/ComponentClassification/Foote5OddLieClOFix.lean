module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat
  signMat_mul_self commute_signMat_iff commute_compInd_compl mul_conj_mul_inv)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem ClO.block_fix_of_components (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {J : Finset (Fin d)} (hJd : 2 * J.card ≠ d) {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
    (hI3 : 3 ≤ I.card) (hIexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g : similarityPairs (oQ (diagGL hw))} (hy : oκ _ g ∈ Ro)
    {X : matrixDerived (oQ (diagGL hw))} (hX : (X : GL (Fin d) K) ∈ oBlock K hw I) :
    (g.val.left : Matrix (Fin d) (Fin d) K) *
        ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map g.val.right *
        ((g.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ (diagGL hw)) = ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  set t := oκ (oQ (diagGL hw)) (sgnPair h2 hw J) with ht
  set φ := (matrixDerivedConjugation (oQ (diagGL hw)) (sgnPair h2 hw J)).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ (diagGL hw)),
      ((φ Y : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
        signGL K J * Y * (signGL K J)⁻¹ :=
    fun Y => coe_conj_linPair _ _ Y
  have hφt : ∀ Y, t (projH (matrixDerived (oQ (diagGL hw))) Y) =
      projH (matrixDerived (oQ (diagGL hw))) (φ Y) := fun Y => kappa_lift _ Y
  have hIH : oBlock K hw I ≤ matrixDerived (oQ (diagGL hw)) := by rw [hHeq]; exact oBlock_le hw I
  set F := (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) with hF
  have hF1 : ∀ Y ∈ F, φ Y = Y := by
    intro Y hY
    apply Subtype.ext
    rw [hφc, signGL_inv]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_signGL, commute_signMat_of_mem_oIsoBlock h2 hw hI
      (oBlock_le_oIsoBlock hw I (mem_subgroupOf.1 hY)), Matrix.mul_assoc, signMat_mul_self,
      Matrix.mul_one]
  have hF2 : ∀ h : matrixDerived (oQ (diagGL hw)), h⁻¹ * φ h ∈
      (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ (diagGL hw))) →
      ∀ Y ∈ F, h * Y * h⁻¹ ∈ F := by
    intro h hh Y hY
    obtain ⟨c, hc⟩ := hh
    have hc' : ((h : GL (Fin d) K))⁻¹ * (signGL K J * h * signGL K J) =
        GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]
      change _ = ((h : GL (Fin d) K))⁻¹ * ((φ h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K)
      rw [hφc, signGL_inv]
    have hcm : signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J =
        (c : K) • ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have e := congrArg (fun M : GL (Fin d) K => ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (M : Matrix (Fin d) (Fin d) K)) hc'
      simp only [Units.val_mul, ← Matrix.mul_assoc, GeneralLinearGroup.coe_scalar] at e
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at e
      rw [coe_signGL] at e
      rw [e, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    have hc2 : (c : K) * c = 1 := by
      have e1 : signMat K J * (signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          signMat K J) *
          signMat K J = ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        simp only [← Matrix.mul_assoc, signMat_mul_self, Matrix.one_mul]
        rw [Matrix.mul_assoc, signMat_mul_self, Matrix.mul_one]
      rw [hcm, Matrix.mul_smul, Matrix.smul_mul, hcm, smul_smul] at e1
      have hne : ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ≠ 0 := by
        intro h0
        have : Nonempty (Fin d) := ⟨⟨0, by
          have := I.card_le_univ
          rw [Fintype.card_fin] at this
          omega⟩⟩
        have e0 := congrArg Matrix.det h0
        rw [Matrix.det_zero] at e0
        exact (Matrix.isUnits_det_units (h : GL (Fin d) K)).ne_zero e0
      have e2 : ((c : K) * c - 1) • ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 0 := by
        rw [sub_smul, one_smul, e1, sub_self]
      rcases smul_eq_zero.1 e2 with e3 | e3
      · exact sub_eq_zero.1 e3
      · exact absurd e3 hne
    have hcomm : signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J := by
      rcases mul_self_eq_one_iff.1 hc2 with hc1 | hc1
      · calc signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            (signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J) *
              signMat K J := by
              rw [Matrix.mul_assoc _ (signMat K J), signMat_mul_self, Matrix.mul_one]
          _ = _ := by rw [hcm, hc1, one_smul]
      · exfalso
        apply hJd
        refine two_mul_card_eq_of_anticommute h2 (h := (h : GL (Fin d) K)) ?_
        calc signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            (signMat K J * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J) *
              signMat K J := by
              rw [Matrix.mul_assoc _ (signMat K J), signMat_mul_self, Matrix.mul_one]
          _ = _ := by rw [hcm, hc1, neg_one_smul, Matrix.neg_mul]
    have hcI : compInd K I * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * compInd K I := by
      have h1 := (commute_signMat_iff h2 J _).1 hcomm
      rcases hI with rfl | rfl
      · exact h1
      · exact commute_compInd_compl h1
    have hhI : (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) :=
      Subgroup.commutator_le_self _ (by rw [← hHeq]; exact h.2)
    rw [mem_subgroupOf] at hY ⊢
    exact conj_mem_oBlock hw hhI hcI hY
  obtain ⟨hperf, m, L, hsup, hL⟩ := oBlock_componentData hK hw hI3 hIexc
  have hfixL : ∀ i, ∀ Y : matrixDerived (oQ (diagGL hw)), (Y : GL (Fin d) K) ∈ L i →
      oκ (oQ (diagGL hw)) g (projH (matrixDerived (oQ (diagGL hw))) Y) =
        projH (matrixDerived (oQ (diagGL hw))) Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L i).subgroupOf (matrixDerived (oQ (diagGL hw))) with hLh
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hLI.trans hIH)).symm hq
    have hLF : Lh ≤ F := fun Z hZ => mem_subgroupOf.2 (hLI (mem_subgroupOf.1 hZ))
    have hLn' : ∀ x ∈ F, ∀ l ∈ Lh, x * l * x⁻¹ ∈ Lh := by
      intro x hx l hl
      have hx' : (x : GL (Fin d) K) ∈ oBlock K hw I := mem_subgroupOf.1 hx
      have hl' : (l : GL (Fin d) K) ∈ L i := mem_subgroupOf.1 hl
      exact mem_subgroupOf.2 (by simpa using hLn _ hx' _ hl')
    exact ClU.fix_of_lift_sub hinj hRodd hRi hRc φ
      (matrixDerivedConjugation (oQ (diagGL hw)) (sgnPair h2 hw J)).injective hφt
      (fun Z hZ => hF1 Z hZ)
      (fun x hx Z hZ => hF2 x (by
        rw [show φ x = x from hx, inv_mul_cancel]
        exact one_mem _) Z hZ) hLF hLn' hLhq hy (mem_subgroupOf.2 hY)
  have hFsup : F ≤ MonoidHom.eqLocus ((oκ (oQ (diagGL hw)) g).toMonoidHom.comp
      (projH (matrixDerived (oQ (diagGL hw))))) (projH (matrixDerived (oQ (diagGL hw)))) := by
    intro Y hY
    have hY' : (Y : GL (Fin d) K) ∈ ⨆ i, L i := by rw [hsup]; exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L i).subgroupOf (matrixDerived (oQ (diagGL hw)))).map
        (matrixDerived (oQ (diagGL hw))).subtype = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hIH)]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z hZ => ?_ :
      (⨆ i, (L i).subgroupOf (matrixDerived (oQ (diagGL hw)))) ≤ _) hY'L
    exact hfixL i Z (mem_subgroupOf.1 hZ)
  have hperfF : ⁅F, F⁆ = F := by
    apply Subgroup.map_injective (matrixDerived (oQ (diagGL hw))).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hIH, hperf]
  exact kappa_eq_of_fix g hperfF (fun Y hY => hFsup hY) (mem_subgroupOf.2 hX)

end CFSG.ComponentClassification.Foote5.OddLieCore
