module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenFix
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphFix

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat signMat_eq
  signMat_mul_self commute_signMat_iff commute_compInd_compl compInd_compl mul_conj_mul_inv)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem ClO.block_fix_gen (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {J : Finset (Fin d)} {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
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
  have hIH : ∀ I' : Finset (Fin d), oBlock K hw I' ≤ matrixDerived (oQ (diagGL hw)) :=
    fun I' => by rw [hHeq]; exact oBlock_le hw I'
  have hsupH : oBlock K hw J ⊔ oBlock K hw Jᶜ ≤ matrixDerived (oQ (diagGL hw)) :=
    sup_le (hIH J) (hIH Jᶜ)
  set F := (oBlock K hw J ⊔ oBlock K hw Jᶜ).subgroupOf (matrixDerived (oQ (diagGL hw))) with hF
  have hFS : oBlock K hw J ⊔ oBlock K hw Jᶜ ≤ centralizer ({signGL K J} : Set (GL (Fin d) K)) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_singleton_iff]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_signGL]
      exact (commute_signMat_of_mem_oIsoBlock h2 hw (Or.inl rfl)
        (oBlock_le_oIsoBlock hw _ hx)).symm
    · rw [mem_centralizer_singleton_iff]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_signGL]
      exact (commute_signMat_of_mem_oIsoBlock h2 hw (Or.inr rfl)
        (oBlock_le_oIsoBlock hw _ hx)).symm
  have hF1 : ∀ Y ∈ F, φ Y = Y := by
    intro Y hY
    apply Subtype.ext
    rw [hφc, signGL_inv]
    have hc := mem_centralizer_singleton_iff.1 (hFS (mem_subgroupOf.1 hY))
    rw [← hc, mul_assoc, show signGL K J * signGL K J = 1 from Units.ext (signMat_mul_self J),
      mul_one]
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
    have hhI : (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) :=
      Subgroup.commutator_le_self _ (by rw [← hHeq]; exact h.2)
    rw [mem_subgroupOf] at hY ⊢
    exact conj_mem_blockSup h2 hw hhI (mul_self_eq_one_iff.1 hc2) hcm hY
  obtain ⟨hperf, m, L, hsup, hL⟩ := oBlock_componentData hK hw hI3 hIexc
  have hIc : oBlock K hw J ⊔ oBlock K hw Jᶜ = oBlock K hw I ⊔ oBlock K hw Iᶜ := by
    rcases hI with rfl | rfl
    · rfl
    · rw [compl_compl, sup_comm]
  have hnorm : ∀ i, oBlock K hw J ⊔ oBlock K hw Jᶜ ≤ normalizer (L i : Set (GL (Fin d) K)) := by
    intro i
    rw [hIc]
    obtain ⟨-, hLI, hLn⟩ := hL i
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_normalizer_iff]
      intro l
      refine ⟨fun hl => hLn x hx l hl, fun hl => ?_⟩
      have := hLn x⁻¹ (inv_mem hx) _ hl
      simpa [mul_assoc] using this
    · rw [mem_normalizer_iff]
      intro l
      have hcomm : ∀ y ∈ oBlock K hw Iᶜ, ∀ l ∈ L i, y * l * y⁻¹ = l := fun y hy l hl => by
        rw [← commute_of_mem_oIsoBlock_compl hw (oBlock_le_oIsoBlock hw I (hLI hl))
          (oBlock_le_oIsoBlock hw Iᶜ hy), mul_inv_cancel_right]
      refine ⟨fun hl => by rw [hcomm x hx l hl]; exact hl, fun hl => ?_⟩
      have h1 := hcomm x⁻¹ (inv_mem hx) _ hl
      have h3 : l = x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ := by group
      rw [h3, h1]
      exact hl
  have hfixL : ∀ i, ∀ Y : matrixDerived (oQ (diagGL hw)), (Y : GL (Fin d) K) ∈ L i →
      oκ (oQ (diagGL hw)) g (projH (matrixDerived (oQ (diagGL hw))) Y) =
        projH (matrixDerived (oQ (diagGL hw))) Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L i).subgroupOf (matrixDerived (oQ (diagGL hw))) with hLh
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hLI.trans (hIH I))).symm hq
    have hLF : Lh ≤ F := fun Z hZ => mem_subgroupOf.2 (by
      have := hLI (mem_subgroupOf.1 hZ)
      rcases hI with rfl | rfl
      · exact mem_sup_left this
      · exact mem_sup_right this)
    have hLn' : ∀ x ∈ F, ∀ l ∈ Lh, x * l * x⁻¹ ∈ Lh := by
      intro x hx l hl
      have hx' : (x : GL (Fin d) K) ∈ oBlock K hw J ⊔ oBlock K hw Jᶜ := mem_subgroupOf.1 hx
      have hl' : (l : GL (Fin d) K) ∈ L i := mem_subgroupOf.1 hl
      have := (mem_normalizer_iff.1 (hnorm i hx') _).1 hl'
      exact mem_subgroupOf.2 (by simpa using this)
    exact ClU.fix_of_lift_sub hinj hRodd hRi hRc φ
      (matrixDerivedConjugation (oQ (diagGL hw)) (sgnPair h2 hw J)).injective hφt
      (fun Z hZ => hF1 Z hZ)
      (fun x hx Z hZ => hF2 x (by
        rw [show φ x = x from hx, inv_mul_cancel]
        exact one_mem _) Z hZ) hLF hLn' hLhq hy (mem_subgroupOf.2 hY)
  set FI := (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) with hFI
  have hFsup : FI ≤ MonoidHom.eqLocus ((oκ (oQ (diagGL hw)) g).toMonoidHom.comp
      (projH (matrixDerived (oQ (diagGL hw))))) (projH (matrixDerived (oQ (diagGL hw)))) := by
    intro Y hY
    have hY' : (Y : GL (Fin d) K) ∈ ⨆ i, L i := by rw [hsup]; exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L i).subgroupOf (matrixDerived (oQ (diagGL hw)))).map
        (matrixDerived (oQ (diagGL hw))).subtype = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans (hIH I))]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z hZ => ?_ :
      (⨆ i, (L i).subgroupOf (matrixDerived (oQ (diagGL hw)))) ≤ _) hY'L
    exact hfixL i Z (mem_subgroupOf.1 hZ)
  have hperfF : ⁅FI, FI⁆ = FI := by
    apply Subgroup.map_injective (matrixDerived (oQ (diagGL hw))).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hIH I), hperf]
  exact kappa_eq_of_fix g hperfF (fun Y hY => hFsup hY) (mem_subgroupOf.2 hX)

end CFSG.ComponentClassification.Foote5.OddLieCore
