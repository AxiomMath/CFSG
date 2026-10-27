module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat signMat_eq
  signMat_mul_self commute_signMat_iff commute_compInd_compl compInd_compl
  isSubnormal_subgroupOf_of_normalizes mul_conj_mul_inv)

variable {K : Type} [Field K] {d : ℕ}

theorem conj_mem_blockSup (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} {h : GL (Fin d) K}
    (hh : h ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw)) {c : K}
    (hc1 : c = 1 ∨ c = -1)
    (hcm : signMat K J * (h : Matrix (Fin d) (Fin d) K) * signMat K J =
      c • (h : Matrix (Fin d) (Fin d) K))
    {g : GL (Fin d) K} (hg : g ∈ oBlock K hw J ⊔ oBlock K hw Jᶜ) :
    h * g * h⁻¹ ∈ oBlock K hw J ⊔ oBlock K hw Jᶜ := by
  set H := (h : Matrix (Fin d) (Fin d) K) with hH
  have hSH : signMat K J * H = c • (H * signMat K J) := by
    calc signMat K J * H = signMat K J * H * signMat K J * signMat K J := by
          rw [Matrix.mul_assoc _ (signMat K J), signMat_mul_self, Matrix.mul_one]
      _ = c • (H * signMat K J) := by rw [hcm, Matrix.smul_mul]
  have hcase : (compInd K J * H = H * compInd K J ∧ compInd K Jᶜ * H = H * compInd K Jᶜ) ∨
      (compInd K J * H = H * compInd K Jᶜ ∧ compInd K Jᶜ * H = H * compInd K J) := by
    have hS' : (2 : K) • (compInd K J * H) - H = c • ((2 : K) • (H * compInd K J) - H) := by
      have := hSH
      rw [signMat_eq, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
        Matrix.mul_one, Matrix.mul_smul] at this
      exact this
    rcases hc1 with rfl | rfl
    · left
      rw [one_smul, sub_left_inj] at hS'
      have e' : compInd K J * H = H * compInd K J := smul_right_injective _ h2 hS'
      exact ⟨e', commute_compInd_compl e'⟩
    · right
      rw [neg_one_smul, neg_sub] at hS'
      have e1 : compInd K J * H = H - H * compInd K J := by
        apply smul_right_injective _ h2
        change (2 : K) • (compInd K J * H) = (2 : K) • (H - H * compInd K J)
        have h3 : (2 : K) • (compInd K J * H) = ((2 : K) • (compInd K J * H) - H) + H := by
          abel
        rw [h3, hS', smul_sub, two_smul K H]
        abel
      refine ⟨?_, ?_⟩
      · rw [compInd_compl, Matrix.mul_sub, Matrix.mul_one, e1]
      · rw [compInd_compl, Matrix.sub_mul, Matrix.one_mul, e1]
        abel
  have hsup : oBlock K hw J ⊔ oBlock K hw Jᶜ ≤
      (oBlock K hw J ⊔ oBlock K hw Jᶜ).comap (MulAut.conj h).toMonoidHom := by
    rcases hcase with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact mem_sup_left (conj_mem_oBlock_of hw hh h1 hx)
      · exact mem_sup_right (conj_mem_oBlock_of hw hh h2' hx)
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact mem_sup_right (conj_mem_oBlock_of hw hh h2' hx)
      · exact mem_sup_left (conj_mem_oBlock_of hw hh h1 hx)
  exact hsup hg

variable [Finite K]

theorem block_fix_gen (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {J : Finset (Fin d)} {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
    (hI3 : 3 ≤ I.card) (hIexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4))
    {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
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
  obtain ⟨hle, hsub⟩ := isSubnormal_map_fixedH hinj hB φ hφt hF1 hF2
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
    have hQim := isQuasisimple_map_conjProjH hinj hLhq
    have hQsub : ((Lh.map (conjProjH (matrixDerived (oQ (diagGL hw))))).subgroupOf
        (B ⊓ centralizer ({t} : Set _))).IsSubnormal := by
      refine isSubnormal_subgroupOf_of_normalizes (map_mono hLF) ?_ hsub
      rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
      refine ⟨x * l * x⁻¹, mem_subgroupOf.2 ?_, by simp only [map_mul, map_inv]⟩
      have hx' : (x : GL (Fin d) K) ∈ oBlock K hw J ⊔ oBlock K hw Jᶜ := mem_subgroupOf.1 hx
      have hl' : (l : GL (Fin d) K) ∈ L i := mem_subgroupOf.1 hl
      have := (mem_normalizer_iff.1 (hnorm i hx') _).1 hl'
      simpa using this
    have hc := commute_of_mem_pPrimeCore ((map_mono hLF).trans hle) hQim hQsub
      (even_card_of_isQuasisimple hQim) hy ⟨Y, mem_subgroupOf.2 hY, rfl⟩
    apply hinj
    rw [← mul_conj_mul_inv]
    change _ * conjProjH (matrixDerived (oQ (diagGL hw))) Y * _ =
      conjProjH (matrixDerived (oQ (diagGL hw))) Y
    rw [hc, mul_inv_cancel_right]
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

end CFSG.ComponentClassification.Burgoyne.O
