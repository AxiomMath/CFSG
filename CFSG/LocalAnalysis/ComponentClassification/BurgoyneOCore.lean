module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat
  signMat_mul_self commute_signMat_iff commute_compInd_compl isSubnormal_subgroupOf_of_normalizes
  mul_conj_mul_inv)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def linPair {Q : QuadraticForm K (Fin d → K)} (A : GL (Fin d) K)
    (hA : A ∈ matrixIsometries Q) : similarityPairs Q :=
  ⟨⟨A, 1⟩, ⟨1, fun v => by
    rw [coordinateSemilinearMap_apply]
    change Q (matrixLinearEquiv A v) = _
    rw [(mem_matrixIsometries_iff Q A).1 hA v]
    simp⟩⟩

theorem linPair_left {Q : QuadraticForm K (Fin d → K)} (A : GL (Fin d) K)
    (hA : A ∈ matrixIsometries Q) : (linPair A hA).val.left = A := rfl

theorem linPair_right {Q : QuadraticForm K (Fin d → K)} (A : GL (Fin d) K)
    (hA : A ∈ matrixIsometries Q) : (linPair A hA).val.right = 1 := rfl

theorem coe_conj_linPair {Q : QuadraticForm K (Fin d → K)} (A : GL (Fin d) K)
    (hA : A ∈ matrixIsometries Q) (X : matrixDerived Q) :
    ((matrixDerivedConjugation Q (linPair A hA) X : matrixDerived Q) : GL (Fin d) K) =
      A * X * A⁻¹ := by
  rw [matrixDerivedConjugation_val, linPair_left, linPair_right, map_one, MulAut.one_apply]

variable (K) in
@[expose] def signGL (J : Finset (Fin d)) : GL (Fin d) K :=
  ⟨signMat K J, signMat K J, signMat_mul_self J, signMat_mul_self J⟩

theorem coe_signGL (J : Finset (Fin d)) :
    ((signGL K J : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = signMat K J := rfl

theorem signGL_inv (J : Finset (Fin d)) : (signGL K J)⁻¹ = signGL K J :=
  inv_eq_of_mul_eq_one_right (Units.ext (signMat_mul_self J))

theorem signGL_mem {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    signGL K J ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := by
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_signGL, coe_diagGL, signMat,
    diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> ring

theorem diagGL_transpose {w : Fin d → K} (hw : ∀ i, w i ≠ 0) :
    ((diagGL hw : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ = diagGL hw := by
  rw [coe_diagGL]
  exact diagonal_transpose _

@[expose] def sgnPair (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J : Finset (Fin d)) : similarityPairs (oQ (diagGL hw)) :=
  linPair (signGL K J) ((mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).2
    (signGL_mem hw J))

theorem two_mul_card_eq_of_anticommute (h2 : (2 : K) ≠ 0) {J : Finset (Fin d)}
    {h : GL (Fin d) K}
    (hh : signMat K J * (h : Matrix (Fin d) (Fin d) K) = -((h : Matrix (Fin d) (Fin d) K) *
      signMat K J)) : 2 * J.card = d := by
  classical
  set H := (h : Matrix (Fin d) (Fin d) K) with hH
  set Hi := ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hHi
  have e1 : Hi * H = 1 := by rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconj : Hi * (signMat K J - 1) * H = -signMat K J - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hh, Matrix.mul_neg, ← Matrix.mul_assoc,
      e1, Matrix.one_mul, Matrix.mul_one, e1]
  have hdetH : IsUnit H.det := by
    rw [hH]
    exact (Matrix.isUnits_det_units h)
  have hdetHi : IsUnit Hi.det := by
    rw [hHi]
    exact (Matrix.isUnits_det_units h⁻¹)
  have hrank : (signMat K J - 1).rank = (-signMat K J - 1).rank := by
    rw [← hconj, rank_mul_eq_left_of_isUnit_det H _ hdetH,
      rank_mul_eq_right_of_isUnit_det Hi _ hdetHi]
  have hS1 : signMat K J - 1 = diagonal fun i => if i ∈ J then (-2 : K) else 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ J <;> simp [signMat, hi]; ring
    · simp [signMat, hij, one_apply]
  have hS2 : -signMat K J - 1 = diagonal fun i => if i ∈ J then (0 : K) else -2 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ J <;> simp [signMat, hi]; ring
    · simp [signMat, hij, one_apply]
  have h2' : (-2 : K) ≠ 0 := neg_ne_zero.2 h2
  rw [hS1, hS2, rank_diagonal, rank_diagonal] at hrank
  have c1 : Fintype.card {i // (if i ∈ J then (-2 : K) else 0) ≠ 0} = J.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext i
    by_cases hi : i ∈ J <;> simp [hi, h2']
  have c2 : Fintype.card {i // (if i ∈ J then (0 : K) else -2) ≠ 0} = d - J.card := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin d => (if i ∈ J then (0 : K) else -2) ≠ 0) = Jᶜ := by
      ext i
      by_cases hi : i ∈ J <;> simp [hi, h2']
    rw [this, Finset.card_compl, Fintype.card_fin]
  rw [c1, c2] at hrank
  have := J.card_le_univ
  rw [Fintype.card_fin] at this
  omega

theorem commute_signMat_of_mem_oIsoBlock (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) {g : GL (Fin d) K}
    (hg : g ∈ oIsoBlock K hw I) :
    signMat K J * (g : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin d) (Fin d) K) * signMat K J := by
  obtain ⟨-, hg1, hg2⟩ := hg
  rw [commute_signMat_iff h2]
  have hcI : compInd K I * (g : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin d) (Fin d) K) * compInd K I := by rw [hg1, hg2]
  rcases hI with rfl | rfl
  · exact hcI
  · have := commute_compInd_compl hcI
    rwa [compl_compl] at this

variable [Finite K]


theorem block_fix_of_components (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {J : Finset (Fin d)} (hJd : 2 * J.card ≠ d) {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
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
  obtain ⟨hle, hsub⟩ := isSubnormal_map_fixedH hinj hB φ hφt hF1 hF2
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
    have hQim := isQuasisimple_map_conjProjH hinj hLhq
    have hQsub : ((Lh.map (conjProjH (matrixDerived (oQ (diagGL hw))))).subgroupOf
        (B ⊓ centralizer ({t} : Set _))).IsSubnormal := by
      refine isSubnormal_subgroupOf_of_normalizes (map_mono hLF) ?_ hsub
      rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
      refine ⟨x * l * x⁻¹, mem_subgroupOf.2 ?_, by simp only [map_mul, map_inv]⟩
      have hx' : (x : GL (Fin d) K) ∈ oBlock K hw I := mem_subgroupOf.1 hx
      have hl' : (l : GL (Fin d) K) ∈ L i := mem_subgroupOf.1 hl
      simpa using hLn _ hx' _ hl'
    have hc := commute_of_mem_pPrimeCore ((map_mono hLF).trans hle) hQim hQsub
      (even_card_of_isQuasisimple hQim) hy ⟨Y, mem_subgroupOf.2 hY, rfl⟩
    apply hinj
    rw [← mul_conj_mul_inv]
    change _ * conjProjH (matrixDerived (oQ (diagGL hw))) Y * _ =
      conjProjH (matrixDerived (oQ (diagGL hw))) Y
    rw [hc, mul_inv_cancel_right]
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

end CFSG.ComponentClassification.Burgoyne.O
