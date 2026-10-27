module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOAvg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOIdent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarIso
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOMinA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthData

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd)

variable {K : Type} [Field K] {d : ℕ}

theorem linPair_mul {Q : QuadraticForm K (Fin d → K)} {A B : GL (Fin d) K}
    (hA : A ∈ matrixIsometries Q) (hB : B ∈ matrixIsometries Q) :
    linPair (A * B) (mul_mem hA hB) = linPair A hA * linPair B hB := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change A * B = A * glFieldAut (Fin d) K 1 B
    rw [map_one, MulAut.one_apply]
  · change (1 : K ≃+* K) = 1 * 1
    rw [mul_one]

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem mem_matrixIsometries_of_mem_oIsoBlock (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)}
    {D : GL (Fin d) K} (hD : D ∈ oIsoBlock K hw I) : D ∈ matrixIsometries (oQ (diagGL hw)) :=
  (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) D).2 hD.1

@[expose] def oIsoHom (h2 : (2 : K) ≠ 0) (I : Finset (Fin d)) :
    oIsoBlock K hw I →* MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))) where
  toFun D := oκ _ (linPair D (mem_matrixIsometries_of_mem_oIsoBlock hw h2 D.2))
  map_one' := oκ_linPair_one _
  map_mul' A B := by
    rw [← map_mul, ← linPair_mul]
    rfl

theorem oIsoHom_injective (h2 : (2 : K) ≠ 0) (hker : OKer (oQ (diagGL hw))) {I : Finset (Fin d)}
    (hIne : I.Nonempty) : Function.Injective (oIsoHom hw h2 Iᶜ) := by
  rw [injective_iff_map_eq_one]
  intro D hD
  obtain ⟨-, c, hc⟩ := hker _ hD
  rw [linPair_left] at hc
  obtain ⟨i, hi⟩ := hIne
  have hii := ((mem_oIsoBlock_iff hw).1 D.2).2 i i (Or.inl (by simpa using hi))
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
    ite_eq_left (rfl : i = i)] at hii
  have hc1 : c = 1 := Units.ext hii
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc, hc1, map_one]

theorem mul_compInd_of_sign {A : Finset (Fin d)} (h2 : (2 : K) ≠ 0) {Y : Matrix (Fin d) (Fin d) K}
    (h1 : Y * (1 - signMat K A) = 1 - signMat K A) (hc : Y * signMat K A = signMat K A * Y) :
    compInd K Aᶜ * Y = compInd K Aᶜ ∧ Y * compInd K Aᶜ = compInd K Aᶜ := by
  have e : 1 - signMat K A = (2 : K) • compInd K Aᶜ := by
    rw [Burgoyne.PSL.signMat_eq, Burgoyne.PSL.compInd_compl, smul_sub, smul_one_eq_diagonal]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp; ring
  have hY : Y * compInd K Aᶜ = compInd K Aᶜ := by
    rw [e, Matrix.mul_smul] at h1
    exact smul_right_injective _ h2 h1
  have hcomm : Y * compInd K Aᶜ = compInd K Aᶜ * Y := by
    have e' : compInd K Aᶜ = (2 : K)⁻¹ • (1 - signMat K A) := by
      rw [e, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [e', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hc]
  exact ⟨hcomm ▸ hY, hY⟩

theorem mul_compInd_of_sign' {A : Finset (Fin d)} (h2 : (2 : K) ≠ 0)
    {Y : Matrix (Fin d) (Fin d) K} (h1 : Y * (1 + signMat K A) = 1 + signMat K A)
    (hc : Y * signMat K A = signMat K A * Y) :
    compInd K A * Y = compInd K A ∧ Y * compInd K A = compInd K A := by
  have e : 1 + signMat K A = (2 : K) • compInd K A := by
    rw [Burgoyne.PSL.signMat_eq]
    abel
  have hY : Y * compInd K A = compInd K A := by
    rw [e, Matrix.mul_smul] at h1
    exact smul_right_injective _ h2 h1
  have hcomm : Y * compInd K A = compInd K A * Y := by
    have e' : compInd K A = (2 : K)⁻¹ • (1 + signMat K A) := by
      rw [e, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [e', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hc]
  exact ⟨hcomm ▸ hY, hY⟩

theorem conj_mul_conj {X N : Matrix (Fin d) (Fin d) K} (S : GL (Fin d) K) (h : X * N = N) :
    ((S : Matrix (Fin d) (Fin d) K) * X * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S : Matrix (Fin d) (Fin d) K) * N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      (S : Matrix (Fin d) (Fin d) K) * N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have e : ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (S : Matrix (Fin d) (Fin d) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((S : Matrix (Fin d) (Fin d) K) * X * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S : Matrix (Fin d) (Fin d) K) * N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      (S : Matrix (Fin d) (Fin d) K) * X *
        (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (S : Matrix (Fin d) (Fin d) K)) *
          N * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one, Matrix.mul_assoc (S : Matrix (Fin d) (Fin d) K) X N, h]

include hw in
theorem exists_second_model [Finite K] (hK : ringChar K ≠ 2) (hker : OKer (oQ (diagGL hw)))
    {I : Finset (Fin d)} (hIne : I.Nonempty)
    {E : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))} (hE : IsPGroup 2 E)
    (hE1 : ∃ e ∈ E, e ≠ 1)
    (hrep : ∀ e ∈ E, ∃ (D : GL (Fin d) K) (hD : D ∈ matrixIsometries (oQ (diagGL hw))),
      D ∈ oIsoBlock K hw Iᶜ ∧ e = oκ _ (linPair D hD))
    {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} (hLE : L ≤ fixedBy E)
    (hLc : IsPComponent 2 (L.subgroupOf (fixedBy E)))
    {M : Subgroup (GL (Fin d) K)} (hMH : M ≤ matrixDerived (oQ (diagGL hw))) (hMp : ⁅M, M⁆ = M)
    (hML : (M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _) = L)
    (hMD : ∀ (D : GL (Fin d) K) (hD : D ∈ matrixIsometries (oQ (diagGL hw))),
      D ∈ oIsoBlock K hw Iᶜ → oκ _ (linPair D hD) ∈ E →
      ∀ X ∈ M, X * D = D * X ∧
        (X : Matrix (Fin d) (Fin d) K) * ((D : Matrix (Fin d) (Fin d) K) - 1) =
          (D : Matrix (Fin d) (Fin d) K) - 1) :
    ∃ (w' : Fin d → K) (hw' : ∀ i, w' i ≠ 0) (C : Finset (Fin d))
      (θ : StatedProj (matrixDerived (oQ (diagGL hw))) ≃*
        StatedProj (matrixDerived (oQ (diagGL hw')))),
      Cᶜ.Nonempty ∧ (3 ≤ C.card → BlockNF w' C) ∧
        L.map θ.toMonoidHom ≤ Burgoyne.C.blockP K hw' C ∧
        IsPComponent 2 ((L.map θ.toMonoidHom).subgroupOf (Burgoyne.C.blockP K hw' C)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψi := oIsoHom_injective hw h2 hker hIne
  set G₀ : Subgroup (oIsoBlock K hw Iᶜ) := E.comap (oIsoHom hw h2 Iᶜ) with hG₀
  set G : Subgroup (GL (Fin d) K) := G₀.map (oIsoBlock K hw Iᶜ).subtype with hG
  have hmemG : ∀ g, g ∈ G ↔ ∃ hg : g ∈ oIsoBlock K hw Iᶜ, oIsoHom hw h2 Iᶜ ⟨g, hg⟩ ∈ E := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hgE⟩
      exact ⟨⟨g, hg⟩, hgE, rfl⟩
  have : Fintype G := Fintype.ofFinite G
  have hG₀p : IsPGroup 2 G₀ := hE.of_injective
    (((oIsoHom hw h2 Iᶜ).comp G₀.subtype).codRestrict E fun x => x.2) (by
      intro a b hab
      apply Subtype.ext
      apply hψi
      exact congrArg Subtype.val hab)
  obtain ⟨k, hk⟩ := (hG₀p.map (oIsoBlock K hw Iᶜ).subtype).exists_card_eq
  have hGc : (Fintype.card G : K) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, hk, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero _ h2
  have hGI : ∀ g ∈ G, g ∈ oIsoBlock K hw Iᶜ := fun g hg => ((hmemG g).1 hg).1
  have hGiso : ∀ g ∈ G, ((g : Matrix (Fin d) (Fin d) K))ᵀ * (diagGL hw : Matrix (Fin d) (Fin d) K) *
      (g : Matrix (Fin d) (Fin d) K) = diagGL hw := fun g hg =>
    (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 (hGI g hg).1
  have hMG : ∀ X ∈ M, ∀ g ∈ G, X * g = g * X ∧
      (X : Matrix (Fin d) (Fin d) K) * ((g : Matrix (Fin d) (Fin d) K) - 1) =
        (g : Matrix (Fin d) (Fin d) K) - 1 := by
    intro X hX g hg
    obtain ⟨hgI, hgE⟩ := (hmemG g).1 hg
    exact hMD g (mem_matrixIsometries_of_mem_oIsoBlock hw h2 hgI) hgI hgE X hX
  have hS'2 := avgSign_mul_self hGc
  have hS'R := transpose_avgSign_mul hGc hGiso
  set S'GL : GL (Fin d) K := ⟨avgSign G, avgSign G, hS'2, hS'2⟩ with hS'GL
  have hS'iso : S'GL ∈ matrixIsometries (oQ (diagGL hw)) :=
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).2
      ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hS'R)
  obtain ⟨hab, cfr, hcA, horth, hdiag, -, hNF₂⟩ :=
    exists_split_nf hK (diagGL_transpose hw) hS'R hS'2
  obtain ⟨hw', S₂, hS₂, heq⟩ := exists_transport_of_family h2 hS'iso hab cfr hcA horth hdiag
  have hS₂S' : S₂ * S'GL * S₂⁻¹ = signGL K (famJ hab) := by
    have e := congrArg (fun g : similarityPairs (oQ (diagGL hw')) => g.val.left) heq
    simp only [transPair_left, linPair_left, linPair_right, map_one, MulAut.one_apply] at e
    rw [sgnPair, linPair_left] at e
    exact e
  have hSA : signMat K (famJ hab) = (S₂ : Matrix (Fin d) (Fin d) K) * avgSign G *
      ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [← coe_signGL, ← hS₂S', Units.val_mul, Units.val_mul]
  have hS₂i : ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (S₂ : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hS₂i' : (S₂ : Matrix (Fin d) (Fin d) K) *
      ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj1 : ∀ N : Matrix (Fin d) (Fin d) K, (S₂ : Matrix (Fin d) (Fin d) K) * (1 - N) *
      ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 - (S₂ : Matrix (Fin d) (Fin d) K) * N *
        ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := fun N => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS₂i']
  have hconj2 : ∀ N : Matrix (Fin d) (Fin d) K, (S₂ : Matrix (Fin d) (Fin d) K) * (1 + N) *
      ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + (S₂ : Matrix (Fin d) (Fin d) K) * N *
        ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := fun N => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS₂i']
  have hcomm_conj : ∀ X N : Matrix (Fin d) (Fin d) K, X * N = N * X →
      ((S₂ : Matrix (Fin d) (Fin d) K) * X * ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S₂ : Matrix (Fin d) (Fin d) K) * N * ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      ((S₂ : Matrix (Fin d) (Fin d) K) * N * ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S₂ : Matrix (Fin d) (Fin d) K) * X *
          ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
    fun X N hXN => by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), hS₂i,
        Matrix.one_mul, ← Matrix.mul_assoc ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), hS₂i,
        Matrix.one_mul, ← Matrix.mul_assoc X, hXN, Matrix.mul_assoc N]
  have hiso₂ : ∀ X : GL (Fin d) K, X ∈ matrixIsometries (oQ (diagGL hw)) →
      MulAut.conj S₂ X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw') := fun X hX =>
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw') _).1
      (map_matrixIsometries_conj S₂ 1 hS₂ ▸ ⟨X, hX, rfl⟩)
  have hM₂ : M.map (MulAut.conj S₂).toMonoidHom ≤ oIsoBlock K hw' (famJ hab)ᶜ := by
    rintro _ ⟨X, hX, rfl⟩
    have hXP := mul_one_sub_avgMat hGc fun g hg => (hMG X hX g hg).2
    have hXc := mul_avgMat_comm (X := (X : Matrix (Fin d) (Fin d) K)) fun g hg => by
      rw [← Units.val_mul, (hMG X hX g hg).1, Units.val_mul]
    have hXS1 : (X : Matrix (Fin d) (Fin d) K) * (1 - avgSign G) = 1 - avgSign G := by
      have e : (1 : Matrix (Fin d) (Fin d) K) - avgSign G = (2 : K) • (1 - avgMat G) := by
        rw [avgSign]
        module
      rw [e, Matrix.mul_smul, hXP]
    have hXSc : (X : Matrix (Fin d) (Fin d) K) * avgSign G = avgSign G * X := by
      rw [avgSign, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hXc,
        Matrix.mul_one, Matrix.one_mul]
    have hYm : ((MulAut.conj S₂ X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (S₂ : Matrix (Fin d) (Fin d) K) * X *
          ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
    have hY1 := conj_mul_conj S₂ hXS1
    rw [hconj1, ← hSA, ← hYm] at hY1
    have hYc := hcomm_conj _ _ hXSc
    rw [← hSA, ← hYm] at hYc
    exact ⟨hiso₂ X (matrixDerived_le_isometries _ (hMH hX)), mul_compInd_of_sign h2 hY1 hYc⟩
  have hLP : L.map (oTransport S₂ 1 hS₂).toMonoidHom ≤ Burgoyne.C.blockP K hw' (famJ hab)ᶜ := by
    rw [← hML, ← X10Orth.map_projH_conj hMH S₂ 1 hS₂]
    refine map_mono fun x hx => mem_subgroupOf.2 ?_
    have hxM := mem_subgroupOf.1 hx
    have hperf : ⁅M.map (MulAut.conj S₂).toMonoidHom, M.map (MulAut.conj S₂).toMonoidHom⁆ =
        M.map (MulAut.conj S₂).toMonoidHom := by
      rw [← Subgroup.map_commutator, hMp]
    rw [← hperf] at hxM
    exact commutator_mono hM₂ hM₂ hxM
  have hPfix : Burgoyne.C.blockP K hw' (famJ hab)ᶜ ≤
      fixedBy (E.map (MulAut.congr (oTransport S₂ 1 hS₂)).toMonoidHom) := by
    rintro _ ⟨Z, hZ, rfl⟩ _ ⟨e, he, rfl⟩
    obtain ⟨D, hD, hDI, rfl⟩ := hrep e he
    have hDG : D ∈ G := (hmemG D).2 ⟨hDI, he⟩
    have hD1 : (D : Matrix (Fin d) (Fin d) K) * (1 + avgSign G) = 1 + avgSign G := by
      have e : (1 : Matrix (Fin d) (Fin d) K) + avgSign G = (2 : K) • avgMat G := by
        rw [avgSign]
        abel
      rw [e, Matrix.mul_smul, mul_avgMat hDG]
    have hDc : (D : Matrix (Fin d) (Fin d) K) * avgSign G = avgSign G * D := by
      rw [avgSign, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_avgMat hDG,
        avgMat_mul hDG, Matrix.mul_one, Matrix.one_mul]
    have hD₂m : ((S₂ * D * S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (S₂ : Matrix (Fin d) (Fin d) K) * D *
          ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [Units.val_mul, Units.val_mul]
    have hY1 := conj_mul_conj S₂ hD1
    rw [hconj2, ← hSA, ← hD₂m] at hY1
    have hYc := hcomm_conj _ _ hDc
    rw [← hSA, ← hD₂m] at hYc
    have hD₂ : S₂ * D * S₂⁻¹ ∈ oIsoBlock K hw' (famJ hab) :=
      ⟨hiso₂ D hD, mul_compInd_of_sign' h2 hY1 hYc⟩
    have hZD := commute_of_mem_oIsoBlock_compl hw'
      (oBlock_le_oIsoBlock hw' _ (mem_subgroupOf.1 hZ)) (by rwa [compl_compl])
    change MulAut.congr (oTransport S₂ 1 hS₂) (oκ _ (linPair D hD)) (projH _ Z) = projH _ Z
    rw [oTransport_kappa, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, transPair_left, transPair_right, linPair_left,
      linPair_right]
    simp only [map_one, MulAut.one_apply]
    rw [← hZD, mul_inv_cancel_right]
  refine ⟨_, hw', (famJ hab)ᶜ, oTransport S₂ 1 hS₂, ?_, ?_, hLP, ?_⟩
  ·
    rw [compl_compl, Finset.nonempty_iff_ne_empty]
    intro hA0
    obtain ⟨e, he, he1⟩ := hE1
    obtain ⟨D, hD, hDI, rfl⟩ := hrep e he
    have hDG : D ∈ G := (hmemG D).2 ⟨hDI, he⟩
    apply he1
    have hS'1 : S'GL = 1 := by
      have e1 : S₂ * S'GL * S₂⁻¹ = 1 := by rw [hS₂S', hA0]; exact Burgoyne.C.signGL_empty
      calc S'GL = S₂⁻¹ * (S₂ * S'GL * S₂⁻¹) * S₂ := by group
        _ = 1 := by rw [e1, mul_one, inv_mul_cancel]
    have hP1 : avgMat G = 1 := by
      have e2 : avgSign G = 1 := congrArg Units.val hS'1
      rw [avgSign, sub_eq_iff_eq_add] at e2
      have e3 : (2 : K) • avgMat G = (2 : K) • 1 := by rw [e2, two_smul]
      exact smul_right_injective _ h2 e3
    have hD1 : D = 1 := by
      have e3 := one_sub_avgMat_mul hDG
      rw [hP1, sub_self, Matrix.zero_mul] at e3
      exact Units.ext (by rw [Units.val_one]; exact (sub_eq_zero.1 e3.symm))
    subst hD1
    exact oκ_linPair_one hD
  ·
    intro h3
    apply hNF₂
    rw [Finset.card_compl, Fintype.card_fin, card_famJ] at h3
    omega
  · have hc1 := isPComponent_map_subgroupOf (oTransport S₂ 1 hS₂) hLE hLc
    rw [← fixedBy_map_congr] at hc1
    exact Burgoyne.C.isPComponent_subgroupOf_of_le hLP hPfix hc1

end CFSG.ComponentClassification.GSThmB.QPUCl
