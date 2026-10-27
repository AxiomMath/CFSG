module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn blockOn_one blockOn_mul det_blockOn
  blockOn_apply_mem blockOn_apply_not_mem compInd compInd_mul_apply mul_compInd_apply
  compInd_apply diagGL coe_diagGL OrthComponentData orthComponentData)
open CFSG.ComponentClassification.Burgoyne.U (blockGL coe_blockGL blockOn_transpose)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

abbrev wRes (w : Fin d → K) (J : Finset (Fin d)) : Fin J.card → K :=
  fun a => w (J.equivFin.symm a)

theorem wRes_ne_zero {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    ∀ a, wRes w J a ≠ 0 := fun _ => hw _

theorem diagonal_reindex (w : Fin d → K) (J : Finset (Fin d)) :
    diagonal w = reindexAlgEquiv K K (Equiv.sumCompl (· ∈ J))
      (fromBlocks (reindexAlgEquiv K K J.equivFin.symm (diagonal (wRes w J))) 0 0
        (diagonal fun a : {a // a ∉ J} => w a)) := by
  ext i j
  rw [coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₁₁, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp [wRes]
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne]
      intro h
      apply hij
      have := congrArg (fun a => (J.equivFin.symm a : Fin d)) h
      simpa using this
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₁₂, Matrix.zero_apply, diagonal_apply_ne]
    exact fun h => hj (h ▸ hi)
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₂₁, Matrix.zero_apply, diagonal_apply_ne]
    exact fun h => hi (h ▸ hj)
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₂₂]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne]
      intro h
      exact hij (congrArg Subtype.val h)

theorem blockOn_transpose_mul_diagonal_mul (w : Fin d → K) (J : Finset (Fin d))
    (X Y : Matrix (Fin J.card) (Fin J.card) K) :
    (blockOn K J X)ᵀ * diagonal w * blockOn K J Y = reindexAlgEquiv K K (Equiv.sumCompl (· ∈ J))
      (fromBlocks (reindexAlgEquiv K K J.equivFin.symm (Xᵀ * diagonal (wRes w J) * Y)) 0 0
        (diagonal fun a : {a // a ∉ J} => w a)) := by
  rw [blockOn_transpose, diagonal_reindex w J, blockOn, blockOn, ← map_mul, ← map_mul,
    fromBlocks_multiply, fromBlocks_multiply, map_mul, map_mul]
  simp

theorem blockOn_isometry_iff (w : Fin d → K) (J : Finset (Fin d))
    (X : Matrix (Fin J.card) (Fin J.card) K) :
    (blockOn K J X)ᵀ * diagonal w * blockOn K J X = diagonal w ↔
      Xᵀ * diagonal (wRes w J) * X = diagonal (wRes w J) := by
  rw [blockOn_transpose_mul_diagonal_mul, diagonal_reindex w J, EmbeddingLike.apply_eq_iff_eq,
    fromBlocks_inj]
  simp only [and_true, EmbeddingLike.apply_eq_iff_eq]

variable (K) in
@[expose] def oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    Subgroup (GL (Fin d) K) where
  carrier := {g | g ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) ∧
    compInd K J * (g : Matrix (Fin d) (Fin d) K) = compInd K J ∧
    (g : Matrix (Fin d) (Fin d) K) * compInd K J = compInd K J}
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  mul_mem' := by
    rintro g g' ⟨hg, hg1, hg2⟩ ⟨hg', hg1', hg2'⟩
    refine ⟨mul_mem hg hg', ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mul_assoc, hg1, hg1']
    · rw [Units.val_mul, Matrix.mul_assoc, hg2', hg2]
  inv_mem' := by
    rintro g ⟨hg, hg1, hg2⟩
    have h1 : (g : Matrix (Fin d) (Fin d) K) * ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) =
        1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨inv_mem hg, ?_, ?_⟩
    · calc compInd K J * ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          (compInd K J * (g : Matrix (Fin d) (Fin d) K)) *
            ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hg1]
        _ = compInd K J := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    · calc ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * compInd K J =
          ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((g : Matrix (Fin d) (Fin d) K) * compInd K J) := by rw [hg2]
        _ = compInd K J := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem support_iff {J : Finset (Fin d)} {M : Matrix (Fin d) (Fin d) K} :
    (compInd K J * M = compInd K J ∧ M * compInd K J = compInd K J) ↔
      ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [compInd_mul_apply, compInd_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_compInd_apply, compInd_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  · intro hg
    refine ⟨?_, ?_⟩
    · ext i j
      rw [compInd_mul_apply, compInd_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact hg i j (Or.inl hi)
    · ext i j
      rw [mul_compInd_apply, compInd_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [hg i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]

theorem mem_oIsoBlock_iff {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {g : GL (Fin d) K} :
    g ∈ oIsoBlock K hw J ↔ g ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) ∧
      ∀ i j, (i ∉ J ∨ j ∉ J) → (g : Matrix (Fin d) (Fin d) K) i j = if i = j then 1 else 0 := by
  change (_ ∧ _ ∧ _) ↔ _
  rw [← support_iff]

@[expose] def oBlockHom {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    CatalogueBGraphForm.isometryGroup J.card K (diagGL (wRes_ne_zero hw J)) →* GL (Fin d) K :=
  (blockGL K J).comp (Subgroup.subtype _)

theorem coe_oBlockHom {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
    (X : CatalogueBGraphForm.isometryGroup J.card K (diagGL (wRes_ne_zero hw J))) :
    ((oBlockHom hw J X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blockOn K J ((X : GL (Fin J.card) K) : Matrix (Fin J.card) (Fin J.card) K) := rfl

theorem oBlockHom_injective {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    Function.Injective (oBlockHom hw J) := by
  intro X Y hXY
  apply Subtype.ext
  apply Units.ext
  ext a b
  have h1 := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)
    (J.equivFin.symm a) (J.equivFin.symm b)) hXY
  simp only [coe_oBlockHom] at h1
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at h1
  simpa using h1

theorem blockOn_injective (J : Finset (Fin d)) :
    Function.Injective (blockOn K J) := by
  intro M N hMN
  ext a b
  have := congrFun (congrFun hMN (J.equivFin.symm a)) (J.equivFin.symm b)
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at this
  simpa using this

theorem range_oBlockHom {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    (oBlockHom hw J).range = oIsoBlock K hw J := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_oIsoBlock_iff]
    refine ⟨?_, fun i j hij => by rw [coe_oBlockHom, blockOn_apply_not_mem J _ hij]⟩
    rw [CatalogueBGraphForm.mem_isometryGroup, coe_oBlockHom, coe_diagGL]
    have hX := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 X.2
    rw [coe_diagGL] at hX
    exact (blockOn_isometry_iff w J _).2 hX
  · intro g hg
    rw [mem_oIsoBlock_iff] at hg
    obtain ⟨hgI, hg⟩ := hg
    set X : Matrix (Fin J.card) (Fin J.card) K := Matrix.of fun a b =>
      (g : Matrix (Fin d) (Fin d) K) (J.equivFin.symm a) (J.equivFin.symm b) with hX
    have hXg : blockOn K J X = (g : Matrix (Fin d) (Fin d) K) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J X hi hj, hX, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J X (Or.inr hj), hg i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
    have hgi := inv_mem (show g ∈ oIsoBlock K hw J from (mem_oIsoBlock_iff hw).2 ⟨hgI, hg⟩)
    rw [mem_oIsoBlock_iff] at hgi
    set Y : Matrix (Fin J.card) (Fin J.card) K := Matrix.of fun a b =>
      ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (J.equivFin.symm a) (J.equivFin.symm b)
      with hY
    have hYg : blockOn K J Y = ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J Y hi hj, hY, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J Y (Or.inr hj), hgi.2 i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J Y (Or.inl hi), hgi.2 i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J Y (Or.inl hi), hgi.2 i j (Or.inl hi)]
    have hXY : X * Y = 1 := blockOn_injective J (by
      rw [blockOn_mul, hXg, hYg, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockOn_one])
    have hYX : Y * X = 1 := blockOn_injective J (by
      rw [blockOn_mul, hXg, hYg, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockOn_one])
    set XG : GL (Fin J.card) K := ⟨X, Y, hXY, hYX⟩
    have hmem : XG ∈ CatalogueBGraphForm.isometryGroup J.card K (diagGL (wRes_ne_zero hw J)) := by
      rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL]
      rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL] at hgI
      refine (blockOn_isometry_iff w J X).1 ?_
      rw [hXg]
      exact hgI
    exact ⟨⟨XG, hmem⟩, Units.ext hXg⟩

@[expose] def oIsoBlockEquiv {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    CatalogueBGraphForm.isometryGroup J.card K (diagGL (wRes_ne_zero hw J)) ≃* oIsoBlock K hw J :=
  (MonoidHom.ofInjective (oBlockHom_injective hw J)).trans
    (MulEquiv.subgroupCongr (range_oBlockHom hw J))

theorem oIsoBlock_le {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    oIsoBlock K hw J ≤ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := fun _ hg => hg.1

theorem conj_mem_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {h : GL (Fin d) K} (hh : h ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hc : compInd K J * (h : Matrix (Fin d) (Fin d) K) = (h : Matrix (Fin d) (Fin d) K) *
      compInd K J) {g : GL (Fin d) K} (hg : g ∈ oIsoBlock K hw J) :
    h * g * h⁻¹ ∈ oIsoBlock K hw J := by
  obtain ⟨hgI, hg1, hg2⟩ := hg
  set P := compInd K J with hP
  set H := (h : Matrix (Fin d) (Fin d) K) with hH
  set Hi := ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hHi
  set G := (g : Matrix (Fin d) (Fin d) K) with hG
  have e1 : H * Hi = 1 := by rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : Hi * H = 1 := by rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hhi : Hi * P = P * Hi := by
    calc Hi * P = Hi * (P * H) * Hi := by
          rw [Matrix.mul_assoc Hi, Matrix.mul_assoc P, e1, Matrix.mul_one]
      _ = Hi * (H * P) * Hi := by rw [hc]
      _ = P * Hi := by rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
  refine ⟨mul_mem (mul_mem hh hgI) (inv_mem hh), ?_, ?_⟩
  · change P * (H * G * Hi) = P
    calc P * (H * G * Hi) = H * (P * G) * Hi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc H P G]
      _ = P := by rw [hg1, Matrix.mul_assoc, ← hhi, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  · change (H * G * Hi) * P = P
    calc (H * G * Hi) * P = H * (G * P) * Hi := by
          rw [Matrix.mul_assoc, hhi, ← Matrix.mul_assoc, Matrix.mul_assoc H G P]
      _ = P := by rw [hg2, ← hc, Matrix.mul_assoc, e1, Matrix.mul_one]

variable (K) in
abbrev oBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) : Subgroup (GL (Fin d) K) :=
  ⁅oIsoBlock K hw J, oIsoBlock K hw J⁆

theorem oBlock_le {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    oBlock K hw J ≤ ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
  commutator_mono (oIsoBlock_le hw J) (oIsoBlock_le hw J)

theorem oBlock_le_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    oBlock K hw J ≤ oIsoBlock K hw J := Subgroup.commutator_le_self _

theorem oBlock_eq_map {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d)) :
    oBlock K hw J = (⁅CatalogueBGraphForm.isometryGroup J.card K (diagGL (wRes_ne_zero hw J)),
      CatalogueBGraphForm.isometryGroup J.card K (diagGL (wRes_ne_zero hw J))⁆).map
        (blockGL K J) := by
  have h1 : oIsoBlock K hw J = (CatalogueBGraphForm.isometryGroup J.card K
      (diagGL (wRes_ne_zero hw J))).map (blockGL K J) := by
    rw [← range_oBlockHom hw J, oBlockHom, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [oBlock, h1, Subgroup.map_commutator]

theorem conj_mem_oBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {h : GL (Fin d) K} (hh : h ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hc : compInd K J * (h : Matrix (Fin d) (Fin d) K) = (h : Matrix (Fin d) (Fin d) K) *
      compInd K J) {g : GL (Fin d) K} (hg : g ∈ oBlock K hw J) :
    h * g * h⁻¹ ∈ oBlock K hw J := by
  have hle : oBlock K hw J ≤ (oBlock K hw J).comap (MulAut.conj h).toMonoidHom := by
    rw [oBlock, Subgroup.commutator_le]
    intro a ha b hb
    change h * ⁅a, b⁆ * h⁻¹ ∈ oBlock K hw J
    have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by group
    rw [e]
    exact commutator_mem_commutator (conj_mem_oIsoBlock hw hh hc ha)
      (conj_mem_oIsoBlock hw hh hc hb)
  exact hle hg

theorem oBlock_componentData [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hJ : 3 ≤ J.card)
    (hexc : ¬ (Nat.card K = 3 ∧ J.card ≤ 4)) :
    ⁅oBlock K hw J, oBlock K hw J⁆ = oBlock K hw J ∧
      ∃ (m : ℕ) (L : Fin m → Subgroup (GL (Fin d) K)), (⨆ i, L i) = oBlock K hw J ∧
        ∀ i, IsQuasisimple (L i) ∧ L i ≤ oBlock K hw J ∧
          ∀ x ∈ oBlock K hw J, ∀ l ∈ L i, x * l * x⁻¹ ∈ L i := by
  obtain ⟨hperf, m, L, hsup, hL⟩ := orthComponentData hK hJ (diagGL (wRes_ne_zero hw J))
    (by rw [coe_diagGL]; exact diagonal_transpose _) hexc
  have hinj : Function.Injective (blockGL K J) := by
    intro X Y hXY
    apply Units.ext
    exact blockOn_injective J (congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K))
      hXY)
  rw [oBlock_eq_map]
  refine ⟨by rw [← Subgroup.map_commutator, hperf], m, fun i => (L i).map (blockGL K J), ?_,
    fun i => ⟨?_, map_mono (hL i).2.1, ?_⟩⟩
  · rw [← Subgroup.map_iSup, hsup]
  · exact LocalCores.isQuasisimple_of_mulEquiv ((L i).equivMapOfInjective _ hinj) (hL i).1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
    exact ⟨x * l * x⁻¹, (hL i).2.2 x hx l hl, by simp only [map_mul, map_inv]⟩

end CFSG.ComponentClassification.Burgoyne.O
