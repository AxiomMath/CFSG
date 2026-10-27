module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusAut

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement
open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section Borel

variable {K : Type} [Field K] [Finite K] (n : ℕ)

omit [Finite K] in
theorem mem_plusDerivedBorel_iff_flagStab (hn : 3 ≤ n) (g : StatedOmega (StatedQuadPlus n K)) :
    g ∈ plusDerivedBorel n K ↔ toLinEquiv (Fin n ⊕ Fin n) K g.val ∈ flagStab n K := by
  have hmap := plusDerivedBorel_map n K hn
  rw [← Subgroup.mem_map_iff_mem (f := (plusDerivedEquiv n K hn).toMonoidHom)
    (plusDerivedEquiv n K hn).injective, hmap, Subgroup.mem_subgroupOf]
  rfl

theorem toLinEquiv_mem_posBorel (hn : 3 ≤ n) {g : StatedOmega (StatedQuadPlus n K)}
    (hg : g ∈ plusDerivedBorel n K) : toLinEquiv (Fin n ⊕ Fin n) K g.val ∈ posBorel n K :=
  flagStab_le_posBorel (by omega) (fun _ ha => map_flag_top_ne_Xstar hn ha)
    ((mem_plusDerivedBorel_iff_flagStab n hn g).1 hg)

omit [Finite K] in
theorem mem_plusDerivedBorel_of_posBorel (hn : 3 ≤ n) {g : StatedOmega (StatedQuadPlus n K)}
    (hg : toLinEquiv (Fin n ⊕ Fin n) K g.val ∈ posBorel n K) : g ∈ plusDerivedBorel n K :=
  (mem_plusDerivedBorel_iff_flagStab n hn g).2
    (mem_flagStab.2 ⟨(plusDerivedEquiv n K hn g).property, fun i _ _ => (mem_posBorel.1 hg).2 i⟩)

theorem mem_plusDerivedBorel_iff (hn : 3 ≤ n) (g : StatedOmega (StatedQuadPlus n K)) :
    g ∈ plusDerivedBorel n K ↔ ∃ (A : GL (Fin n) K) (C : Matrix (Fin n) (Fin n) K),
      (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      ((g.val : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        fromBlocks (A : Matrix (Fin n) (Fin n) K) ((A : Matrix (Fin n) (Fin n) K) * C) 0
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  constructor
  · intro hg
    obtain ⟨A, C, hA, hC, hd, hgM⟩ := mem_posBorel_iff.1 (toLinEquiv_mem_posBorel n hn hg)
    refine ⟨A, C, hA, hC, hd, ?_⟩
    rw [← hgM]
    exact (toMatrix_toLinEquiv n K g.val).symm
  · rintro ⟨A, C, hA, hC, hd, hgM⟩
    refine mem_plusDerivedBorel_of_posBorel n hn (mem_posBorel_iff.2 ⟨A, C, hA, hC, hd, ?_⟩)
    rw [toMatrix_toLinEquiv n K g.val]
    exact hgM

@[expose] noncomputable def plusDiag (hn : 3 ≤ n) : plusDerivedBorel n K →* (Fin n → Kˣ) :=
  (posBorelDiag n K).comp
    (MonoidHom.codRestrict
      (((orthElementaryGroup (quadPlus n K)).subtype.comp
        (plusDerivedEquiv n K hn).toMonoidHom).comp (plusDerivedBorel n K).subtype)
      (posBorel n K) (fun g => toLinEquiv_mem_posBorel n hn g.2))

theorem coe_plusDiag (hn : 3 ≤ n) (g : plusDerivedBorel n K) (i : Fin n) :
    ((plusDiag n hn g i : Kˣ) : K) =
      ((g.1.val : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (.inl i) (.inl i) := by
  rw [plusDiag, MonoidHom.comp_apply, coe_posBorelDiag]
  have := toMatrix_toLinEquiv n K g.1.val
  exact congrFun (congrFun this (.inl i)) (.inl i)

theorem mem_plusDerivedUnipotent_of_diag (hn : 3 ≤ n) {g : plusDerivedBorel n K}
    (h : plusDiag n hn g = 1) : g.1 ∈ plusDerivedUnipotent n K := by
  change toLinEquiv (Fin n ⊕ Fin n) K g.1.val ∈ posUnip n K
  refine mem_posUnip.2 ⟨toLinEquiv_mem_posBorel n hn g.2, fun i => ?_⟩
  have h1 := congrArg Units.val (congrFun h i)
  rw [coe_plusDiag n hn g i, Pi.one_apply, Units.val_one] at h1
  rw [toMatrix_toLinEquiv n K g.1.val]
  exact h1

omit [Finite K] in
theorem mem_plusDerivedBorel_of_unipotent (hn : 3 ≤ n) {g : StatedOmega (StatedQuadPlus n K)}
    (hg : g ∈ plusDerivedUnipotent n K) : g ∈ plusDerivedBorel n K :=
  mem_plusDerivedBorel_of_posBorel n hn
    (mem_posUnip.1 (show toLinEquiv (Fin n ⊕ Fin n) K g.val ∈ posUnip n K from hg)).1

theorem plusDiag_eq_one_of_unipotent (hn : 3 ≤ n) {g : plusDerivedBorel n K}
    (hg : g.1 ∈ plusDerivedUnipotent n K) : plusDiag n hn g = 1 := by
  funext i
  refine Units.ext ?_
  rw [coe_plusDiag n hn g i, Pi.one_apply, Units.val_one]
  have hmem : toLinEquiv (Fin n ⊕ Fin n) K g.1.val ∈ posUnip n K := hg
  have := (mem_posUnip.1 hmem).2 i
  rw [toMatrix_toLinEquiv n K g.1.val] at this
  exact this

end Borel

section Field

variable {K : Type} [Field K] [Finite K] (n : ℕ)

omit [Finite K] in
theorem glFieldAut_val {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K) (B : GL ι K) :
    ((glFieldAut ι K σ B : GL ι K) : Matrix ι ι K) = (B : Matrix ι ι K).map σ := rfl

theorem plusDerivedBorel_entrywise (hn : 3 ≤ n) (σ : K ≃+* K)
    {g g' : StatedOmega (StatedQuadPlus n K)}
    (h : (g'.val : GL (Fin n ⊕ Fin n) K) = glFieldAut (Fin n ⊕ Fin n) K σ g.val)
    (hg : g ∈ plusDerivedBorel n K) : g' ∈ plusDerivedBorel n K := by
  obtain ⟨A, C, hA, hC, hd, hgM⟩ := (mem_plusDerivedBorel_iff n hn g).1 hg
  rw [mem_plusDerivedBorel_iff n hn g']
  refine ⟨glFieldAut (Fin n) K σ A, C.map σ, ?_, ?_, ?_, ?_⟩
  · intro i j hji
    rw [glFieldAut_val]
    change σ ((A : Matrix (Fin n) (Fin n) K) i j) = 0
    rw [hA hji, map_zero]
  · rw [← Matrix.transpose_map, hC, Matrix.map_neg _ (map_neg σ)]
  · intro i
    simp [hd i]
  · rw [h, glFieldAut_val, hgM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero σ),
      glFieldAut_val, Matrix.map_mul, ← map_inv, glFieldAut_val, Matrix.transpose_map]

theorem plusDiag_entrywise (hn : 3 ≤ n) (σ : K ≃+* K) {g g' : plusDerivedBorel n K}
    (h : (g'.1.val : GL (Fin n ⊕ Fin n) K) = glFieldAut (Fin n ⊕ Fin n) K σ g.1.val) (i : Fin n) :
    ((plusDiag n hn g' i : Kˣ) : K) = σ ((plusDiag n hn g i : Kˣ) : K) := by
  rw [coe_plusDiag n hn g' i, coe_plusDiag n hn g i, h]
  rfl

theorem entrywise_mul_pow_inv_mem_unipotent (hn : 3 ≤ n) (σ : K ≃+* K) {k : ℕ}
    (hk : ∀ x : K, σ x = x ^ k) {g g' : plusDerivedBorel n K}
    (h : (g'.1.val : GL (Fin n ⊕ Fin n) K) = glFieldAut (Fin n ⊕ Fin n) K σ g.1.val) :
    (g' * (g ^ k)⁻¹ : plusDerivedBorel n K).1 ∈ plusDerivedUnipotent n K := by
  have hd : plusDiag n hn (g' * (g ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow]
    funext i
    refine Units.ext ?_
    have hx : ((plusDiag n hn g i : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h1 := plusDiag_entrywise n hn σ h i
    rw [hk] at h1
    change ((plusDiag n hn g' i : Kˣ) : K) * ((((plusDiag n hn g i) ^ k)⁻¹ : Kˣ) : K) = 1
    rw [h1, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    exact mul_inv_cancel₀ (pow_ne_zero k hx)
  exact mem_plusDerivedUnipotent_of_diag n hn hd

end Field

section StatedAut

variable {K : Type} [Field K] (n : ℕ)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.RankThree.PartOne.KCOrthogonalSubfield

@[expose] noncomputable def plusReindex :
    StatedOmega (StatedQuadPlus n K) ≃* matrixDerived (coordinateQuadPlus n K) :=
  statedDerivedReindexEquiv (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)

@[expose] noncomputable def plusProjReindex :
    StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      matrixProjectiveDerived (coordinateQuadPlus n K) :=
  statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)

theorem plusProjReindex_mk (g : StatedOmega (StatedQuadPlus n K)) :
    plusProjReindex n (QuotientGroup.mk' _ g) =
      matrixProjectiveProjection (coordinateQuadPlus n K) (plusReindex n g) :=
  statedProjectiveReindexEquiv_mk (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K) g

theorem plusProjReindex_symm_mk (G : matrixDerived (coordinateQuadPlus n K)) :
    (plusProjReindex n).symm (matrixProjectiveProjection (coordinateQuadPlus n K) G) =
      QuotientGroup.mk' _ ((plusReindex n).symm G) :=
  statedProjectiveReindexEquiv_symm_mk (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K) G

theorem plusReindex_entry (g : StatedOmega (StatedQuadPlus n K)) (i j : Fin (2 * n)) :
    ((plusReindex n g).val : GL (Fin (2 * n)) K) i j =
      (g.val : GL (Fin n ⊕ Fin n) K) ((plusIndexEquiv n).symm i) ((plusIndexEquiv n).symm j) :=
  statedDerivedReindexEquiv_entry (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K) g i j

theorem plusReindex_symm_entry (G : matrixDerived (coordinateQuadPlus n K)) (i j : Fin n ⊕ Fin n) :
    (((plusReindex n).symm G).val : GL (Fin n ⊕ Fin n) K) i j =
      (G.val : GL (Fin (2 * n)) K) (plusIndexEquiv n i) (plusIndexEquiv n j) :=
  statedDerivedReindexEquiv_symm_entry (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K) G i j

@[expose] noncomputable def plusStatedAut (σ : K ≃+* K) :
    MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  MulAut.congr (plusProjReindex n).symm
    (matrixProjectiveConjugationHom (coordinateQuadPlus n K) (plusFieldHom n σ))

theorem plusStatedAut_apply (σ : K ≃+* K) (x : StatedProj (StatedOmega (StatedQuadPlus n K))) :
    plusStatedAut n σ x = (plusProjReindex n).symm
      (matrixProjectiveConjugationHom (coordinateQuadPlus n K) (plusFieldHom n σ)
        (plusProjReindex n x)) := rfl

theorem plusStatedAut_mk (σ : K ≃+* K) (g : StatedOmega (StatedQuadPlus n K)) :
    ∃ g' : StatedOmega (StatedQuadPlus n K),
      (g'.val : GL (Fin n ⊕ Fin n) K) = glFieldAut (Fin n ⊕ Fin n) K σ g.val ∧
        plusStatedAut n σ (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ g' := by
  refine ⟨(plusReindex n).symm
    (matrixDerivedConjugation (coordinateQuadPlus n K) (plusFieldHom n σ) (plusReindex n g)),
    ?_, ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have h3 : ((matrixDerivedConjugation (coordinateQuadPlus n K) (plusFieldHom n σ)
        (plusReindex n g)).val : GL (Fin (2 * n)) K) =
        glFieldAut (Fin (2 * n)) K σ (plusReindex n g).val :=
      matrixDerivedConjugation_fieldPair_val (coordinateQuadPlus n K) σ
        (coordinateQuadPlus_fieldMap n σ) (plusReindex n g)
    rw [plusReindex_symm_entry, h3, glFieldAut_val]
    change σ (((plusReindex n g).val : GL (Fin (2 * n)) K) _ _) = _
    rw [plusReindex_entry, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · rw [plusStatedAut_apply, plusProjReindex_mk]
    change (plusProjReindex n).symm
      (matrixProjectiveConjugation _ _ (matrixProjectiveProjection _ _)) = _
    rw [matrixProjectiveConjugation_mk, plusProjReindex_symm_mk]

@[expose] noncomputable def plusStatedAutHom :
    (K ≃+* K) →* MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  (MulAut.congr (plusProjReindex n).symm).toMonoidHom.comp
    ((matrixProjectiveConjugationHom (coordinateQuadPlus n K)).comp (plusFieldHom n))

end StatedAut

section Preserve

variable {K : Type} [Field K] [Finite K] (n : ℕ)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem plusStatedAut_mem_unipotent (hn : 3 ≤ n) (σ : K ≃+* K)
    {w : StatedProj (StatedOmega (StatedQuadPlus n K))} (hw : w ∈ plusProjectiveUnipotent n K) :
    plusStatedAut n σ w ∈ plusProjectiveUnipotent n K := by
  obtain ⟨g, hg, rfl⟩ := hw
  obtain ⟨g', hval, hg'⟩ := plusStatedAut_mk n σ g
  rw [hg']
  refine ⟨g', ?_, rfl⟩
  have hB : g ∈ plusDerivedBorel n K := mem_plusDerivedBorel_of_unipotent n hn hg
  have hB' : g' ∈ plusDerivedBorel n K := plusDerivedBorel_entrywise n hn σ hval hB
  have h1 : plusDiag n hn ⟨g, hB⟩ = 1 := plusDiag_eq_one_of_unipotent n hn hg
  have h2 : plusDiag n hn ⟨g', hB'⟩ = 1 := by
    funext i
    refine Units.ext ?_
    rw [plusDiag_entrywise n hn σ (g := ⟨g, hB⟩) (g' := ⟨g', hB'⟩) hval i, h1]
    simp
  exact mem_plusDerivedUnipotent_of_diag n hn h2

theorem plusStatedAut_mem_unipotent_iff (hn : 3 ≤ n) (σ : K ≃+* K)
    (w : StatedProj (StatedOmega (StatedQuadPlus n K))) :
    w ∈ plusProjectiveUnipotent n K ↔ plusStatedAut n σ w ∈ plusProjectiveUnipotent n K := by
  refine ⟨plusStatedAut_mem_unipotent n hn σ, fun h => ?_⟩
  have := plusStatedAut_mem_unipotent n hn σ⁻¹ h
  have e : plusStatedAut n σ⁻¹ (plusStatedAut n σ w) = w := by
    change (plusStatedAutHom n σ⁻¹ * plusStatedAutHom n σ) w = w
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rwa [e] at this

theorem plusStatedAut_mul_pow_inv_mem (hn : 3 ≤ n) (σ : K ≃+* K) {k : ℕ}
    (hk : ∀ x : K, σ x = x ^ k) {b : StatedProj (StatedOmega (StatedQuadPlus n K))}
    (hb : b ∈ plusProjectiveBorel n K) :
    plusStatedAut n σ b * (b ^ k)⁻¹ ∈ plusProjectiveUnipotent n K := by
  rw [← plusDerivedBorel_project n K] at hb
  obtain ⟨g, hg, rfl⟩ := hb
  obtain ⟨g', hval, hg'⟩ := plusStatedAut_mk n σ g
  have hB' : g' ∈ plusDerivedBorel n K := plusDerivedBorel_entrywise n hn σ hval hg
  have key := entrywise_mul_pow_inv_mem_unipotent n hn σ hk (g := ⟨g, hg⟩) (g' := ⟨g', hB'⟩) hval
  refine ⟨_, key, ?_⟩
  rw [hg']
  simp [map_mul, map_inv, map_pow]

theorem plus_commutator_mem_unipotent (hn : 3 ≤ n)
    {b c : StatedProj (StatedOmega (StatedQuadPlus n K))} (hb : b ∈ plusProjectiveBorel n K)
    (hc : c ∈ plusProjectiveBorel n K) :
    ⁅b, c⁆ ∈ plusProjectiveUnipotent n K := by
  rw [← plusDerivedBorel_project n K] at hb hc
  obtain ⟨g, hg, rfl⟩ := hb
  obtain ⟨h, hh, rfl⟩ := hc
  have hd : plusDiag n hn ⁅(⟨g, hg⟩ : plusDerivedBorel n K), ⟨h, hh⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  refine ⟨_, mem_plusDerivedUnipotent_of_diag n hn hd, ?_⟩
  simp [commutatorElement_def]

end Preserve

end CFSG.AGLEmbedding.ParabAutIrr
