module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometrySemilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusExt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

abbrev GLV (r : ℕ) (K : Type) [Field K] : Type :=
  (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
@[expose] noncomputable def fieldConj (σ : K ≃+* K) : GLV r K →* GLV r K :=
  (matrixEquiv r K).toMonoidHom.comp
    ((Units.map (RingHom.mapMatrix (σ : K →+* K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K →+* Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K
      ).toMonoidHom).comp (matrixEquiv r K).symm.toMonoidHom)

theorem autMat_matrixEquiv (M : GL (Fin r ⊕ Fin r) K) :
    autMat (matrixEquiv r K M) = (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  toMatrix'_matrixEquiv M

theorem autMat_fieldConj (σ : K ≃+* K) (g : GLV r K) :
    autMat (fieldConj r K σ g) = (autMat g).map σ := by
  have h := autMat_matrixEquiv ((matrixEquiv r K).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [fieldConj, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.coe_coe, autMat_matrixEquiv, h]
  rfl

theorem fieldConj_apply (σ : K ≃+* K) (g : GLV r K) (v : Fin r ⊕ Fin r → K) :
    fieldConj r K σ g v = sCoord σ (g (sCoord σ.symm v)) := by
  rw [apply_eq_autMat_mulVec, autMat_fieldConj, apply_eq_autMat_mulVec]
  funext i
  simp only [Matrix.mulVec, dotProduct, sCoord_apply, Matrix.map_apply, map_sum, map_mul,
    RingEquiv.apply_symm_apply]

theorem fieldConj_one (g : GLV r K) : fieldConj r K (1 : K ≃+* K) g = g := by
  apply autMat_injective
  rw [autMat_fieldConj]
  ext i j
  rfl

theorem fieldConj_mem_orthogonalGroup (σ : K ≃+* K) {g : GLV r K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) :
    fieldConj r K σ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
  intro v
  rw [fieldConj_apply, quadPlus_sCoord, hg, quadPlus_sCoord, RingEquiv.apply_symm_apply]

theorem fieldConj_mem_orthElementaryGroup [CharP K 2] (hr : 3 ≤ r) (σ : K ≃+* K) {g : GLV r K}
    (hg : g ∈ orthElementaryGroup (quadPlus r K)) :
    fieldConj r K σ g ∈ orthElementaryGroup (quadPlus r K) := by
  rw [← commutator_orthogonalGroup_quadPlus hr] at hg ⊢
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)).map (fieldConj r K σ) ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact fieldConj_mem_orthogonalGroup σ hx
  have h1 : fieldConj r K σ g ∈ (⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)⁆).map (fieldConj r K σ) := ⟨g, hg, rfl⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hle hle h1

theorem plusCut_fieldConj (σ : K ≃+* K) {g : GLV r K} {c : ℕ} (hg : PlusCut g c) :
    PlusCut (fieldConj r K σ g) c := by
  intro u w hw hu
  rw [autMat_fieldConj, Matrix.map_apply, hg u w hw hu, map_zero]

theorem smul_flag_fieldConj (σ : K ≃+* K) {g : GLV r K} {d : ℕ} (hd : d ≤ r)
    (hg : g • flag r K d = flag r K d) : fieldConj r K σ g • flag r K d = flag r K d := by
  have hg' : g⁻¹ • flag r K d = flag r K d := by
    rw [inv_smul_eq_iff]
    exact hg.symm
  refine smul_flag_of_plusCut hd (plusCut_fieldConj σ (plusCut_of_smul_flag hd hg)) ?_
  rw [← map_inv]
  exact plusCut_fieldConj σ (plusCut_of_smul_flag hd hg')

@[expose] def IsSemilinear (α : MulAut ↥(orthElementaryGroup (quadPlus r K))) : Prop :=
  ∃ (h : GLV r K) (σ : K ≃+* K), h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ∧
    ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
      ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) = h * fieldConj r K σ x * h⁻¹

variable (K) in
@[expose] noncomputable def plusFlagStabO (r : ℕ) (D : Finset ℕ) : Subgroup (GLV r K) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ⊓
    ⨅ d ∈ D, MulAction.stabilizer (GLV r K) (flag r K d)

theorem mem_plusFlagStabO {D : Finset ℕ} {g : GLV r K} :
    g ∈ plusFlagStabO K r D ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ∧
      ∀ d ∈ D, g • flag r K d = flag r K d := by
  simp only [plusFlagStabO, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem plusFlagStab_le_plusFlagStabO (D : Finset ℕ) :
    plusFlagStab K r D ≤ plusFlagStabO K r D := fun _ hg =>
  mem_plusFlagStabO.2 ⟨orthElementaryGroup_le _ (mem_plusFlagStab.1 hg).1,
    (mem_plusFlagStab.1 hg).2⟩

theorem mem_plusFlagStab_iff {D : Finset ℕ} {g : GLV r K} :
    g ∈ plusFlagStab K r D ↔ g ∈ plusFlagStabO K r D ∧
      g ∈ orthElementaryGroup (quadPlus r K) := by
  rw [mem_plusFlagStab]
  exact ⟨fun ⟨hE, hF⟩ => ⟨mem_plusFlagStabO.2 ⟨orthElementaryGroup_le _ hE, hF⟩, hE⟩,
    fun ⟨hO, hE⟩ => ⟨hE, (mem_plusFlagStabO.1 hO).2⟩⟩

theorem plusCut_of_mem_plusFlagStabO {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {g : GLV r K}
    (hg : g ∈ plusFlagStabO K r D) {c : ℕ} (hc : c = 0 ∨ c ∈ D) :
    PlusCut g c ∧ PlusCut g (2 * r - c) := by
  obtain ⟨hgO, hgF⟩ := mem_plusFlagStabO.1 hg
  have hcr : c ≤ r := hc.elim (fun h => by omega) (hD c)
  have hs : g • flag r K c = flag r K c := by
    rcases hc with rfl | hc
    · change Submodule.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K 0) = _
      rw [flag_zero, Submodule.map_bot]
    · exact hgF c hc
  exact ⟨plusCut_of_smul_flag hcr hs, plusCut_of_smul_flag_orthogonal hgO hcr hs⟩

@[expose] noncomputable def plusEBlockHomO {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b : ℕ}
    (hb : b ∈ D) : ↥(plusFlagStabO K r D) →* GL (Fin (b - predCut D b)) K :=
  plusBlockHom _ (plusEIdx_injective (hD b hb)) (mem_range_plusEIdx (hD b hb))
    (fun _ hg => (plusCut_of_mem_plusFlagStabO hD hg (predCut_eq_zero_or_mem D b)).1)
    (fun _ hg => (plusCut_of_mem_plusFlagStabO hD hg (Or.inr hb)).1)

@[expose] noncomputable def plusResBlockHomO {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) :
    ↥(plusFlagStabO K r D) →* GL (Fin m ⊕ Fin m) K :=
  plusBlockHom _ (plusResIdx_injective htm) (mem_range_plusResIdx htm)
    (fun _ hg => (plusCut_of_mem_plusFlagStabO hD hg ht).1)
    (fun _ hg => (plusCut_of_mem_plusFlagStabO hD hg ht).2)

theorem coe_plusEBlockHomO {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b : ℕ} (hb : b ∈ D)
    (g : ↥(plusFlagStabO K r D)) :
    ((plusEBlockHomO hD hb g : GL (Fin (b - predCut D b)) K) :
      Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) =
      (autMat (g : GLV r K)).submatrix (plusEIdx (hD b hb)) (plusEIdx (hD b hb)) :=
  rfl

theorem coe_plusResBlockHomO {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) (g : ↥(plusFlagStabO K r D)) :
    ((plusResBlockHomO hD ht htm g : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      (autMat (g : GLV r K)).submatrix (plusResIdx htm) (plusResIdx htm) :=
  rfl

variable [CharP K 2]

theorem fieldConj_mem_plusFlagStabO (σ : K ≃+* K) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r)
    {g : GLV r K} (hg : g ∈ plusFlagStabO K r D) : fieldConj r K σ g ∈ plusFlagStabO K r D := by
  obtain ⟨hgO, hgF⟩ := mem_plusFlagStabO.1 hg
  exact mem_plusFlagStabO.2 ⟨fieldConj_mem_orthogonalGroup σ hgO,
    fun d hd => smul_flag_fieldConj σ (hD d hd) (hgF d hd)⟩

theorem plusEBlockHomO_fieldConj (σ : K ≃+* K) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b : ℕ}
    (hb : b ∈ D) (g : GLV r K) (hg : g ∈ plusFlagStabO K r D) :
    (plusEBlockHomO hD hb ⟨fieldConj r K σ g, fieldConj_mem_plusFlagStabO σ hD hg⟩ :
      Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) =
      ((plusEBlockHomO hD hb ⟨g, hg⟩ : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K).map σ := by
  rw [coe_plusEBlockHomO, coe_plusEBlockHomO]
  change ((autMat (fieldConj r K σ g)).submatrix _ _) = _
  rw [autMat_fieldConj, Matrix.submatrix_map]

theorem plusResBlockHomO_fieldConj (σ : K ≃+* K) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) (g : GLV r K) (hg : g ∈ plusFlagStabO K r D) :
    (plusResBlockHomO hD ht htm ⟨fieldConj r K σ g, fieldConj_mem_plusFlagStabO σ hD hg⟩ :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      ((plusResBlockHomO hD ht htm ⟨g, hg⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ := by
  rw [coe_plusResBlockHomO, coe_plusResBlockHomO]
  change ((autMat (fieldConj r K σ g)).submatrix _ _) = _
  rw [autMat_fieldConj, Matrix.submatrix_map]

@[expose] def LeviTriv {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D)
    (htm : t + m = r) (g : GLV r K) : Prop :=
  ∃ hg : g ∈ plusFlagStab K r D, (∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb ⟨g, hg⟩ = 1) ∧
    plusResBlockHom hD ht htm ⟨g, hg⟩ = 1

@[expose] def autQ {D : Finset ℕ} (α : MulAut ↥(orthElementaryGroup (quadPlus r K)))
    (q : ↥(plusFlagStab K r D)) : GLV r K :=
  ((α ⟨(q : GLV r K), (mem_plusFlagStab.1 q.2).1⟩ : ↥(orthElementaryGroup (quadPlus r K))) :
    GLV r K)

structure NormFix {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r)
    (α : MulAut ↥(orthElementaryGroup (quadPlus r K))) : Prop where
  stab : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
    (x : GLV r K) ∈ plusFlagStab K r D ↔
      ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) ∈ plusFlagStab K r D
  block : ∀ (q : ↥(plusFlagStab K r D)) (b : ℕ) (hb : b ∈ D)
    (A : Matrix.SpecialLinearGroup (Fin (b - predCut D b)) K), 2 ≤ b - predCut D b →
      (q : GLV r K) = plusFlagLevi K (hD b hb) (Matrix.SpecialLinearGroup.toGL A) →
        LeviTriv hD ht htm (autQ α q * (q : GLV r K)⁻¹)
  res : 2 ≤ m → ∀ (q : ↥(plusFlagStab K r D)) (a b : Fin m ⊕ Fin m) (s : K),
    coordIdx a ≠ coordIdx b → (q : GLV r K) = plusResExt K htm (rpElt a b s) →
      LeviTriv hD ht htm (autQ α q * (q : GLV r K)⁻¹)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
