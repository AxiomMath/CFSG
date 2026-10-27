module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusSemi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusSL
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusHas
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonDefs
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate8026Base
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock

variable {K : Type} [Field K] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

section Coord

variable (hd : OrthCuts r d)

@[expose] def blkVec (l : Fin s) (j : Fin (d l.succ - d l.castSucc)) :
    (Fin r ⊕ Fin r → K) × (Fin 2 → K) :=
  hypVec K (Fin 2 → K) (.inl (orthBlockIdx hd l j))

@[expose] def evB (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) :
    (Fin r ⊕ Fin r → K) × (Fin 2 → K) :=
  ∑ j, u j • blkVec hd l j

@[expose] def coordB (l : Fin s) (w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)) :
    Fin (d l.succ - d l.castSucc) → K :=
  fun i => w.1 (.inl (orthBlockIdx hd l i))

theorem evB_add (l : Fin s) (u v : Fin (d l.succ - d l.castSucc) → K) :
    evB hd l (u + v) = evB hd l u + evB hd l v := by
  simp [evB, add_smul, Finset.sum_add_distrib]

theorem evB_smul (l : Fin s) (a : K) (u : Fin (d l.succ - d l.castSucc) → K) :
    evB hd l (a • u) = a • evB hd l u := by
  simp [evB, Finset.smul_sum, smul_smul]

theorem evB_zero (l : Fin s) : evB hd l (0 : Fin (d l.succ - d l.castSucc) → K) = 0 := by
  simp [evB]

theorem coordB_add (l : Fin s) (v w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)) :
    coordB hd l (v + w) = coordB hd l v + coordB hd l w := rfl

theorem coordB_smul (l : Fin s) (a : K) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)) :
    coordB hd l (a • v) = a • coordB hd l v := rfl

theorem evB_fst_inr (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) (q : Fin r) :
    (evB hd l u).1 (.inr q) = 0 := by
  simp [evB, blkVec, hypVec, Prod.fst_sum, Finset.sum_apply]

theorem evB_snd (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) : (evB hd l u).2 = 0 := by
  simp [evB, blkVec, hypVec, Prod.snd_sum]

theorem evB_fst_inl (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) (p : Fin r) :
    (evB hd l u).1 (.inl p) =
      ∑ j, if p = orthBlockIdx hd l j then u j else 0 := by
  simp only [evB, blkVec, hypVec, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p = orthBlockIdx hd l j
  · subst h
    simp
  · have h' : (Sum.inl p : Fin r ⊕ Fin r) ≠ .inl (orthBlockIdx hd l j) := fun e =>
      h (Sum.inl_injective e)
    simp [Pi.single_apply, h, h']

theorem coordB_evB (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) :
    coordB hd l (evB hd l u) = u := by
  funext i
  rw [coordB, evB_fst_inl, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg]
    exact fun h => hji ((orthBlockIdx_injective hd l h).symm)
  · simp

theorem evB_fst_inl_of_not_mem (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) {p : Fin r}
    (hp : (p : ℕ) < d l.castSucc ∨ d l.succ ≤ (p : ℕ)) : (evB hd l u).1 (.inl p) = 0 := by
  rw [evB_fst_inl]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  intro h
  have := (mem_range_orthBlockIdx hd l p).1 ⟨j, h.symm⟩
  omega

theorem evB_mem_flag (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) :
    evB hd l u ∈ tailFlag K (Fin 2 → K) r (d l.succ) := by
  rw [mem_tailFlag_iff]
  refine ⟨mem_flag.2 ⟨evB_fst_inr hd l u, fun p hp => ?_⟩, evB_snd hd l u⟩
  exact evB_fst_inl_of_not_mem hd l u (Or.inr hp)

theorem sub_evB_mem (l : Fin s) {w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)}
    (hw : w ∈ tailFlag K (Fin 2 → K) r (d l.succ)) :
    w - evB hd l (coordB hd l w) ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := by
  obtain ⟨hw1, hw2⟩ := mem_tailFlag_iff.1 hw
  obtain ⟨hwr, hwl⟩ := mem_flag.1 hw1
  rw [mem_tailFlag_iff]
  refine ⟨mem_flag.2 ⟨fun q => ?_, fun p hp => ?_⟩, ?_⟩
  · rw [Prod.fst_sub, Pi.sub_apply, evB_fst_inr, hwr q, sub_zero]
  · rw [Prod.fst_sub, Pi.sub_apply]
    by_cases hps : (p : ℕ) < d l.succ
    · obtain ⟨i, rfl⟩ := (mem_range_orthBlockIdx hd l p).2 ⟨hp, hps⟩
      have := congrFun (coordB_evB hd l (coordB hd l w)) i
      rw [coordB] at this
      rw [this]
      exact sub_eq_zero.2 rfl
    · rw [hwl p (not_lt.1 hps), evB_fst_inl_of_not_mem hd l _ (Or.inr (not_lt.1 hps)), sub_zero]
  · rw [Prod.snd_sub, hw2, evB_snd, sub_zero]

theorem coordB_eq_zero (l : Fin s) {w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)}
    (hw : w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc)) :
    coordB hd l w = 0 := by
  funext i
  obtain ⟨hw1, -⟩ := mem_tailFlag_iff.1 hw
  have := (mem_flag.1 hw1).2 (orthBlockIdx hd l i) (by rw [orthBlockIdx_val]; omega)
  exact this

theorem coordB_map_evB (l : Fin s)
    (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
    (u : Fin (d l.succ - d l.castSucc) → K) :
    coordB hd l (g (evB hd l u)) = orthBlockMat hd l g *ᵥ u := by
  funext i
  simp only [coordB, evB, map_sum, map_smul, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, orthBlockMat, orthCoefMat_apply,
    Matrix.submatrix_apply, blkVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem coordB_map_eq {G : Type*} [FunLike G ((Fin r ⊕ Fin r → K) × (Fin 2 → K))
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))] [AddMonoidHomClass G ((Fin r ⊕ Fin r → K) × (Fin 2 → K))
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))] (g : G) (l : Fin s)
    (hg : ∀ w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc),
      g w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc))
    {w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)} (hw : w ∈ tailFlag K (Fin 2 → K) r (d l.succ)) :
    coordB hd l (g w) = coordB hd l (g (evB hd l (coordB hd l w))) := by
  have h1 := sub_evB_mem hd l hw
  have h2 := coordB_eq_zero hd l (hg _ h1)
  have h3 : g w = g (w - evB hd l (coordB hd l w)) + g (evB hd l (coordB hd l w)) := by
    rw [← map_add, sub_add_cancel]
  rw [h3, coordB_add, h2, zero_add]

end Coord

section Phi

variable (hd : OrthCuts r d) (S : SemiData K r b c)

@[expose] def phiB (l : Fin s) (u : Fin (d l.succ - d l.castSucc) → K) :
    Fin (d l.succ - d l.castSucc) → K :=
  coordB hd l (S.F (evB hd l u))

theorem phiB_add (l : Fin s) (u v : Fin (d l.succ - d l.castSucc) → K) :
    phiB hd S l (u + v) = phiB hd S l u + phiB hd S l v := by
  rw [phiB, evB_add, map_add, coordB_add]
  rfl

theorem phiB_smul (l : Fin s) (a : K) (u : Fin (d l.succ - d l.castSucc) → K) :
    phiB hd S l (a • u) = S.σ a • phiB hd S l u := by
  rw [phiB, evB_smul, S.hF, coordB_smul]
  rfl

theorem phiB_injective
    (hflag : ∀ (i : Fin (s + 1)) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)),
      S.F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i))
    (l : Fin s) : Function.Injective (phiB hd S l) := by
  have hadd : ∀ u v, phiB hd S l (u + v) = phiB hd S l u + phiB hd S l v := phiB_add hd S l
  have hinj : Function.Injective (AddMonoidHom.mk' (phiB hd S l) hadd) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hu' : phiB hd S l u = 0 := hu
    have hw : S.F (evB hd l u) ∈ tailFlag K (Fin 2 → K) r (d l.succ) :=
      (hflag l.succ _).2 (evB_mem_flag hd l u)
    have h1 := sub_evB_mem hd l hw
    rw [show coordB hd l (S.F (evB hd l u)) = 0 from hu', evB_zero, sub_zero] at h1
    have h2 : evB hd l u ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := (hflag l.castSucc _).1 h1
    have h3 := coordB_eq_zero hd l h2
    rwa [coordB_evB] at h3
  exact hinj

theorem phiB_comm
    (hflag : ∀ (i : Fin (s + 1)) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)),
      S.F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i))
    (l : Fin s) (x y : ↥(orthParab r (minusTailForm K b c) d))
    (hxy : orthBlockMat hd l ((y : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) =
      orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _))
    (hconj : ∀ v, ((y : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) v =
      S.F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) (S.F.symm v)))
    (u : Fin (d l.succ - d l.castSucc) → K) :
    phiB hd S l (orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r
        (minusTailForm K b c)))) : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) *ᵥ u) =
      orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) *ᵥ phiB hd S l u := by
  set X : 𝕍 ≃ₗ[K] 𝕍 := ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    𝕍 ≃ₗ[K] 𝕍) with hX
  set Y : 𝕍 ≃ₗ[K] 𝕍 := ((y : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    𝕍 ≃ₗ[K] 𝕍) with hY
  have hXhi : ∀ w ∈ tailFlag K (Fin 2 → K) r (d l.succ),
      X w ∈ tailFlag K (Fin 2 → K) r (d l.succ) :=
    mapsTo_of_mem_orthParab x.2 l.succ
  have hYlo : ∀ w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc),
      Y w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := mapsTo_of_mem_orthParab y.2 l.castSucc
  have hFlo : ∀ w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc),
      S.F w ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := fun w hw => (hflag l.castSucc w).2 hw
  have hFhi : ∀ w ∈ tailFlag K (Fin 2 → K) r (d l.succ),
      S.F w ∈ tailFlag K (Fin 2 → K) r (d l.succ) := fun w hw => (hflag l.succ w).2 hw
  have e1 : coordB hd l (S.F (X (evB hd l u))) =
      phiB hd S l (orthBlockMat hd l X *ᵥ u) := by
    have h := coordB_map_eq hd S.F l hFlo (hXhi _ (evB_mem_flag hd l u))
    rw [h, coordB_map_evB]
    rfl
  have e2 : coordB hd l (Y (S.F (evB hd l u))) = orthBlockMat hd l Y *ᵥ phiB hd S l u := by
    have h := coordB_map_eq hd Y l hYlo (hFhi _ (evB_mem_flag hd l u))
    rw [h]
    exact coordB_map_evB hd l Y _
  have e3 : Y (S.F (evB hd l u)) = S.F (X (evB hd l u)) := by
    rw [hconj, AddEquiv.symm_apply_apply]
  rw [← e1, ← e3, e2, hxy]

theorem block_sigma_and_scalar
    (hflag : ∀ (i : Fin (s + 1)) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)),
      S.F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i))
    (l : Fin s) (hk : 2 ≤ d l.succ - d l.castSucc)
    (hrel : ∀ (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K)
      (u : Fin (d l.succ - d l.castSucc) → K),
      phiB hd S l ((B : Matrix _ _ K) *ᵥ u) = (B : Matrix _ _ K) *ᵥ phiB hd S l u) :
    (∀ a : K, S.σ a = a) ∧ ∃ a : K, a ≠ 0 ∧ ∀ u, phiB hd S l u = a • u :=
  sl_schur hk S.σ (phiB hd S l) (phiB_add hd S l) (phiB_smul hd S l)
    (phiB_injective hd S hflag l) hrel

theorem phiB_scalar_of_le_one (hσ : ∀ a : K, S.σ a = a) (l : Fin s)
    (hk : d l.succ - d l.castSucc ≤ 1) :
    ∃ a : K, ∀ u, phiB hd S l u = a • u := by
  have hpos : 0 < d l.succ - d l.castSucc := by
    have := hd.mono (Fin.castSucc_lt_succ (i := l))
    omega
  let i₀ : Fin (d l.succ - d l.castSucc) := ⟨0, hpos⟩
  have hi : ∀ i : Fin (d l.succ - d l.castSucc), i = i₀ := fun i => Fin.ext (by
    have := i.isLt
    simp only [i₀]
    omega)
  have hu : ∀ u : Fin (d l.succ - d l.castSucc) → K, u = u i₀ • (Pi.single i₀ 1 : _ → K) := by
    intro u
    funext i
    rw [hi i]
    simp
  set a := phiB hd S l (Pi.single i₀ 1) i₀ with ha
  have h1 : phiB hd S l (Pi.single i₀ 1) = a • Pi.single i₀ 1 := by
    funext i
    rw [hi i]
    simp [ha]
  refine ⟨a, fun u => ?_⟩
  calc phiB hd S l u = phiB hd S l (u i₀ • (Pi.single i₀ 1 : _ → K)) := by rw [← hu u]
    _ = u i₀ • (a • (Pi.single i₀ 1 : _ → K)) := by rw [phiB_smul, hσ, h1]
    _ = a • (u i₀ • (Pi.single i₀ 1 : _ → K)) := smul_comm _ _ _
    _ = a • u := by rw [← hu u]

theorem scalarMod_of_phiB
    (hflag : ∀ (i : Fin (s + 1)) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)),
      S.F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i))
    (l : Fin s) {a : K} (ha : ∀ u, phiB hd S l u = a • u) :
    ∀ v ∈ tailFlag K (Fin 2 → K) r (d l.succ),
      S.F v - a • v ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) := by
  intro v hv
  set u := coordB hd l v with hu
  have h1 := sub_evB_mem hd l hv
  have h2 : S.F (v - evB hd l u) ∈ tailFlag K (Fin 2 → K) r (d l.castSucc) :=
    (hflag l.castSucc _).2 h1
  have h3 := sub_evB_mem hd l ((hflag l.succ _).2 (evB_mem_flag hd l u))
  rw [show coordB hd l (S.F (evB hd l u)) = a • u from ha u, evB_smul] at h3
  have h4 : S.F v - a • v = S.F (v - evB hd l u) + (S.F (evB hd l u) - a • evB hd l u) -
      a • (v - evB hd l u) := by
    rw [map_sub]
    simp only [smul_sub]
    abel
  rw [h4]
  exact Submodule.sub_mem _ (Submodule.add_mem _ h2 h3) (Submodule.smul_mem _ _ h1)

end Phi

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
