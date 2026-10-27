module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviCard
public import CFSG.RankThree.PartOne.S11d.OrthRankBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.Classical2 (orthDerived)

section Dickson

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem mem_matrixDerived_of_glIncl [Finite K] [CharP K 2] (hext : IsExtension k Q₀ Q)
    (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (polarBilin Q).Nondegenerate) {x : GL (Fin d) k}
    (hx : glIncl k x ∈ matrixDerived Q) : x ∈ matrixDerived Q₀ := by
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hxO : x ∈ matrixIsometries Q₀ :=
    mem_isometries_of_glIncl k hext (matrixDerived_le_isometries Q hx)
  have hyD : matrixLinearIso (glIncl k x) ∈ orthDerived Q := by
    rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q]
    exact ⟨glIncl k x, hx, rfl⟩
  have hyΩ := orthDerived_le_omegaGroup hnd hyD
  have heven : Even (finrank K (commSpace (matrixLinearEquiv (glIncl k x)))) :=
    (mem_omegaGroup.mp hyΩ).2
  rw [finrank_commSpace_glIncl] at heven
  have hxΩ : matrixLinearIso x ∈ omegaGroup Q₀ hnd₀ := mem_omegaGroup.mpr ⟨hxO, heven⟩
  have h := omegaGroup_le_orthDerived hnd₀ hT₀ hxΩ
  rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q₀] at h
  obtain ⟨x', hx', hx'x⟩ := h
  have : x' = x := matrixLinearIso.injective hx'x
  exact this ▸ hx'

end Dickson

section Plus

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)

variable {m : ℕ}

theorem mem_omegaPlus_iff_reindex {L : Type} [Field L] (A : GL (Fin m ⊕ Fin m) L) :
    A ∈ LargeEvenOmega (LargeEvenQPlus L m) ↔
      reindexMatrixEquiv (plusIndexEquiv m) A ∈ matrixDerived (coordinateQuadPlus m L) := by
  have hQ : ⇑(quadPlus m L) = LargeEvenQPlus L m := coe_quadPlus m L
  constructor
  · intro hA
    have h := (statedDerivedReindexEquiv (plusIndexEquiv m) (quadPlus m L) hQ ⟨A, hA⟩).2
    rw [statedDerivedReindexEquiv_val] at h
    exact h
  · intro hA
    have h := ((statedDerivedReindexEquiv (plusIndexEquiv m) (quadPlus m L) hQ).symm ⟨_, hA⟩).2
    rw [statedDerivedReindexEquiv_symm_val] at h
    simpa using h


theorem reindex_glMap_subtype {L : Type} [Field L] (k : Subfield L) (A : GL (Fin m ⊕ Fin m) k) :
    reindexMatrixEquiv (plusIndexEquiv m) (Matrix.GeneralLinearGroup.map k.subtype A) =
      glIncl k (reindexMatrixEquiv (plusIndexEquiv m) A) := by
  apply Units.ext
  ext i j
  rfl

theorem map_subtype_mem_omegaPlus_iff {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m)
    (k : Subfield K) (A : GL (Fin m ⊕ Fin m) k) :
    Matrix.GeneralLinearGroup.map k.subtype A ∈ LargeEvenOmega (LargeEvenQPlus K m) ↔
      A ∈ LargeEvenOmega (LargeEvenQPlus k m) := by
  rw [mem_omegaPlus_iff_reindex, mem_omegaPlus_iff_reindex, reindex_glMap_subtype]
  have hext := coordinateQuadPlus_isExtension (K := K) k m
  constructor
  · intro h
    exact mem_matrixDerived_of_glIncl hext (regular_coordinateQuadPlus m k hm).1
      (regular_coordinateQuadPlus m k hm).2 (regular_coordinateQuadPlus m K hm).1 h
  · intro h
    exact map_derived_le k hext ⟨_, h, rfl⟩

theorem card_fixed_omegaPlus {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m)
    (σ : K ≃+* K) :
    Nat.card {h : LargeEvenOmega (LargeEvenQPlus K m) //
        Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin m ⊕ Fin m) K) = h} =
      Nat.card (LargeEvenOmega (LargeEvenQPlus (fixF σ) m)) :=
  card_fixed_eq_of_iff σ _ _ fun A => map_subtype_mem_omegaPlus_iff hm (fixF σ) A

theorem twoPart_card_omegaPlus {L : Type} [Field L] [Finite L] {e : ℕ} (he : 1 ≤ e)
    (hL : Nat.card L = 2 ^ e) (hm : 4 ≤ m) :
    twoPart (Nat.card (LargeEvenOmega (LargeEvenQPlus L m))) = 2 ^ (e * (m * (m - 1))) := by
  haveI : CharP L 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hL
  rw [twoPart_card_matrix_group he hL]
  obtain ⟨O, hO, h⟩ :=
    CFSG.SeitzReduction.OmegaPilot.card_statedProj_statedOmega_quadPlus_eq_mul_odd hL he hm
  have h' : Nat.card (StatedProj (LargeEvenOmega (LargeEvenQPlus L m))) =
      Nat.card L ^ (m * (m - 1)) * O := h
  rw [h', hL, ← pow_mul, twoPart_two_pow_mul_odd hO]

theorem stOrderBody_omegaPlus {K : Type} [Field K] [Finite K] (hm : 4 ≤ m) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    (I : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))) :
    StOrderBody p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  refine stOrderBody_of_matrix hn hK (LargeEvenOmega (LargeEvenQPlus K m))
    (fun σ h hh => omegaPlus_map_mem σ h hh) (fun _ => True) (fun _ _ _ => trivial)
    (u := m * (m - 1)) (v := 1) (Nat.mul_pos (by omega) (by omega)) one_pos ?_ ?_ hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩) I
  · rw [pow_one]
    exact twoPart_card_omegaPlus hn hK hm
  · intro σ _ e he
    have hk : Nat.card (fixF σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, card_fixed_omegaPlus (by omega) σ]
    exact twoPart_card_omegaPlus (one_le_of_card_fixed he) hk hm

end Plus

end FQ

end CFSG.LocalAnalysis.GLTheoremA
