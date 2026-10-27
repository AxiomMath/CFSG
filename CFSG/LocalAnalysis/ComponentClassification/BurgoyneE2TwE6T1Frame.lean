module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Lang
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1SL2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Root
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7SL2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open scoped Matrix MatrixGroups


variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]

omit [IsAlgClosed L] in
theorem conj_pinnedX_e6W0 {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    ∃ μ : Lˣ, ∀ c : L, (wordWeylMatrix TwistTag.E6.tag L e6W0Word * diagramMap TwistTag.E6 L) *
      pinnedX TwistTag.E6.tag L α c *
        (wordWeylMatrix TwistTag.E6.tag L e6W0Word * diagramMap TwistTag.E6 L)⁻¹ =
          pinnedX TwistTag.E6.tag L (-α) (μ * c) := by
  obtain ⟨μ, hμ⟩ := wordWeylMatrix_mul_diagramMap_conj_pinnedX (k := L) TwistTag.E6 e6W0Word hα
  exact ⟨μ, fun c => by rw [hμ c, thetaMap_e6W0]⟩

theorem exists_t1_sl2_frame (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [Algebra K L]
    (hK : Nat.card K = p ^ f) (h4 : 4 ≤ Nat.card K) {w : ModGL TwistTag.E6.tag L}
    (hw : w ∈ adjointGroup TwistTag.E6.tag L)
    (hcoc : w * (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) w)⁻¹ =
      wordWeylMatrix TwistTag.E6.tag L e6W0Word) :
    ∃ (S' : Subgroup (ModGL TwistTag.E6.tag L)) (e : SL2 K ≃* S'),
      ((e (-1) : S') : ModGL TwistTag.E6.tag L) =
        rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) (-1) ∧
      (∀ s ∈ S', w⁻¹ * s * w ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag L)
            (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))⁆) ∧
      (∀ z ∈ adjointGroup TwistTag.E6.tag L, w⁻¹ * z * w ∈ fixedPointsIn
          (adjointGroup TwistTag.E6.tag L)
          (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) →
        z * rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) (-1) =
          rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) (-1) * z →
        ∀ s ∈ S', z * s * z⁻¹ ∈ S') ∧
      (∀ b : Fin TwistTag.E6.tag.rank → Lˣ, w⁻¹ * rootDiagUnit TwistTag.E6.tag b * w ∈
          fixedPointsIn (adjointGroup TwistTag.E6.tag L)
            (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) →
        ∀ s ∈ S', rootDiagUnit TwistTag.E6.tag b * s * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈ S') ∧
      ∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
        (∀ s ∈ S', rootDiagUnit TwistTag.E6.tag b * s = s * rootDiagUnit TwistTag.E6.tag b) →
          rootChar b (Pi.single (t1Node 2) 1) = 1 := by
  classical
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
    (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set Fr := iterateFrobenius L p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr_def, iterateFrobenius_def, hK]
  set N := wordWeylMatrix TwistTag.E6.tag L e6W0Word with hN
  set P := diagramMap TwistTag.E6 L with hP
  set β := (Pi.single (t1Node 2) 1 : Fin TwistTag.E6.tag.rank → ℤ) with hβ
  have hβr : IsRoot TwistTag.E6.tag β := isRoot_single TwistTag.E6.tag _
  have hF1 : ∀ y : ModGL TwistTag.E6.tag L,
      frobTwistGL TwistTag.E6.tag L p f P y = P * Units.map (entrywiseHom Fr) y * P⁻¹ :=
    fun y => frobTwistGL_apply p f P y
  have hFw : frobTwistGL TwistTag.E6.tag L p f P w = N⁻¹ * w := by
    have h1 : (frobTwistGL TwistTag.E6.tag L p f P w)⁻¹ = w⁻¹ * N := by rw [← hcoc]; group
    calc frobTwistGL TwistTag.E6.tag L p f P w =
        ((frobTwistGL TwistTag.E6.tag L p f P w)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (w⁻¹ * N)⁻¹ := by rw [h1]
      _ = N⁻¹ * w := by group
  have hfix : ∀ z, w⁻¹ * z * w ∈ R →
      (N * P) * Units.map (entrywiseHom Fr) z * (N * P)⁻¹ = z := by
    intro z hz
    have h := (mem_fixedPointsIn.1 hz).2
    rw [map_mul, map_mul, map_inv, hFw, hF1 z] at h
    calc (N * P) * Units.map (entrywiseHom Fr) z * (N * P)⁻¹ =
        w * ((N⁻¹ * w)⁻¹ * (P * Units.map (entrywiseHom Fr) z * P⁻¹) * (N⁻¹ * w)) * w⁻¹ := by
          group
      _ = z := by rw [h]; group
  obtain ⟨Pm, hPm⟩ := exists_rootSL2_fixed_of_neg (K := K) Fr hFr (m := N * P)
    (fun α hα => conj_pinnedX_e6W0 hα) hβr
  set SK := (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL Pm) with hSK
  have hρinj : Function.Injective (rootSL2 TwistTag.E6.tag L β) := rootSL2_injective_of_field β
  have hSLinj : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hPinj : Function.Injective (conjSL Pm) := fun A B h => by
    have h1 := congrArg (conjSL Pm⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let e : SL2 K ≃* SK.map (rootSL2 TwistTag.E6.tag L β) := (MonoidHom.ofInjective hSLinj).trans
    ((Subgroup.equivMapOfInjective _ _ hPinj).trans (SK.equivMapOfInjective _ hρinj))
  have he : ∀ A, ((e A : SK.map (rootSL2 TwistTag.E6.tag L β)) : ModGL TwistTag.E6.tag L) =
      rootSL2 TwistTag.E6.tag L β (conjSL Pm (SpecialLinearGroup.map (algebraMap K L) A)) :=
    fun A => rfl
  have hρG : ∀ A, rootSL2 TwistTag.E6.tag L β A ∈ adjointGroup TwistTag.E6.tag L :=
    (exceptional_Lang_root_rank_one_data TwistTag.E6.tag L β).2.2.2.2.1
  have hnorm : ∀ z, (N * P) * Units.map (entrywiseHom Fr) z * (N * P)⁻¹ = z →
      (∀ B, ∃ B', z * rootSL2 TwistTag.E6.tag L β B * z⁻¹ = rootSL2 TwistTag.E6.tag L β B') →
      ∀ s ∈ SK.map (rootSL2 TwistTag.E6.tag L β),
        z * s * z⁻¹ ∈ SK.map (rootSL2 TwistTag.E6.tag L β) := by
    rintro z hz hzn _ ⟨B, hB, rfl⟩
    obtain ⟨B', hB'⟩ := hzn B
    refine ⟨B', (hPm B').1 ?_, hB'.symm⟩
    rw [← hB']
    calc (N * P) * Units.map (entrywiseHom Fr) (z * rootSL2 TwistTag.E6.tag L β B * z⁻¹) *
          (N * P)⁻¹ =
        ((N * P) * Units.map (entrywiseHom Fr) z * (N * P)⁻¹) *
          ((N * P) * Units.map (entrywiseHom Fr) (rootSL2 TwistTag.E6.tag L β B) * (N * P)⁻¹) *
            ((N * P) * Units.map (entrywiseHom Fr) z * (N * P)⁻¹)⁻¹ := by
          rw [map_mul, map_mul, map_inv]; group
      _ = z * rootSL2 TwistTag.E6.tag L β B * z⁻¹ := by rw [hz, (hPm B).2 hB]
  refine ⟨SK.map (rootSL2 TwistTag.E6.tag L β), e, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : SpecialLinearGroup.map (algebraMap K L) (-1 : SL2 K) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h2 : conjSL Pm (-1 : SL2 L) = -1 := by
      ext i j
      rw [coe_conjSL]
      simp
    rw [he, h1, h2]
  · have hqS : CFSG.IsQuasisimple (SK.map (rootSL2 TwistTag.E6.tag L β)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (SK.equivMapOfInjective _ hρinj)
        (sl2_conj_range_quasisimple (K := K) h4 Pm).2
    have hperf : ⁅SK.map (rootSL2 TwistTag.E6.tag L β), SK.map (rootSL2 TwistTag.E6.tag L β)⁆ =
        SK.map (rootSL2 TwistTag.E6.tag L β) := Subgroup.isPerfect_iff.1 hqS.1
    set S'' := (SK.map (rootSL2 TwistTag.E6.tag L β)).map (MulAut.conj w⁻¹).toMonoidHom with hS''
    have hS''R : S'' ≤ R := by
      rintro _ ⟨s, ⟨B, hB, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem hw) (hρG B)) hw, ?_⟩
      rw [map_mul, map_mul, map_inv, hFw, hF1]
      calc (N⁻¹ * w)⁻¹ * (P * Units.map (entrywiseHom Fr) (rootSL2 TwistTag.E6.tag L β B) * P⁻¹) *
            (N⁻¹ * w) =
          w⁻¹ * ((N * P) * Units.map (entrywiseHom Fr) (rootSL2 TwistTag.E6.tag L β B) *
            (N * P)⁻¹) * w := by group
        _ = w⁻¹ * rootSL2 TwistTag.E6.tag L β B * w := by rw [(hPm B).2 hB]
    have hperf'' : ⁅S'', S''⁆ = S'' := by rw [hS'', ← Subgroup.map_commutator, hperf]
    intro s hs
    have hmem : w⁻¹ * s * w ∈ S'' := ⟨s, hs, by simp⟩
    rw [← hperf''] at hmem
    exact Subgroup.commutator_mono hS''R hS''R hmem
  · intro z hz hzR hzt
    exact hnorm z (hfix z hzR) (exists_conj_rootSL2_three hL2 hz hzt)
  · intro b hb
    exact hnorm _ (hfix _ hb) fun B =>
      ⟨_, RankThree.Chevalley.rootDiagUnit_conj_rootSL2 b hβr B⟩
  · intro b hb
    refine TwE7.eq_one_of_conjSL_diagUnitOne (K := K) Pm fun B hB => hρinj ?_
    rw [← RankThree.Chevalley.rootDiagUnit_conj_rootSL2 b hβr B, hb _ ⟨B, hB, rfl⟩,
      mul_inv_cancel_right]

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
