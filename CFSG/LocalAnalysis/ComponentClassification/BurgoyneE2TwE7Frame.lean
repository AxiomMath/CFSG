module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Beta
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7SL2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Chevalley.ToralSign (e7Word2_1)
open scoped Matrix MatrixGroups


variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]

theorem exists_twisted_sl2_frame (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [Algebra K L]
    (hK : Nat.card K = p ^ f) (h4 : 4 ≤ Nat.card K) {g₁ : ModGL .E7 L}
    (hg₁ : g₁ ∈ adjointGroup .E7 L)
    (hcoc : g₁ * (frobTwistGL .E7 L p f 1 g₁)⁻¹ = wordWeylMatrix .E7 L e7Word2_1) :
    ∃ (S' : Subgroup (ModGL .E7 L)) (e : SL2 K ≃* S'),
      ((e (-1) : S') : ModGL .E7 L) = rootSL2 .E7 L e7Beta0 (-1) ∧
      (∀ w ∈ S', g₁⁻¹ * w * g₁ ∈ ⁅fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1),
        fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1)⁆) ∧
      (∀ z ∈ adjointGroup .E7 L,
        g₁⁻¹ * z * g₁ ∈ fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) →
        z * rootSL2 .E7 L e7Beta0 (-1) = rootSL2 .E7 L e7Beta0 (-1) * z →
        ∀ w ∈ S', z * w * z⁻¹ ∈ S') ∧
      (∀ b : Fin (Tag.rank .E7) → Lˣ, g₁⁻¹ * rootDiagUnit .E7 b * g₁ ∈
          fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) →
        ∀ w ∈ S', rootDiagUnit .E7 b * w * (rootDiagUnit .E7 b)⁻¹ ∈ S') ∧
      ∀ b : Fin (Tag.rank .E7) → Lˣ,
        (∀ w ∈ S', rootDiagUnit .E7 b * w = w * rootDiagUnit .E7 b) → rootChar b e7Beta0 = 1 := by
  classical
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
  set R := fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) with hR
  set Fr := iterateFrobenius L p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr_def, iterateFrobenius_def, hK]
  set N := wordWeylMatrix .E7 L e7Word2_1 with hN
  have hF1 : ∀ w : ModGL .E7 L, frobTwistGL .E7 L p f 1 w = Units.map (entrywiseHom Fr) w :=
    fun w => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hFg₁ : Units.map (entrywiseHom Fr) g₁ = N⁻¹ * g₁ := by
    have h1 : (Units.map (entrywiseHom Fr) g₁)⁻¹ = g₁⁻¹ * N := by rw [← hF1, ← hcoc]; group
    calc Units.map (entrywiseHom Fr) g₁ = ((Units.map (entrywiseHom Fr) g₁)⁻¹)⁻¹ :=
          (inv_inv _).symm
      _ = (g₁⁻¹ * N)⁻¹ := by rw [h1]
      _ = N⁻¹ * g₁ := by group
  have hfix : ∀ z, g₁⁻¹ * z * g₁ ∈ R → N * Units.map (entrywiseHom Fr) z * N⁻¹ = z := by
    intro z hz
    have h := (mem_fixedPointsIn.1 hz).2
    rw [hF1, map_mul, map_mul, map_inv, hFg₁] at h
    calc N * Units.map (entrywiseHom Fr) z * N⁻¹ =
        g₁ * ((N⁻¹ * g₁)⁻¹ * Units.map (entrywiseHom Fr) z * (N⁻¹ * g₁)) * g₁⁻¹ := by group
      _ = z := by rw [h]; group
  obtain ⟨P, hP⟩ := exists_twisted_rootSL2_fixed (K := K) Fr hFr e7Word2_1 isRoot_e7Beta0
    wordElt_e7Word2_1_e7Beta0
  set SK := (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) with hSK
  have hρinj : Function.Injective (rootSL2 .E7 L e7Beta0) := rootSL2_injective_of_field e7Beta0
  have hSLinj : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let e : SL2 K ≃* SK.map (rootSL2 .E7 L e7Beta0) := (MonoidHom.ofInjective hSLinj).trans
    ((Subgroup.equivMapOfInjective _ _ hPinj).trans (SK.equivMapOfInjective _ hρinj))
  have he : ∀ A, ((e A : SK.map (rootSL2 .E7 L e7Beta0)) : ModGL .E7 L) =
      rootSL2 .E7 L e7Beta0 (conjSL P (SpecialLinearGroup.map (algebraMap K L) A)) :=
    fun A => rfl
  have hρG : ∀ A, rootSL2 .E7 L e7Beta0 A ∈ adjointGroup .E7 L :=
    (exceptional_Lang_root_rank_one_data .E7 L e7Beta0).2.2.2.2.1
  have hnorm : ∀ z, N * Units.map (entrywiseHom Fr) z * N⁻¹ = z →
      (∀ B, ∃ B', z * rootSL2 .E7 L e7Beta0 B * z⁻¹ = rootSL2 .E7 L e7Beta0 B') →
      ∀ w ∈ SK.map (rootSL2 .E7 L e7Beta0), z * w * z⁻¹ ∈ SK.map (rootSL2 .E7 L e7Beta0) := by
    rintro z hz hzn _ ⟨B, hB, rfl⟩
    obtain ⟨B', hB'⟩ := hzn B
    refine ⟨B', (hP B').1 ?_, hB'.symm⟩
    rw [← hB']
    calc N * Units.map (entrywiseHom Fr) (z * rootSL2 .E7 L e7Beta0 B * z⁻¹) * N⁻¹ =
        (N * Units.map (entrywiseHom Fr) z * N⁻¹) *
          (N * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7Beta0 B) * N⁻¹) *
            (N * Units.map (entrywiseHom Fr) z * N⁻¹)⁻¹ := by
          rw [map_mul, map_mul, map_inv]; group
      _ = z * rootSL2 .E7 L e7Beta0 B * z⁻¹ := by rw [hz, (hP B).2 hB]
  refine ⟨SK.map (rootSL2 .E7 L e7Beta0), e, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : SpecialLinearGroup.map (algebraMap K L) (-1 : SL2 K) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h2 : conjSL P (-1 : SL2 L) = -1 := by
      ext i j
      rw [coe_conjSL]
      simp
    rw [he, h1, h2]
  · have hqS : CFSG.IsQuasisimple (SK.map (rootSL2 .E7 L e7Beta0)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (SK.equivMapOfInjective _ hρinj)
        (sl2_conj_range_quasisimple (K := K) h4 P).2
    have hperf : ⁅SK.map (rootSL2 .E7 L e7Beta0), SK.map (rootSL2 .E7 L e7Beta0)⁆ =
        SK.map (rootSL2 .E7 L e7Beta0) := Subgroup.isPerfect_iff.1 hqS.1
    set S'' := (SK.map (rootSL2 .E7 L e7Beta0)).map (MulAut.conj g₁⁻¹).toMonoidHom with hS''
    have hS''R : S'' ≤ R := by
      rintro _ ⟨w, ⟨B, hB, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem hg₁) (hρG B)) hg₁, ?_⟩
      rw [hF1, map_mul, map_mul, map_inv, hFg₁]
      calc (N⁻¹ * g₁)⁻¹ * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7Beta0 B) * (N⁻¹ * g₁) =
          g₁⁻¹ * (N * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7Beta0 B) * N⁻¹) * g₁ := by
            group
        _ = g₁⁻¹ * rootSL2 .E7 L e7Beta0 B * g₁ := by rw [(hP B).2 hB]
    have hperf'' : ⁅S'', S''⁆ = S'' := by rw [hS'', ← Subgroup.map_commutator, hperf]
    intro w hw
    have hmem : g₁⁻¹ * w * g₁ ∈ S'' := ⟨w, hw, by simp⟩
    rw [← hperf''] at hmem
    exact Subgroup.commutator_mono hS''R hS''R hmem
  · intro z hz hzR hzt
    exact hnorm z (hfix z hzR) (exists_conj_rootSL2_e7Beta0 hL2 hz hzt)
  · intro b hb
    exact hnorm _ (hfix _ hb) fun B =>
      ⟨_, RankThree.Chevalley.rootDiagUnit_conj_rootSL2 b isRoot_e7Beta0 B⟩
  · intro b hb
    refine eq_one_of_conjSL_diagUnitOne (K := K) P fun B hB => hρinj ?_
    rw [← RankThree.Chevalley.rootDiagUnit_conj_rootSL2 b isRoot_e7Beta0 B, hb _ ⟨B, hB, rfl⟩,
      mul_inv_cancel_right]

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
