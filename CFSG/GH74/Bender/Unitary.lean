module

public import CFSG.GH74.SectionalRank
public import CFSG.GH74.SmallRanks.Basic
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryPoint
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12

public section

namespace CFSG.GH74.Bender

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.BenderSuzuki.External
  CFSG.ShultStronglyClosedTI.TwoCoreGrowth

section Heisenberg

variable {K : Type} [Field K]

@[expose] def firstCoordinate (J : HermitianForm 3 K) :
    hermitianUnipotentCoord J →* Multiplicative K where
  toFun z := Multiplicative.ofAdd z.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mem_ker_firstCoordinate (J : HermitianForm 3 K) (z : hermitianUnipotentCoord J) :
    z ∈ (firstCoordinate J).ker ↔ z.1.1 = 0 := by
  rw [MonoidHom.mem_ker]
  exact ofAdd_eq_one

theorem conj_snd_eq_of_fst_eq_zero [CharP K 2] (J : HermitianForm 3 K)
    {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) : J.conj z.1.2 = z.1.2 := by
  have h : z.1.2 + J.conj z.1.2 + z.1.1 * J.conj z.1.1 = 0 := z.2
  rw [hz, map_zero, mul_zero, add_zero] at h
  rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]

theorem fst_eq_zero_of_sq_eq_one [CharP K 2] (J : HermitianForm 3 K)
    {z : hermitianUnipotentCoord J} (h : z ^ 2 = 1) : z.1.1 = 0 := by
  rw [pow_two] at h
  change hermitianUnipotentMul J z z = hermitianUnipotentOne J at h
  have h2 := congrArg (fun w : hermitianUnipotentCoord J => w.1.2) h
  simp only [hermitianUnipotentMul, hermitianUnipotentOne] at h2
  rw [CharTwo.add_self_eq_zero, zero_sub, neg_eq_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact EmbeddingLike.map_eq_zero_iff.mp h3

theorem card_ker_firstCoordinate_le [CharP K 2] [Finite K] (J : HermitianForm 3 K) {q : ℕ}
    (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    Nat.card (firstCoordinate J).ker ≤ q := by
  classical
  rw [← hfixed]
  refine Nat.card_le_card_of_injective
    (fun z => (⟨z.1.1.2, conj_snd_eq_of_fst_eq_zero J
      ((mem_ker_firstCoordinate J z.1).mp z.2)⟩ : {x : K // J.conj x = x})) ?_
  intro z z' hzz
  have hb : z.1.1.2 = z'.1.1.2 := congrArg Subtype.val hzz
  have ha : z.1.1.1 = z'.1.1.1 :=
    ((mem_ker_firstCoordinate J z.1).mp z.2).trans ((mem_ker_firstCoordinate J z'.1).mp z'.2).symm
  exact Subtype.ext (Subtype.ext (Prod.ext ha hb))

end Heisenberg

section Unitary

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ)

theorem charP_two_of_card_sq (hcard : Nat.card K = (2 ^ f) ^ 2) : CharP K 2 :=
  CFSG.ShultStronglyClosedTI.LinearModel.charP_two_of_card (f := f * 2)
    (by rw [hcard, pow_mul])

theorem twoRank_projectiveSpecialUnitary_le (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)] :
    CFSG.Open.twoRank (ProjectiveSpecialUnitaryMatrixGroup J) ≤ f := by
  classical
  have : CharP K 2 := charP_two_of_card_sq f hcard
  obtain ⟨-, S, -, -, -, hSR, -⟩ := unitary_entire_root_point_structure J f hf hcard hfixed hJ
  have hψ : Function.Injective (hermitianUnipotentPSU J hJ) :=
    CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  refine SmallRanks.twoRank_le_of_sylow S (fun E hES hE => ?_)
  have hER : E ≤ (hermitianUnipotentPSU J hJ).range := by
    rw [← hSR]
    exact hES
  have hcardE : Nat.card E = Nat.card (E.comap (hermitianUnipotentPSU J hJ)) := by
    have h := Subgroup.card_map_of_injective hψ (K := E.comap (hermitianUnipotentPSU J hJ))
    rwa [Subgroup.map_comap_eq_self hER] at h
  have hle : E.comap (hermitianUnipotentPSU J hJ) ≤ (firstCoordinate J).ker := by
    intro z hz
    rw [mem_ker_firstCoordinate]
    apply fst_eq_zero_of_sq_eq_one J
    apply hψ
    rw [map_pow, map_one]
    exact hE.2 _ hz
  calc Nat.card E = Nat.card (E.comap (hermitianUnipotentPSU J hJ)) := hcardE
    _ ≤ Nat.card (firstCoordinate J).ker := Subgroup.card_le_of_le hle
    _ ≤ 2 ^ f := card_ker_firstCoordinate_le J hfixed

theorem le_two_of_gen4_projectiveSpecialUnitary (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hgen : Gen4 (ProjectiveSpecialUnitaryMatrixGroup J)) : f ≤ 2 := by
  classical
  have : CharP K 2 := charP_two_of_card_sq f hcard
  have hψ : Function.Injective (hermitianUnipotentPSU J hJ) :=
    CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hfin : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
    have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    exact Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J => (x : Matrix.ProjGenLinGroup (Fin 3) K))
      Subtype.coe_injective
  have : Finite (hermitianUnipotentCoord J) := Finite.of_injective _ hψ
  have hHcard : Nat.card (hermitianUnipotentCoord J) = (2 ^ f) ^ 3 := by
    obtain ⟨-, S, -, -, -, hSR, hScard, -⟩ :=
      unitary_entire_root_point_structure J f hf hcard hfixed hJ
    have h1 : Nat.card (hermitianUnipotentPSU J hJ).range =
        Nat.card (hermitianUnipotentCoord J) :=
      Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
    rw [← h1, ← hSR]
    exact hScard
  have hker := card_ker_firstCoordinate_le J hfixed
  have hmul := Subgroup.card_ker_mul_card_range (firstCoordinate J)
  have hq : 0 < 2 ^ f := by positivity
  have hV : (2 ^ f) ^ 2 ≤ Nat.card (firstCoordinate J).range := by
    have h1 : 2 ^ f * (2 ^ f) ^ 2 ≤ 2 ^ f * Nat.card (firstCoordinate J).range := by
      calc 2 ^ f * (2 ^ f) ^ 2 = (2 ^ f) ^ 3 := by ring
        _ = Nat.card (firstCoordinate J).ker * Nat.card (firstCoordinate J).range := by
          rw [hmul, hHcard]
        _ ≤ 2 ^ f * Nat.card (firstCoordinate J).range := Nat.mul_le_mul_right _ hker
    exact Nat.le_of_mul_le_mul_left h1 hq
  have hgenH : Gen4 (hermitianUnipotentCoord J) := Gen4.of_injective _ hψ hgen
  have hgenV : Gen4 (firstCoordinate J).range :=
    Gen4.of_surjective (firstCoordinate J).rangeRestrict
      (firstCoordinate J).rangeRestrict_surjective hgenH
  have hsq : ∀ y : Multiplicative K, y ^ 2 = 1 := fun y => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  have hVcard : Nat.card (firstCoordinate J).range ≤ 2 ^ 4 := by
    have h := SectionalTwoRankLE.card_le_of_elementary hgenV ⊤
      ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (mul_comm _ _))⟩⟩,
        fun x _ => Subtype.ext (hsq (x : Multiplicative K))⟩
    rwa [Subgroup.card_top] at h
  have h2 : 2 ^ (f * 2) ≤ 2 ^ 4 := by
    rw [pow_mul]
    exact hV.trans hVcard
  have h3 := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h2
  omega

theorem false_of_mulEquiv_psu3Model {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* PSU3Model n) (hrank : 3 ≤ CFSG.Open.twoRank G) (hgen : Gen4 G) : False := by
  classical
  let J := binaryQuadraticHermitian n (by omega)
  have hKcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 // J.conj x = x} =
      2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e'⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hKcard hfixed
  let e'' : G ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e'.symm
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv G e''.toEquiv
  have h1 := twoRank_projectiveSpecialUnitary_le J n hn hKcard hfixed hJ
  have h2 := le_two_of_gen4_projectiveSpecialUnitary J n hn hKcard hfixed hJ
    (Gen4.of_mulEquiv e'' hgen)
  have h3 : CFSG.Open.twoRank G = CFSG.Open.twoRank (ProjectiveSpecialUnitaryMatrixGroup J) :=
    twoRank_eq_of_mulEquiv e''
  omega

end Unitary

end CFSG.GH74.Bender
