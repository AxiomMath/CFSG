module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ext
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinAux
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic
import CFSG.Quasithin.EmptyFaithful.R3cBase
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.Foundations
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Setting
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Milestones.CL_LIT_SQTK_simple_list
import CFSG.Monster.Code.Weights
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.B5Statement
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.J4Base
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate8026Base

public section

open Matrix CFSG.Open

namespace CFSG.ClassicalGroups.SpecialLinear

variable {K : Type*} [Field K] [CharP K 2] {n : ℕ}

private theorem sub_one_mul_self [Nonempty (Fin n)] {u : Matrix (Fin n) (Fin n) K}
    (hu2 : u * u = 1) : (u - 1) * (u - 1) = 0 := by
  have hu : u + u = 0 := CharTwo.add_self_eq_zero u
  have h1 : (1 : Matrix (Fin n) (Fin n) K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  calc (u - 1) * (u - 1) = u * u - u - u + 1 := by noncomm_ring
    _ = 1 - u - u + 1 := by rw [hu2]
    _ = (1 + 1) - (u + u) := by noncomm_ring
    _ = 0 := by rw [hu, h1]; simp

private theorem sub_one_ne_zero {u : Matrix (Fin n) (Fin n) K} (hu1 : u ≠ 1) :
    u - 1 ≠ 0 := fun h => hu1 (sub_eq_zero.mp h)

private theorem exists_mulVec_ne_zero {N : Matrix (Fin n) (Fin n) K} (hN : N ≠ 0) :
    ∃ v : Fin n → K, N *ᵥ v ≠ 0 := by
  by_contra h
  push Not at h
  exact hN (by
    ext i j
    simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i)

private theorem linearIndependent_pair_mulVec {N : Matrix (Fin n) (Fin n) K} (hN2 : N * N = 0)
    {v : Fin n → K} (hv : N *ᵥ v ≠ 0) : LinearIndependent K ![v, N *ᵥ v] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h := congrArg (fun x => N *ᵥ x) hab
  have h' : a • (N *ᵥ v) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_zero] at h
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec, smul_zero, add_zero] at h
    exact h
  have ha : a = 0 := by
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' hv
  subst ha
  rw [zero_smul, zero_add] at hab
  exact ⟨rfl, (smul_eq_zero.mp hab).resolve_right hv⟩

private theorem exists_linearMap_eq_zero_one {V : Type*} [AddCommGroup V] [Module K V] {v w : V}
    (h : LinearIndependent K ![v, w]) : ∃ β : V →ₗ[K] K, β v = 0 ∧ β w = 1 := by
  let f : (Fin 2 → K) →ₗ[K] V :=
    (LinearMap.proj (0 : Fin 2)).smulRight v + (LinearMap.proj (1 : Fin 2)).smulRight w
  have hf : ∀ p : Fin 2 → K, f p = p 0 • v + p 1 • w := by
    intro p
    simp [f, LinearMap.add_apply, LinearMap.smulRight_apply]
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have h0 : p 0 • v + p 1 • w = 0 := by rw [← hf p, hp]
    obtain ⟨h0', h1'⟩ := LinearIndependent.pair_iff.mp h (p 0) (p 1) h0
    funext j
    fin_cases j
    · simpa using h0'
    · simpa using h1'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let β : V →ₗ[K] K := (LinearMap.proj (1 : Fin 2)).comp g
  have hv : f (Pi.single (0 : Fin 2) 1) = v := by
    rw [hf]
    simp
  have hw : f (Pi.single (1 : Fin 2) 1) = w := by
    rw [hf]
    simp
  have h0 : g (f (Pi.single (0 : Fin 2) 1)) = Pi.single (0 : Fin 2) 1 := by
    simpa using congrArg (fun l : (Fin 2 → K) →ₗ[K] (Fin 2 → K) =>
      l (Pi.single (0 : Fin 2) 1)) hg
  have h1 : g (f (Pi.single (1 : Fin 2) 1)) = Pi.single (1 : Fin 2) 1 := by
    simpa using congrArg (fun l : (Fin 2 → K) →ₗ[K] (Fin 2 → K) =>
      l (Pi.single (1 : Fin 2) 1)) hg
  refine ⟨β, ?_, ?_⟩
  · show (g v) 1 = 0
    rw [← hv, h0]
    simp
  · show (g w) 1 = 1
    rw [← hw, h1]
    simp

private theorem transvection_mulVec (p : Fin 2 → K) :
    transvection (1 : Fin 2) 0 (1 : K) *ᵥ p = ![p 0, p 0 + p 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.mulVec, Fin.sum_univ_two]

private theorem transvection_mul_self :
    transvection (1 : Fin 2) 0 (1 : K) * transvection (1 : Fin 2) 0 (1 : K) = 1 := by
  rw [Matrix.transvection_mul_transvection_same (1 : Fin 2) 0 (by decide) (1 : K) (1 : K)]
  rw [show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, Matrix.transvection_zero]

private theorem matrix_eq_of_mulVec_eq {m : Type*} {X Y : Matrix m (Fin n) K}
    (h : ∀ x, X *ᵥ x = Y *ᵥ x) : X = Y := by
  have h' : Matrix.toLin' X = Matrix.toLin' Y := LinearMap.ext h
  exact (Matrix.toLin' (m := m) (n := Fin n)).injective h'

private def nfA (v w : Fin n → K) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun i j => ![v, w] j i

private def nfRow (β : (Fin n → K) →ₗ[K] K) : Fin n → K :=
  fun i => β fun j => if i = j then 1 else 0

private def nfB (u : Matrix (Fin n) (Fin n) K) (β : (Fin n → K) →ₗ[K] K) :
    Matrix (Fin 2) (Fin n) K :=
  Matrix.of ![nfRow β ᵥ* (u - 1), nfRow β]

private theorem exists_normalFormVectors {u : Matrix (Fin n) (Fin n) K} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : ∃ v w : Fin n → K, (u - 1) *ᵥ v = w ∧ (u - 1) *ᵥ w = 0 ∧
      LinearIndependent K ![v, w] := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu1 (Subsingleton.elim u 1)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have hN2 : (u - 1) * (u - 1) = 0 := sub_one_mul_self hu2
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero (sub_one_ne_zero hu1)
  refine ⟨v, (u - 1) *ᵥ v, rfl, ?_, linearIndependent_pair_mulVec hN2 hv⟩
  rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]

private theorem nfRow_dot (β : (Fin n → K) →ₗ[K] K) (x : Fin n → K) :
    nfRow β ⬝ᵥ x = β x := by
  rw [LinearMap.pi_apply_eq_sum_univ β x]
  simp only [dotProduct, nfRow, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem nfA_mulVec (v w : Fin n → K) (p : Fin 2 → K) :
    nfA v w *ᵥ p = p 0 • v + p 1 • w := by
  funext i
  simp [nfA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_one, mul_comm]

private theorem nfB_mulVec (u : Matrix (Fin n) (Fin n) K) (β : (Fin n → K) →ₗ[K] K)
    (y : Fin n → K) : nfB u β *ᵥ y = ![β ((u - 1) *ᵥ y), β y] := by
  funext i
  fin_cases i
  · change nfB u β 0 ⬝ᵥ y = β ((u - 1) *ᵥ y)
    rw [show nfB u β 0 = nfRow β ᵥ* (u - 1) from rfl, ← Matrix.dotProduct_mulVec, nfRow_dot]
  · change nfB u β 1 ⬝ᵥ y = β y
    rw [show nfB u β 1 = nfRow β from rfl, nfRow_dot]

private theorem nfB_mul_nfA {u : Matrix (Fin n) (Fin n) K} {v w : Fin n → K}
    {β : (Fin n → K) →ₗ[K] K} (hNv : (u - 1) *ᵥ v = w) (hNw : (u - 1) *ᵥ w = 0)
    (hβv : β v = 0) (hβw : β w = 1) : nfB u β * nfA v w = 1 := by
  apply matrix_eq_of_mulVec_eq
  intro p
  have h1 : (u - 1) *ᵥ (p 0 • v + p 1 • w) = p 0 • w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hNw, smul_zero, add_zero, hNv]
  calc (nfB u β * nfA v w) *ᵥ p = nfB u β *ᵥ (nfA v w *ᵥ p) := by rw [Matrix.mulVec_mulVec]
    _ = nfB u β *ᵥ (p 0 • v + p 1 • w) := by rw [nfA_mulVec]
    _ = ![β ((u - 1) *ᵥ (p 0 • v + p 1 • w)), β (p 0 • v + p 1 • w)] := nfB_mulVec u β _
    _ = ![p 0, p 1] := by
          rw [h1, map_smul, hβw, smul_eq_mul, mul_one, map_add, map_smul, map_smul, hβv, hβw,
            smul_zero, smul_eq_mul, mul_one, zero_add]
    _ = (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ p := by
          rw [Matrix.one_mulVec]
          funext i
          fin_cases i <;> simp

private theorem nf_u_mul_nfA {u : Matrix (Fin n) (Fin n) K} {v w : Fin n → K}
    (hNv : (u - 1) *ᵥ v = w) (hNw : (u - 1) *ᵥ w = 0) :
    u * nfA v w = nfA v w * transvection (1 : Fin 2) 0 (1 : K) := by
  have hu_eq : u = 1 + (u - 1) := by abel
  have huv : u *ᵥ v = v + w := by
    conv_lhs => rw [hu_eq]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hNv]
  have huw : u *ᵥ w = w := by
    conv_lhs => rw [hu_eq]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hNw, add_zero]
  apply matrix_eq_of_mulVec_eq
  intro p
  calc (u * nfA v w) *ᵥ p = u *ᵥ (nfA v w *ᵥ p) := by rw [Matrix.mulVec_mulVec]
    _ = u *ᵥ (p 0 • v + p 1 • w) := by rw [nfA_mulVec]
    _ = p 0 • (v + w) + p 1 • w := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, huv, huw]
    _ = p 0 • v + (p 0 + p 1) • w := by rw [smul_add, add_smul]; abel
    _ = ![p 0, p 0 + p 1] 0 • v + ![p 0, p 0 + p 1] 1 • w := by simp
    _ = nfA v w *ᵥ ![p 0, p 0 + p 1] := (nfA_mulVec v w ![p 0, p 0 + p 1]).symm
    _ = nfA v w *ᵥ (transvection (1 : Fin 2) 0 (1 : K) *ᵥ p) := by rw [transvection_mulVec]
    _ = (nfA v w * transvection (1 : Fin 2) 0 (1 : K)) *ᵥ p := by rw [Matrix.mulVec_mulVec]

private theorem nf_nfB_mul_u {u : Matrix (Fin n) (Fin n) K} {β : (Fin n → K) →ₗ[K] K}
    (hNu : (u - 1) * u = u - 1) :
    nfB u β * u = transvection (1 : Fin 2) 0 (1 : K) * nfB u β := by
  have hu_eq : u = 1 + (u - 1) := by abel
  have hu_add : ∀ x, u *ᵥ x = x + (u - 1) *ᵥ x := by
    intro x
    conv_lhs => rw [hu_eq]
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
  apply matrix_eq_of_mulVec_eq
  intro x
  have h1 : (u - 1) *ᵥ (u *ᵥ x) = (u - 1) *ᵥ x := by rw [Matrix.mulVec_mulVec, hNu]
  calc (nfB u β * u) *ᵥ x = nfB u β *ᵥ (u *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = ![β ((u - 1) *ᵥ (u *ᵥ x)), β (u *ᵥ x)] := nfB_mulVec u β _
    _ = ![β ((u - 1) *ᵥ x), β (x + (u - 1) *ᵥ x)] := by rw [h1, hu_add]
    _ = ![β ((u - 1) *ᵥ x), β x + β ((u - 1) *ᵥ x)] := by rw [map_add]
    _ = transvection (1 : Fin 2) 0 (1 : K) *ᵥ ![β ((u - 1) *ᵥ x), β x] := by
          rw [transvection_mulVec]
          funext i
          fin_cases i <;> simp [add_comm]
    _ = (transvection (1 : Fin 2) 0 (1 : K) * nfB u β) *ᵥ x := by
          rw [← Matrix.mulVec_mulVec, nfB_mulVec u β x]

private theorem sub_one_mul_self_eq [Nonempty (Fin n)] {u : Matrix (Fin n) (Fin n) K}
    (hu2 : u * u = 1) : (u - 1) * u = u - 1 := by
  rw [sub_mul, one_mul, hu2, CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]

theorem exists_mul_eq_mul_of_mul_self_eq_one {K : Type*} [Field K] [CharP K 2] {n : ℕ}
    {u : Matrix (Fin n) (Fin n) K} (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ (A : Matrix (Fin n) (Fin 2) K) (B : Matrix (Fin 2) (Fin n) K), B * A = 1 ∧
      u * A = A * transvection (1 : Fin 2) 0 (1 : K) ∧
        B * u = transvection (1 : Fin 2) 0 (1 : K) * B := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu1 (Subsingleton.elim u 1)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨v, w, hNv, hNw, hli⟩ := exists_normalFormVectors hu2 hu1
  obtain ⟨β, hβv, hβw⟩ := exists_linearMap_eq_zero_one (K := K) hli
  exact ⟨nfA v w, nfB u β, nfB_mul_nfA hNv hNw hβv hβw,
    nf_u_mul_nfA hNv hNw, nf_nfB_mul_u (sub_one_mul_self_eq hu2)⟩

section SL2

private theorem ne_one_of_conj_eq_inv {K : Type} [Field K] [Finite K] [CharP K 2]
    {g t : SpecialLinearGroup (Fin 2) K} (htg : t * g * t = g⁻¹)
    (hg : orderOf g = Nat.card K + 1) : t ≠ 1 := by
  intro h
  have hg2 : g * g = 1 := by
    have h' : g = g⁻¹ := by simpa [h] using htg
    calc g * g = g * g⁻¹ := congrArg (fun x => g * x) h'
      _ = 1 := mul_inv_cancel g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
  rw [hg] at hdvd
  have hle : Nat.card K + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  omega

private theorem det_conj {A B : Matrix (Fin 2) (Fin 2) K} (hBA : B * A = 1)
    (g : SpecialLinearGroup (Fin 2) K) : (B * (g : Matrix (Fin 2) (Fin 2) K) * A).det = 1 := by
  have hBAdet : B.det * A.det = 1 := by rw [← Matrix.det_mul, hBA, Matrix.det_one]
  calc (B * (g : Matrix (Fin 2) (Fin 2) K) * A).det
      = B.det * (g : Matrix (Fin 2) (Fin 2) K).det * A.det := by
        rw [Matrix.det_mul, Matrix.det_mul]
    _ = B.det * A.det := by rw [g.2, mul_one]
    _ = 1 := hBAdet

private theorem orderOf_conj {A B : Matrix (Fin 2) (Fin 2) K} (hBA : B * A = 1)
    (hAB : A * B = 1) {S : SpecialLinearGroup (Fin 2) K} (g : SpecialLinearGroup (Fin 2) K)
    (hS : (S : Matrix (Fin 2) (Fin 2) K) = B * (g : Matrix (Fin 2) (Fin 2) K) * A) :
    orderOf S = orderOf g := by
  let P : (Matrix (Fin 2) (Fin 2) K)ˣ := ⟨A, B, hAB, hBA⟩
  have hSconj : Matrix.SpecialLinearGroup.toGL S =
      P⁻¹ * Matrix.SpecialLinearGroup.toGL g * P := by
    apply Units.ext
    show (S : Matrix (Fin 2) (Fin 2) K) = B * (g : Matrix (Fin 2) (Fin 2) K) * A
    exact hS
  calc orderOf S = orderOf (Matrix.SpecialLinearGroup.toGL S) :=
        (orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective S).symm
    _ = orderOf (Matrix.SpecialLinearGroup.toGL g) := by
        rw [hSconj]
        exact (SemiconjBy.orderOf_eq (P⁻¹) (by simp [SemiconjBy, mul_assoc])).symm
    _ = orderOf g := orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective g

private theorem mul_conj_inv {A B : Matrix (Fin 2) (Fin 2) K} (hBA : B * A = 1)
    (hAB : A * B = 1) (g : SpecialLinearGroup (Fin 2) K) :
    (B * (g : Matrix (Fin 2) (Fin 2) K) * A) *
      (B * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A) = 1 := by
  have hgg : (g : Matrix (Fin 2) (Fin 2) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc B * (g : Matrix (Fin 2) (Fin 2) K) * A *
        (B * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A)
      = B * (g : Matrix (Fin 2) (Fin 2) K) * (A * B) *
          ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A := by
        noncomm_ring
    _ = B * (g : Matrix (Fin 2) (Fin 2) K) *
          ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A := by
        rw [hAB, Matrix.mul_one]
    _ = B * A := by
        rw [Matrix.mul_assoc B ((g : Matrix (Fin 2) (Fin 2) K))
          (((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)), hgg,
          Matrix.mul_one]
    _ = 1 := hBA

private theorem transvection_conj {A B : Matrix (Fin 2) (Fin 2) K}
    {t g : SpecialLinearGroup (Fin 2) K} (htg : t * g * t = g⁻¹)
    (htA : (t : Matrix (Fin 2) (Fin 2) K) * A = A * transvection (1 : Fin 2) 0 (1 : K))
    (hBt : B * (t : Matrix (Fin 2) (Fin 2) K) = transvection (1 : Fin 2) 0 (1 : K) * B) :
    transvection (1 : Fin 2) 0 (1 : K) * (B * (g : Matrix (Fin 2) (Fin 2) K) * A) *
        transvection (1 : Fin 2) 0 (1 : K) =
      B * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A := by
  have hTB : transvection (1 : Fin 2) 0 (1 : K) * B =
      B * (t : Matrix (Fin 2) (Fin 2) K) := hBt.symm
  have hAT : A * transvection (1 : Fin 2) 0 (1 : K) =
      (t : Matrix (Fin 2) (Fin 2) K) * A := htA.symm
  have htgt : (t : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
      (t : Matrix (Fin 2) (Fin 2) K) =
      ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    simpa using congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K)) htg
  calc transvection (1 : Fin 2) 0 (1 : K) *
        (B * (g : Matrix (Fin 2) (Fin 2) K) * A) * transvection (1 : Fin 2) 0 (1 : K)
      = (transvection (1 : Fin 2) 0 (1 : K) * B) * (g : Matrix (Fin 2) (Fin 2) K) *
          (A * transvection (1 : Fin 2) 0 (1 : K)) := by noncomm_ring
    _ = (B * (t : Matrix (Fin 2) (Fin 2) K)) * (g : Matrix (Fin 2) (Fin 2) K) *
          ((t : Matrix (Fin 2) (Fin 2) K) * A) := by rw [hTB, hAT]
    _ = B * ((t : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
          (t : Matrix (Fin 2) (Fin 2) K)) * A := by noncomm_ring
    _ = B * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A := by
        rw [htgt]

theorem exists_orderOf_eq_card_add_one_conj_eq_inv {K : Type} [Field K] [Finite K]
    [CharP K 2] :
    ∃ S : SpecialLinearGroup (Fin 2) K, orderOf S = Nat.card K + 1 ∧
      transvection (1 : Fin 2) 0 (1 : K) * (S : Matrix (Fin 2) (Fin 2) K) *
          transvection (1 : Fin 2) 0 (1 : K) =
        ((S⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  obtain ⟨t, ht2, htg⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv g
  have htmat2 : (t : Matrix (Fin 2) (Fin 2) K) * (t : Matrix (Fin 2) (Fin 2) K) = 1 := by
    simpa using congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K)) ht2
  have htmat1 : (t : Matrix (Fin 2) (Fin 2) K) ≠ 1 :=
    fun h => ne_one_of_conj_eq_inv htg hg (Subtype.ext h)
  obtain ⟨A, B, hBA, htA, hBt⟩ := exists_mul_eq_mul_of_mul_self_eq_one htmat2 htmat1
  have hAB : A * B = 1 := mul_eq_one_comm.mp hBA
  let S : SpecialLinearGroup (Fin 2) K :=
    ⟨B * (g : Matrix (Fin 2) (Fin 2) K) * A, det_conj hBA g⟩
  have hScoe : (S : Matrix (Fin 2) (Fin 2) K) = B * (g : Matrix (Fin 2) (Fin 2) K) * A := rfl
  let S' : SpecialLinearGroup (Fin 2) K :=
    ⟨B * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A,
      det_conj hBA (g⁻¹)⟩
  refine ⟨S, ?_, ?_⟩
  · rw [orderOf_conj hBA hAB g hScoe, hg]
  have hmulS : S * S' = 1 := by
    apply Subtype.ext
    change (S : Matrix (Fin 2) (Fin 2) K) * (S' : Matrix (Fin 2) (Fin 2) K) = 1
    rw [hScoe]
    exact mul_conj_inv hBA hAB g
  rw [transvection_conj htg htA hBt]
  exact (congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K)) (inv_eq_of_mul_eq_one_right hmulS)).symm

end SL2

section GLn

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

private theorem embedMat_conj {u : Matrix (Fin n) (Fin n) K} {A : Matrix (Fin n) (Fin 2) K}
    {B : Matrix (Fin 2) (Fin n) K} (hU2 : u * u = 1)
    (hUA : u * A = A * transvection (1 : Fin 2) 0 (1 : K))
    (hBu : B * u = transvection (1 : Fin 2) 0 (1 : K) * B)
    (g : Matrix (Fin 2) (Fin 2) K) :
    u * embedMat A B g * u = embedMat A B (transvection (1 : Fin 2) 0 (1 : K) * g *
      transvection (1 : Fin 2) 0 (1 : K)) := by
  have hTg : transvection (1 : Fin 2) 0 (1 : K) * (g - 1) *
      transvection (1 : Fin 2) 0 (1 : K) =
      transvection (1 : Fin 2) 0 (1 : K) * g * transvection (1 : Fin 2) 0 (1 : K) - 1 := by
    calc transvection (1 : Fin 2) 0 (1 : K) * (g - 1) *
          transvection (1 : Fin 2) 0 (1 : K)
        = transvection (1 : Fin 2) 0 (1 : K) * g * transvection (1 : Fin 2) 0 (1 : K) -
            transvection (1 : Fin 2) 0 (1 : K) * transvection (1 : Fin 2) 0 (1 : K) := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = transvection (1 : Fin 2) 0 (1 : K) * g * transvection (1 : Fin 2) 0 (1 : K) - 1 := by
          rw [transvection_mul_self]
  calc u * embedMat A B g * u
      = u * (1 + A * (g - 1) * B) * u := by rw [embedMat]
    _ = (u + u * (A * (g - 1) * B)) * u := by rw [Matrix.mul_add, Matrix.mul_one]
    _ = u * u + (u * (A * (g - 1) * B)) * u := by rw [Matrix.add_mul]
    _ = u * u + (u * A) * (g - 1) * (B * u) := by
        rw [← Matrix.mul_assoc u (A * (g - 1)) B,
          ← Matrix.mul_assoc u A (g - 1),
          Matrix.mul_assoc ((u * A) * (g - 1)) B u]
    _ = 1 + (A * transvection (1 : Fin 2) 0 (1 : K)) * (g - 1) *
          (transvection (1 : Fin 2) 0 (1 : K) * B) := by rw [hU2, hUA, hBu]
    _ = 1 + A * (transvection (1 : Fin 2) 0 (1 : K) * (g - 1) *
          transvection (1 : Fin 2) 0 (1 : K)) * B := by
        rw [Matrix.mul_assoc A (transvection (1 : Fin 2) 0 (1 : K)) (g - 1),
          Matrix.mul_assoc A (transvection (1 : Fin 2) 0 (1 : K) * (g - 1))
            (transvection (1 : Fin 2) 0 (1 : K) * B),
          ← Matrix.mul_assoc (transvection (1 : Fin 2) 0 (1 : K) * (g - 1))
            (transvection (1 : Fin 2) 0 (1 : K)) B,
          ← Matrix.mul_assoc A ((transvection (1 : Fin 2) 0 (1 : K) * (g - 1)) *
            transvection (1 : Fin 2) 0 (1 : K)) B]
    _ = 1 + A * (transvection (1 : Fin 2) 0 (1 : K) * g *
          transvection (1 : Fin 2) 0 (1 : K) - 1) * B := by rw [hTg]
    _ = embedMat A B (transvection (1 : Fin 2) 0 (1 : K) * g *
          transvection (1 : Fin 2) 0 (1 : K)) := by rw [embedMat]

theorem exists_inv_conj_of_sq_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {u : GL (Fin n) K} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ s ∈ StatedSL n K, orderOf s = Nat.card K + 1 ∧ u⁻¹ * s * u = s⁻¹ := by
  have hu2' : u * u = 1 := by rwa [pow_two] at hu2
  have hU2 : (u : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hu2'
  have hU1 : (u : Matrix (Fin n) (Fin n) K) ≠ 1 := fun h => hu1 (Units.ext h)
  obtain ⟨A, B, hBA, hUA, hBu⟩ := exists_mul_eq_mul_of_mul_self_eq_one hU2 hU1
  obtain ⟨S, hSorder, hSinv⟩ := exists_orderOf_eq_card_add_one_conj_eq_inv (K := K)
  have hkey := embedMat_conj hU2 hUA hBu (S : Matrix (Fin 2) (Fin 2) K)
  let s : GL (Fin n) K := Matrix.SpecialLinearGroup.toGL (embedHom hBA S)
  have hs : s ∈ StatedSL n K := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL, MonoidHom.mem_range]
    exact ⟨embedHom hBA S, rfl⟩
  have horder : orderOf s = Nat.card K + 1 := by
    rw [← hSorder]
    exact orderOf_injective (Matrix.SpecialLinearGroup.toGL.comp (embedHom hBA))
      (Matrix.SpecialLinearGroup.toGL_injective.comp (embedHom_injective hBA)) S
  have hmul : embedMat A B (S : Matrix (Fin 2) (Fin 2) K) *
      embedMat A B (((S⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← embedMat_mul hBA, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, embedMat_one]
  have hrel_mat : (u : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) *
      (u : Matrix (Fin n) (Fin n) K) = ((s : Matrix (Fin n) (Fin n) K))⁻¹ := by
    have hscoe : (s : Matrix (Fin n) (Fin n) K) =
        embedMat A B (S : Matrix (Fin 2) (Fin 2) K) := rfl
    rw [hscoe, hkey, hSinv]
    exact (Matrix.inv_eq_right_inv hmul).symm
  have hu_inv : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, hu2']
  have hrel : u⁻¹ * s * u = s⁻¹ := by
    rw [hu_inv]
    apply Units.ext
    simpa using hrel_mat
  exact ⟨s, hs, horder, hrel⟩

end GLn

section PSL

private theorem nonempty_fin_of_orderOf_eq_two {K : Type} [Field K] {n : ℕ}
    {d : StatedProj (StatedSL n K)} (hd : orderOf d = 2) : Nonempty (Fin n) := by
  by_contra h
  have hn : n = 0 := by
    by_contra hn
    exact h ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  subst hn
  have h1 : d = 1 := Subsingleton.elim d 1
  rw [h1, orderOf_one] at hd
  omega

private theorem pow_eq_one_of_mem_scalars {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} [Nonempty (Fin n)] {S : GL (Fin n) K} (hord : orderOf S = Nat.card K + 1) {k : ℕ}
    (hk : S ^ k ∈ StatedScalars (Fin n) K) : S ^ k = 1 := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hk
  have h1 : (S ^ k) ^ (Nat.card K + 1) = 1 := by
    rw [← pow_mul, mul_comm k (Nat.card K + 1), pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
  rw [← hc] at h1
  have h2 : c ^ (Nat.card K + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h1
    rw [Units.val_pow_eq_pow_val, Units.val_one, Matrix.GeneralLinearGroup.coe_scalar,
      ← map_pow] at h
    have h' := congrFun (congrFun h (Classical.arbitrary (Fin n))) (Classical.arbitrary (Fin n))
    simpa [Matrix.scalar_apply] using h'
  have h3 : c ^ (Nat.card K - 1) = 1 := by
    have h := pow_card_eq_one' (x := c)
    rwa [Nat.card_units] at h
  have hq : Nat.card K + 1 = Nat.card K - 1 + 2 := by
    have h2 := Finite.one_lt_card (α := K)
    omega
  have h4 : c ^ 2 = 1 := by
    have h := h2
    rw [hq, pow_add, h3, one_mul] at h
    exact h
  have h5 : c = 1 := by
    have hcK : ((c : K)) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
    rcases sq_eq_one_iff.mp hcK with h | h
    · exact Units.ext h
    · exact Units.ext (by rw [h, CharTwo.neg_eq]; rfl)
  rw [← hc, h5, map_one]

private theorem exists_lift_of_orderOf_eq_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {d : StatedProj (StatedSL n K)} (hd : orderOf d = 2) : ∃ u : StatedSL n K,
      u * u = 1 ∧ (u : GL (Fin n) K) ≠ 1 ∧ QuotientGroup.mk u = d := by
  let e := CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv n K
  let t : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K := e d
  have ht2 : t * t = 1 := by
    have h : orderOf t = 2 := by rw [show orderOf t = orderOf d from e.orderOf_eq d, hd]
    simpa [h, pow_two] using pow_orderOf_eq_one t
  obtain ⟨s, hs, hs2⟩ := CFSG.ComponentClassification.OutcomeLocal.exists_sl_lift t ht2
  let u : StatedSL n K := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K s
  have hu2 : u * u = 1 := by
    change CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K s *
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K s = 1
    rw [← map_mul, hs2, map_one]
  have hmk : QuotientGroup.mk u = d := by
    apply e.injective
    rw [CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv_mk]
    exact hs
  have hu1 : (u : GL (Fin n) K) ≠ 1 := by
    intro h
    have hu : u = 1 := Subtype.ext h
    have hd1 : d = 1 := by rw [← hmk, hu]; rfl
    rw [hd1, orderOf_one] at hd
    omega
  exact ⟨u, hu2, hu1, hmk⟩

theorem exists_inv_conj_statedProj_statedSL {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {d : StatedProj (StatedSL n K)} (hd : orderOf d = 2) :
    ∃ τ : StatedProj (StatedSL n K), orderOf τ = Nat.card K + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  haveI : Nonempty (Fin n) := nonempty_fin_of_orderOf_eq_two hd
  obtain ⟨u, hu2, hu1, hmk⟩ := exists_lift_of_orderOf_eq_two hd
  have huGL2 : ((u : GL (Fin n) K)) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg (fun x : StatedSL n K => (x : GL (Fin n) K)) hu2
  obtain ⟨S, hS, hSorder, hSrel⟩ :=
    exists_inv_conj_of_sq_eq_one (u := (u : GL (Fin n) K)) huGL2 hu1
  let S' : StatedSL n K := ⟨S, hS⟩
  let τ : StatedProj (StatedSL n K) := QuotientGroup.mk S'
  refine ⟨τ, ?_, ?_⟩
  · apply CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.orderOf_mk_eq S' (Nat.card K + 1)
    intro k
    rw [show ((S' : StatedSL n K) : GL (Fin n) K) = S from rfl]
    constructor
    · intro hk
      rw [← hSorder]
      exact orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_scalars hSorder hk)
    · intro hk
      have h1 : S ^ k = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hSorder]
        exact hk
      rw [h1]
      exact Subgroup.one_mem _
  · have hSL : u⁻¹ * S' * u = S'⁻¹ := by
      apply Subtype.ext
      simpa using hSrel
    have h := congrArg (QuotientGroup.mk'
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))) hSL
    simpa [τ, hmk, map_mul, map_inv] using h

end PSL

section LieModel

theorem exists_inv_conj_of_lieModel_psl_of_orderOf_eq_two {Y : Type} [Group Y] {m x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSL m 2 x) {d : Y} (hd : orderOf d = 2) :
    ∃ τ : Y, orderOf τ = 2 ^ x + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hKcard
  have hd' : orderOf (e d) = 2 := by rw [MulEquiv.orderOf_eq, hd]
  obtain ⟨τ, hτ, hrel⟩ := exists_inv_conj_statedProj_statedSL (d := e d) hd'
  refine ⟨e.symm τ, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hτ, hKcard]
  · have h' := congrArg e.symm hrel
    simpa using h'

end LieModel

end CFSG.ClassicalGroups.SpecialLinear

