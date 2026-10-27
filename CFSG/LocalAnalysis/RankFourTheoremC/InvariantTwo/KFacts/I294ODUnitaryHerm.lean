module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryField
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryTorus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODMono
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Polynomial Matrix CFSG.ClassicalGroups.Unitary
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid)

section Herm

variable {K : Type} [Field K] [Finite K] {r e0 p n : ℕ} [Fact r.Prime] [CharP K r]
  [hpf : Fact p.Prime] {c : K} [hirr : Fact (Irreducible (X ^ p - C c : K[X]))]

@[expose] def odBv {n : ℕ} (B : GL (Fin n) K) (s : ℤ) (y : Fin n → K) : Fin n → K :=
  ((B ^ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y

variable (p c) in
@[expose] noncomputable def odG (σ : K ≃+* K) (B : GL (Fin n) K) (x y : Fin n → K) (s : ℤ) :
    AdjoinRoot (X ^ p - C c : K[X]) :=
  algebraMap K _ (herm σ x (odBv B s y)) * (AdjoinRoot.root (X ^ p - C c : K[X])) ^ (-s)

variable (p c) in
@[expose] noncomputable def odH (σ : K ≃+* K) (B : GL (Fin n) K) (x y : Fin n → K) :
    AdjoinRoot (X ^ p - C c : K[X]) :=
  ∑ t ∈ Finset.range p, odG p c σ B x y (t : ℤ)

local notation "𝔸" => AdjoinRoot (X ^ p - C c : K[X])
local notation "β" => AdjoinRoot.root (X ^ p - C c : K[X])

variable {σ : K ≃+* K} {B : GL (Fin n) K}

theorem odBv_add (s t : ℤ) (y : Fin n → K) : odBv B (s + t) y = odBv B s (odBv B t y) := by
  simp [odBv, _root_.zpow_add, Matrix.mulVec_mulVec]

theorem odBv_zero (y : Fin n → K) : odBv B 0 y = y := by simp [odBv]

theorem odBv_one (y : Fin n → K) :
    odBv B 1 y = ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y := by
  simp [odBv]

theorem odBv_add_vec (s : ℤ) (y y' : Fin n → K) :
    odBv B s (y + y') = odBv B s y + odBv B s y' := by simp [odBv, Matrix.mulVec_add]

theorem odBv_smul (s : ℤ) (a : K) (y : Fin n → K) : odBv B s (a • y) = a • odBv B s y := by
  simp [odBv, Matrix.mulVec_smul]

theorem odBv_p (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (y : Fin n → K) : odBv B (p : ℤ) y = c • y := by
  have h1 : ((B ^ (p : ℤ) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p := by
    rw [_root_.zpow_natCast, Units.val_pow_eq_pow_val]
  rw [odBv, h1, hBp]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem odBv_herm (hB : B ∈ Uid σ n) (s : ℤ) (x y : Fin n → K) :
    herm σ (odBv B s x) (odBv B s y) = herm σ x y := (zpow_mem hB s) x y

theorem odA_root_ne_zero (hc0 : c ≠ 0) : (β : 𝔸) ≠ 0 := by
  intro h
  have h1 : (β : 𝔸) ^ p = algebraMap K 𝔸 c := odA_root_pow
  rw [h, zero_pow hpf.out.ne_zero] at h1
  exact hc0 ((map_eq_zero_iff _ (algebraMap K 𝔸).injective).1 h1.symm)

theorem odG_add_p (hc0 : c ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (x y : Fin n → K) (s : ℤ) :
    odG p c σ B x y (s + p) = odG p c σ B x y s := by
  have hβ0 := odA_root_ne_zero (p := p) hc0
  have hc' : algebraMap K 𝔸 c ≠ 0 := (map_ne_zero_iff _ (algebraMap K 𝔸).injective).2 hc0
  have hβp : (β : 𝔸) ^ (-(p : ℤ)) = (algebraMap K 𝔸 c)⁻¹ := by
    rw [_root_.zpow_neg, _root_.zpow_natCast, odA_root_pow]
  unfold odG
  rw [odBv_add, odBv_p hBp, odBv_smul, herm_smul_right, map_mul, neg_add, _root_.zpow_add₀ hβ0,
    hβp]
  field_simp

theorem odG_period (hc0 : c ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (x y : Fin n → K) :
    odG p c σ B x y (p : ℤ) = odG p c σ B x y 0 := by
  simpa using odG_add_p (σ := σ) hc0 hBp x y 0

theorem odH_B_right (hc0 : c ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (x y : Fin n → K) :
    odH p c σ B x (odBv B 1 y) = β * odH p c σ B x y := by
  have hβ0 := odA_root_ne_zero (p := p) hc0
  have h1 : ∀ s : ℤ, odG p c σ B x (odBv B 1 y) s = β * odG p c σ B x y (s + 1) := by
    intro s
    unfold odG
    rw [← odBv_add, show -s = -(s + 1) + 1 by ring, _root_.zpow_add₀ hβ0, _root_.zpow_one]
    ring
  unfold odH
  simp_rw [h1]
  have h2 := sum_range_succ_of_periodic (fun t : ℕ => odG p c σ B x y (t : ℤ)) p
    (by simpa using odG_period (σ := σ) hc0 hBp x y)
  simp only [Nat.cast_add, Nat.cast_one] at h2
  rw [← Finset.mul_sum, h2]

theorem odH_B_left (hB : B ∈ Uid σ n) (hc0 : c ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (x y : Fin n → K) :
    odH p c σ B (odBv B 1 x) y = β⁻¹ * odH p c σ B x y := by
  have hβ0 := odA_root_ne_zero (p := p) hc0
  have h1 : ∀ s : ℤ, odG p c σ B (odBv B 1 x) y s = β⁻¹ * odG p c σ B x y (s - 1) := by
    intro s
    unfold odG
    have h2 : odBv B s y = odBv B 1 (odBv B (s - 1) y) := by
      rw [← odBv_add]; congr 1; ring
    rw [h2, odBv_herm hB, show -s = -(s - 1) + (-1) by ring, _root_.zpow_add₀ hβ0,
      _root_.zpow_neg_one]
    ring
  unfold odH
  simp_rw [h1]
  have h3 := sum_range_succ_of_periodic (fun t : ℕ => odG p c σ B x y ((t : ℤ) - 1)) p (by
    have h4 := odG_add_p (σ := σ) hc0 hBp x y (-1)
    have h5 : (p : ℤ) - 1 = -1 + p := by ring
    simp only [Nat.cast_zero, zero_sub]
    rw [h5]
    exact h4)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h3
  rw [← Finset.mul_sum, ← h3]

theorem odG_add_left (x x' y : Fin n → K) (s : ℤ) :
    odG p c σ B (x + x') y s = odG p c σ B x y s + odG p c σ B x' y s := by
  unfold odG
  rw [herm_add_left, map_add, add_mul]

theorem odG_add_right (x y y' : Fin n → K) (s : ℤ) :
    odG p c σ B x (y + y') s = odG p c σ B x y s + odG p c σ B x y' s := by
  unfold odG
  rw [odBv_add_vec, herm_add_right, map_add, add_mul]

theorem odG_smul_left (a : K) (x y : Fin n → K) (s : ℤ) :
    odG p c σ B (a • x) y s = algebraMap K 𝔸 (σ a) * odG p c σ B x y s := by
  unfold odG
  rw [herm_smul_left, map_mul, mul_assoc]

theorem odG_smul_right (a : K) (x y : Fin n → K) (s : ℤ) :
    odG p c σ B x (a • y) s = algebraMap K 𝔸 a * odG p c σ B x y s := by
  unfold odG
  rw [odBv_smul, herm_smul_right, map_mul, mul_assoc]

theorem odH_add_left (x x' y : Fin n → K) :
    odH p c σ B (x + x') y = odH p c σ B x y + odH p c σ B x' y := by
  unfold odH
  simp_rw [odG_add_left]
  rw [Finset.sum_add_distrib]

theorem odH_add_right (x y y' : Fin n → K) :
    odH p c σ B x (y + y') = odH p c σ B x y + odH p c σ B x y' := by
  unfold odH
  simp_rw [odG_add_right]
  rw [Finset.sum_add_distrib]

theorem odH_smul_left (a : K) (x y : Fin n → K) :
    odH p c σ B (a • x) y = algebraMap K 𝔸 (σ a) * odH p c σ B x y := by
  unfold odH
  simp_rw [odG_smul_left]
  rw [← Finset.mul_sum]

theorem odH_smul_right (a : K) (x y : Fin n → K) :
    odH p c σ B x (a • y) = algebraMap K 𝔸 a * odH p c σ B x y := by
  unfold odH
  simp_rw [odG_smul_right]
  rw [← Finset.mul_sum]

theorem odH_pow_right (hc0 : c ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (x y : Fin n → K) (t : ℕ) :
    odH p c σ B x (odBv B (t : ℤ) y) = β ^ t * odH p c σ B x y := by
  induction t with
  | zero => simp [odBv_zero]
  | succ t ih =>
    have h1 : odBv B ((t + 1 : ℕ) : ℤ) y = odBv B 1 (odBv B (t : ℤ) y) := by
      rw [← odBv_add]; congr 1; push_cast; ring
    rw [h1, odH_B_right hc0 hBp, ih, pow_succ, mul_comm (β ^ t) β, mul_assoc]

theorem odH_pow_left (hB : B ∈ Uid σ n) (hc0 : c ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c)
    (x y : Fin n → K) (t : ℕ) :
    odH p c σ B (odBv B (t : ℤ) x) y = (β⁻¹) ^ t * odH p c σ B x y := by
  induction t with
  | zero => simp [odBv_zero]
  | succ t ih =>
    have h1 : odBv B ((t + 1 : ℕ) : ℤ) x = odBv B 1 (odBv B (t : ℤ) x) := by
      rw [← odBv_add]; congr 1; push_cast; ring
    rw [h1, odH_B_left hB hc0 hBp, ih, pow_succ, mul_comm ((β⁻¹) ^ t) β⁻¹, mul_assoc]

structure OdSetup (r e0 p : ℕ) (c : K) (σ : K ≃+* K) (B : GL (Fin n) K) : Prop where
  hB : B ∈ Uid σ n
  hc0 : c ≠ 0
  hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c
  hσq : ∀ k, σ k = k ^ (r ^ e0)
  hσσ : ∀ k, σ (σ k) = k
  hK : Nat.card K = (r ^ e0) ^ 2
  hpodd : Odd p
  hpq : p ∣ r ^ e0 + 1
  hcq : c ^ (r ^ e0 + 1) = 1

variable (p c) in
@[expose] noncomputable def odAct (M : Matrix (Fin n) (Fin n) K)
    (hM : M ^ p = Matrix.scalar (Fin n) c) :
    AdjoinRoot (X ^ p - C c : K[X]) →+* Matrix (Fin n) (Fin n) K :=
  Ideal.Quotient.lift (Ideal.span {(X ^ p - C c : K[X])}) (aeval M : K[X] →ₐ[K] _).toRingHom
    (fun a ha => by
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 ha
      change aeval M ((X ^ p - C c) * g) = 0
      have h2 : algebraMap K (Matrix (Fin n) (Fin n) K) c = Matrix.scalar (Fin n) c := by
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      have hroot : aeval M (X ^ p - C c : K[X]) = 0 := by
        simp only [map_sub, map_pow, aeval_X, aeval_C, hM, h2, sub_self]
      rw [map_mul, hroot, zero_mul])

theorem odAct_mk (M : Matrix (Fin n) (Fin n) K) (hM : M ^ p = Matrix.scalar (Fin n) c)
    (g : K[X]) : odAct p c M hM (AdjoinRoot.mk _ g) = aeval M g := rfl

theorem odAct_algebraMap (M : Matrix (Fin n) (Fin n) K) (hM : M ^ p = Matrix.scalar (Fin n) c)
    (k : K) : odAct p c M hM (algebraMap K 𝔸 k) = Matrix.scalar (Fin n) k := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, odAct_mk, aeval_C]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem odAct_root (M : Matrix (Fin n) (Fin n) K) (hM : M ^ p = Matrix.scalar (Fin n) c) :
    odAct p c M hM β = M := by
  rw [AdjoinRoot.root, odAct_mk, aeval_X]

theorem scalar_mulVec' (k : K) (v : Fin n → K) : Matrix.scalar (Fin n) k *ᵥ v = k • v := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem odBv_natCast (s : ℕ) (y : Fin n → K) :
    odBv B (s : ℤ) y = ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ s *ᵥ y := by
  rw [odBv, _root_.zpow_natCast, Units.val_pow_eq_pow_val]

theorem mk_monomial_eq (s : ℕ) (k : K) :
    AdjoinRoot.mk (X ^ p - C c : K[X]) (monomial s k) = algebraMap K 𝔸 k * β ^ s := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

theorem odH_act_left (S : OdSetup r e0 p c σ B) (a : 𝔸) (x y : Fin n → K) :
    odH p c σ B (odAct p c _ S.hBp a *ᵥ x) y = odIota K r e0 p c a * odH p c σ B x y := by
  induction a using AdjoinRoot.induction_on with
  | ih g =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 =>
      simp only [map_add, Matrix.add_mulVec, odH_add_left, h1, h2, add_mul]
    | monomial s k =>
      rw [mk_monomial_eq, map_mul, map_pow, odAct_algebraMap, odAct_root, ← Matrix.mulVec_mulVec,
        scalar_mulVec', ← odBv_natCast, odH_smul_left, odH_pow_left S.hB S.hc0 S.hBp,
        map_mul, map_pow, odIota_algebraMap S.hK S.hpodd, odIota_root S.hpodd S.hpq S.hcq,
        S.hσq, mul_assoc]

theorem odH_act_right (S : OdSetup r e0 p c σ B) (a : 𝔸) (x y : Fin n → K) :
    odH p c σ B x (odAct p c _ S.hBp a *ᵥ y) = a * odH p c σ B x y := by
  induction a using AdjoinRoot.induction_on with
  | ih g =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 =>
      simp only [map_add, Matrix.add_mulVec, odH_add_right, h1, h2, add_mul]
    | monomial s k =>
      rw [mk_monomial_eq, map_mul, map_pow, odAct_algebraMap, odAct_root, ← Matrix.mulVec_mulVec,
        scalar_mulVec', ← odBv_natCast, odH_smul_right, odH_pow_right S.hc0 S.hBp, mul_assoc]

theorem odAct_mem (S : OdSetup r e0 p c σ B) {W : Submodule K (Fin n → K)}
    (hW : ∀ x ∈ W, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W) (a : 𝔸)
    {x : Fin n → K} (hx : x ∈ W) : odAct p c _ S.hBp a *ᵥ x ∈ W := by
  induction a using AdjoinRoot.induction_on with
  | ih g =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 =>
      simp only [map_add, Matrix.add_mulVec]
      exact W.add_mem h1 h2
    | monomial s k =>
      rw [mk_monomial_eq, map_mul, map_pow, odAct_algebraMap, odAct_root, ← Matrix.mulVec_mulVec,
        scalar_mulVec']
      refine W.smul_mem k ?_
      induction s with
      | zero => simpa using hx
      | succ s ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        exact hW _ ih

variable (p c) in
@[expose] noncomputable def odPB : PowerBasis K (AdjoinRoot (X ^ p - C c : K[X])) :=
  AdjoinRoot.powerBasis ((monic_X_pow_sub_C c hpf.out.ne_zero).ne_zero)

theorem odPB_dim : (odPB p c).dim = p := by
  simp [odPB, AdjoinRoot.powerBasis, natDegree_X_pow_sub_C]

theorem odPB_gen : (odPB p c).gen = β := rfl

variable (p c) in
@[expose] noncomputable def odCoeff0 : AdjoinRoot (X ^ p - C c : K[X]) →ₗ[K] K :=
  (odPB p c).basis.coord ⟨0, (odPB p c).dim_pos⟩

theorem odCoeff0_pow (m : ℕ) (hm : m < p) :
    odCoeff0 p c ((β : 𝔸) ^ m) = if m = 0 then 1 else 0 := by
  have hm' : m < (odPB p c).dim := hm.trans_eq (odPB_dim (p := p) (c := c)).symm
  have h1 : (β : 𝔸) ^ m = (odPB p c).basis ⟨m, hm'⟩ := by
    rw [PowerBasis.basis_eq_pow, odPB_gen]
  rw [h1, odCoeff0, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

theorem odCoeff0_alg_mul (k : K) (a : 𝔸) :
    odCoeff0 p c (algebraMap K 𝔸 k * a) = k * odCoeff0 p c a := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem odCoeff0_odH (hc0 : c ≠ 0) (x y : Fin n → K) :
    odCoeff0 p c (odH p c σ B x y) = herm σ x y := by
  have hβ0 := odA_root_ne_zero (p := p) hc0
  have hβp : (β : 𝔸) ^ (-(p : ℤ)) = algebraMap K 𝔸 c⁻¹ := by
    rw [_root_.zpow_neg, _root_.zpow_natCast, odA_root_pow, map_inv₀]
  unfold odH
  rw [map_sum, Finset.sum_eq_single 0]
  · unfold odG
    simp only [Nat.cast_zero, odBv_zero, neg_zero, _root_.zpow_zero, mul_one]
    rw [← mul_one (algebraMap K 𝔸 (herm σ x y)), odCoeff0_alg_mul]
    have := odCoeff0_pow (p := p) (c := c) 0 hpf.out.pos
    simp only [pow_zero, if_true] at this
    rw [this, mul_one]
  · intro t ht ht0
    have htp := Finset.mem_range.1 ht
    have h1 : (β : 𝔸) ^ (-(t : ℤ)) = algebraMap K 𝔸 c⁻¹ * β ^ (p - t) := by
      have : -(t : ℤ) = ((p - t : ℕ) : ℤ) + (-(p : ℤ)) := by omega
      rw [this, _root_.zpow_add₀ hβ0, hβp, _root_.zpow_natCast, mul_comm]
    unfold odG
    rw [h1, ← mul_assoc, ← map_mul, odCoeff0_alg_mul, odCoeff0_pow (p - t) (by omega),
      if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hpf.out.pos) h

theorem odIota_odG (S : OdSetup r e0 p c σ B) (w : Fin n → K) (t : ℕ) :
    odIota K r e0 p c (odG p c σ B w w (t : ℤ)) = odG p c σ B w w (-(t : ℤ)) := by
  have hβ0 := odA_root_ne_zero (p := p) S.hc0
  have h1 : σ (herm σ w (odBv B (t : ℤ) w)) = herm σ w (odBv B (-(t : ℤ)) w) := by
    rw [← herm_conj σ S.hσσ, ← odBv_herm S.hB (-(t : ℤ)), ← odBv_add, neg_add_cancel, odBv_zero]
  unfold odG
  rw [map_mul, odIota_algebraMap S.hK S.hpodd, ← S.hσq, h1, map_zpow₀,
    odIota_root S.hpodd S.hpq S.hcq, _root_.inv_zpow', neg_neg]

theorem odH_self_fixed (S : OdSetup r e0 p c σ B) (w : Fin n → K) :
    odIota K r e0 p c (odH p c σ B w w) = odH p c σ B w w := by
  unfold odH
  rw [map_sum]
  simp_rw [odIota_odG S w]
  set G : ℤ → 𝔸 := odG p c σ B w w with hG
  have hper : ∀ s, G (s + p) = G s := odG_add_p S.hc0 S.hBp w w
  have h1 : ∑ t ∈ Finset.range p, G (-(t : ℤ)) =
      ∑ t ∈ Finset.range p, G (((p - 1 - t : ℕ) : ℤ) + 1) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have htp := Finset.mem_range.1 ht
    have h2 : ((p - 1 - t : ℕ) : ℤ) + 1 = -(t : ℤ) + p := by omega
    rw [h2, hper]
  rw [h1, Finset.sum_range_reflect (fun j : ℕ => G ((j : ℤ) + 1)) p]
  have h3 := sum_range_succ_of_periodic (fun t : ℕ => G (t : ℤ)) p
    (by simpa using odG_period S.hc0 S.hBp w w)
  simpa using h3

theorem od_exists_orbit (S : OdSetup r e0 p c σ B) {w : Fin n → K} (hw : herm σ w w ≠ 0) :
    ∃ e : 𝔸, ∀ i j : ℕ, i < p → j < p →
      herm σ (odBv B (i : ℤ) (odAct p c _ S.hBp e *ᵥ w))
        (odBv B (j : ℤ) (odAct p c _ S.hBp e *ᵥ w)) = if i = j then 1 else 0 := by
  set ν := odH p c σ B w w with hν
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 := odCoeff0_odH (p := p) (c := c) (σ := σ) (B := B) S.hc0 w w
    rw [← hν, h, map_zero] at h1
    exact hw h1.symm
  obtain ⟨e, he⟩ := od_exists_norm_eq S.hK hν0 (odH_self_fixed S w)
  refine ⟨e, ?_⟩
  set w' := odAct p c _ S.hBp e *ᵥ w with hw'
  have hH : odH p c σ B w' w' = 1 := by
    have h1 : odIota K r e0 p c e * (e * ν) = 1 := by rw [← mul_assoc]; exact he
    rw [hw', odH_act_left S, odH_act_right S]
    exact h1
  have h1 : ∀ t : ℕ, t < p → herm σ w' (odBv B (t : ℤ) w') = if t = 0 then 1 else 0 := by
    intro t ht
    have h2 := odCoeff0_odH (p := p) (c := c) (σ := σ) (B := B) S.hc0 w' (odBv B (t : ℤ) w')
    rw [← h2, odH_pow_right S.hc0 S.hBp, hH, mul_one, odCoeff0_pow t ht]
  have key : ∀ i j : ℕ, i ≤ j → j < p →
      herm σ (odBv B (i : ℤ) w') (odBv B (j : ℤ) w') = if i = j then 1 else 0 := by
    intro i j hij hjp
    have hjj : odBv B (j : ℤ) w' = odBv B (i : ℤ) (odBv B ((j - i : ℕ) : ℤ) w') := by
      rw [← odBv_add]; congr 1; omega
    rw [hjj, odBv_herm S.hB, h1 (j - i) (by omega)]
    by_cases hij' : i = j
    · simp [hij']
    · rw [if_neg hij', if_neg (by omega)]
  intro i j hi hj
  rcases le_total i j with hle | hle
  · exact key i j hle hj
  · by_cases hij : i = j
    · subst hij
      exact key i i le_rfl hi
    · rw [herm_conj σ S.hσσ (odBv B (j : ℤ) w') (odBv B (i : ℤ) w'),
        key j i hle hi, if_neg (Ne.symm hij), if_neg hij, map_zero]

end Herm

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
