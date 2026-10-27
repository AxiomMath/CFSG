module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem scalar_mem_primeFormUnitary (h : UnitaryFieldData ℓ f K) (C : Matrix (Fin n) (Fin n) K)
    {δ : Kˣ} (hδ : h.norm (δ : K) = 1) :
    GeneralLinearGroup.scalar (Fin n) δ ∈ primeFormUnitary h C := by
  rw [mem_primeFormUnitary]
  have hb : (δ : K) * h.bar (δ : K) = 1 := hδ
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_map (map_zero h.bar),
    diagonal_transpose, ← smul_one_eq_diagonal, ← smul_one_eq_diagonal, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hb, one_smul]

theorem primeFormConjHom_scalar_eq_one (h : UnitaryFieldData ℓ f K)
    (C : Matrix (Fin n) (Fin n) K) {δ : Kˣ} (hδ : h.norm (δ : K) = 1) :
    primeFormConjHom h C ⟨GeneralLinearGroup.scalar (Fin n) δ,
      scalar_mem_primeFormUnitary h C hδ⟩ = 1 := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change GeneralLinearGroup.scalar (Fin n) δ * (g : GL (Fin n) K) *
    (GeneralLinearGroup.scalar (Fin n) δ)⁻¹ = g
  rw [← (commute_scalar δ (g : GL (Fin n) K)).eq, mul_inv_cancel_right]

theorem mem_inner_of_pow_eq_one_unitary (h : UnitaryFieldData ℓ f K) (C : GL (Fin n) K)
    {p : ℕ} (hp : p.Prime) (hpg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {x : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hx : x ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K)) (hxp : x ^ p = 1) :
    x ∈ Inn (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  classical
  have hIN : (Inn (primeFormP h (C : Matrix (Fin n) (Fin n) K))).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  let Q := primeFormD h (C : Matrix (Fin n) (Fin n) K) ⧸
    (Inn (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf
      (primeFormD h (C : Matrix (Fin n) (Fin n) K))
  let y : Q := QuotientGroup.mk ⟨x, hx⟩
  have hpow : ∀ k : ℕ, y ^ k = 1 ↔ x ^ k ∈ Inn (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
    intro k
    change (QuotientGroup.mk ⟨x, hx⟩ : Q) ^ k = 1 ↔ _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hy1 : y ^ p = 1 := (hpow p).2 (by rw [hxp]; exact one_mem _)
  have hy2 : y ^ (ℓ ^ f + 1) = 1 := by
    obtain ⟨c, hc⟩ := card_primeFormD_quotient_dvd h C
    have h1 := pow_card_eq_one' (G := Q) (x := y)
    rw [hc, pow_mul, h1, one_pow]
  have hy3 : y ^ n = 1 := by
    rw [hpow]
    obtain ⟨A, hA⟩ := hx
    rw [← hA]
    set δ : Kˣ := GeneralLinearGroup.det (A : GL (Fin n) K) with hδdef
    have hδ : h.norm (δ : K) = 1 := norm_det_eq_one h C A.2
    let Z : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) :=
      ⟨GeneralLinearGroup.scalar (Fin n) δ, scalar_mem_primeFormUnitary h _ hδ⟩
    set s : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := A ^ n * Z⁻¹ with hs
    have hsdet : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      have h1 : (s : GL (Fin n) K) = (A : GL (Fin n) K) ^ n *
          (GeneralLinearGroup.scalar (Fin n) δ)⁻¹ := by
        rw [hs, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
      have h2 : GeneralLinearGroup.det (s : GL (Fin n) K) = 1 := by
        rw [h1, map_mul, map_pow, map_inv, GeneralLinearGroup.det_scalar, Fintype.card_fin,
          ← hδdef, mul_inv_cancel]
      have h3 := congrArg Units.val h2
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h3
    have hsSU : (s : GL (Fin n) K) ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) :=
      (mem_gramSU_iff_unitary h).2 ⟨s.2, hsdet⟩
    have hAn : A ^ n = s * Z := by rw [hs, inv_mul_cancel_right]
    have hZ1 : primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) Z = 1 :=
      primeFormConjHom_scalar_eq_one h _ hδ
    rw [← map_pow, hAn, map_mul, hZ1, mul_one, mem_inner_primeFormP]
    exact ⟨⟨s, hsSU⟩, rfl⟩
  have hord : orderOf y ∣ Nat.gcd p (Nat.gcd n (ℓ ^ f + 1)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy1)
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one hy2))
  have hcop : Nat.gcd p (Nat.gcd n (ℓ ^ f + 1)) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hpg
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have := (hpow 1).1 (by rw [pow_one]; exact hord)
  rwa [pow_one] at this

theorem exists_inner_plane_primeFormP (h : UnitaryFieldData ℓ f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hpg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (D : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))),
      E ≤ D ∧ E ≤ innerAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∧
        IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have := h.finite
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  refine exists_plane_of_hom_cyclic hp _ hD hcard
    ((primeFormFieldFactor h hC hn hq).comp D.subtype) fun x hx => ?_
  have hxD : (x : MulAut _) ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
    rw [← ker_primeFormFieldFactor h hC hn hq]
    exact hx
  exact mem_inner_of_pow_eq_one_unitary h C hp hpg hxD (hD.2 x x.2)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
