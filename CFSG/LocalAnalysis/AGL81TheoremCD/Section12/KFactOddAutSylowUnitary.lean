module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicReduce
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization
import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredThree
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.HardMathSupport.Lang.Proving.SLTwoThreePrime
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.PGlue
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryCover

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

section
open CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.StandardType.RecipeFieldSpU

private theorem primeFormD_pow_mem_inner_of_not_dvd {K : Type} [Field K] {n f r : ℕ}
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hnq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hr : r.Prime) (hgcd : ¬ r ∣ Nat.gcd n (2 ^ f + 1))
    {δ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hδ : δ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (j : ℕ)
    (hδH : δ ^ (r ^ j) ∈ inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    δ ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  let P := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let I := inner P
  let D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let Q := D ⧸ I.subgroupOf D
  let δD : D := ⟨δ, hδ⟩
  let π : D →* Q := QuotientGroup.mk' (I.subgroupOf D)
  have hcard : Nat.card Q = Nat.gcd n (2 ^ f + 1) := by
    obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hnq
    exact hcard
  have h1 : (π δD) ^ (r ^ j) = 1 := by
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff (δD ^ (r ^ j))).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [I, P] using hδH
  have h2 : orderOf (π δD) ∣ r ^ j := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (π δD) ∣ Nat.card Q := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (r ^ j) (Nat.card Q) := by
    rw [hcard]
    exact Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hr).mpr hgcd)
  have h4 : orderOf (π δD) = 1 := by
    have hdvd : orderOf (π δD) ∣ Nat.gcd (r ^ j) (Nat.card Q) := Nat.dvd_gcd h2 h3
    rw [hcop.gcd_eq_one] at hdvd
    exact Nat.dvd_one.mp hdvd
  have h5 : (π δD : Q) = 1 := orderOf_eq_one_iff.mp h4
  have h6 : δD ∈ I.subgroupOf D := (QuotientGroup.eq_one_iff δD).mp h5
  exact Subgroup.mem_subgroupOf.mp h6

private theorem glAut_mem_hypSU {K : Type} [Field K] {f r ε : ℕ} (h : UnitaryFieldData 2 f K)
    (σ : K ≃+* K) {g : GL (HypIndex r ε) K} (hg : g ∈ hypSU h r ε) :
    glAut σ g ∈ hypSU h r ε := by
  rw [mem_hypSU] at hg ⊢
  refine ⟨?_, ?_⟩
  · have h1 := map_similitude h (A := (g : Matrix (HypIndex r ε) (HypIndex r ε) K))
      (μ := (1 : K)) (by simpa using hg.1) σ
    simpa [coe_glAut] using h1
  · rw [coe_glAut]
    have hdet := RingHom.map_det (σ : K →+* K) (g : Matrix (HypIndex r ε) (HypIndex r ε) K)
    rw [hg.2, map_one] at hdet
    exact hdet.symm

private theorem glAut_mem_hypUnitriangular {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (σ : K ≃+* K) {u : hypSU h r ε}
    (hu : u ∈ hypUnitriangular h r ε) :
    (⟨glAut σ (u : GL (HypIndex r ε) K), glAut_mem_hypSU h σ u.2⟩ : hypSU h r ε) ∈
      hypUnitriangular h r ε := by
  rw [mem_hypUnitriangular] at hu ⊢
  refine ⟨?_, ?_⟩
  · rw [coe_glAut]
    exact hu.1.map (σ : K →+* K)
  · intro a
    rw [coe_glAut, Matrix.map_apply, hu.2, map_one]

private theorem fieldToSemilinear_mem {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (σ : K ≃+* K) :
    (⟨1, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε := by
  refine ⟨1, one_ne_zero, map_one h.bar, ?_⟩
  simp

private noncomputable def fieldToSemilinear {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) : (K ≃+* K) →* semilinearSimilitudes h r ε where
  toFun σ := ⟨⟨1, σ⟩, fieldToSemilinear_mem h σ⟩
  map_one' := Subtype.ext (by
    apply SemidirectProduct.ext <;> simp)
  map_mul' σ τ := Subtype.ext (by
    apply SemidirectProduct.ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right])

private noncomputable def hypFieldAutHom {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    (K ≃+* K) →* MulAut (hypPSU h r ε) :=
  (semilinearAutHom h hr hε).comp (fieldToSemilinear h)

private noncomputable def hypFieldAut {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1) (σ : K ≃+* K) :
    MulAut (hypPSU h r ε) :=
  hypFieldAutHom h hr hε σ

private theorem hypFieldAut_apply {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1) (σ : K ≃+* K)
    (g : hypSU h r ε) :
    hypFieldAut h hr hε σ (hypProj h r ε g) =
      hypProj h r ε ⟨glAut σ (g : GL (HypIndex r ε) K), glAut_mem_hypSU h σ g.2⟩ := by
  simp only [hypFieldAut, hypFieldAutHom, MonoidHom.comp_apply, fieldToSemilinear,
    MonoidHom.coe_mk, semilinearAutHom_apply]
  congr 2
  simp

private theorem hypFieldAut_pow_orderOf {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1) (σ : K ≃+* K) :
    hypFieldAut h hr hε σ ^ orderOf σ = 1 := by
  change (hypFieldAutHom h hr hε) σ ^ orderOf σ = 1
  rw [← map_pow, pow_orderOf_eq_one, map_one]

private theorem map_hypProjUnitriangular_hypFieldAut {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1) (σ : K ≃+* K) :
    (hypProjUnitriangular h r ε).map (hypFieldAut h hr hε σ).toMonoidHom =
      hypProjUnitriangular h r ε := by
  let U := hypProjUnitriangular h r ε
  let F := hypFieldAut h hr hε σ
  have hle_all : ∀ τ : K ≃+* K,
      U.map (hypFieldAut h hr hε τ).toMonoidHom ≤ U := by
    intro τ
    rintro x ⟨y, hy, rfl⟩
    change y ∈ (hypUnitriangular h r ε).map (hypProj h r ε) at hy
    rcases hy with ⟨u, hu, rfl⟩
    refine ⟨⟨glAut τ (u : GL (HypIndex r ε) K), glAut_mem_hypSU h τ u.2⟩,
      glAut_mem_hypUnitriangular h τ hu, ?_⟩
    exact (hypFieldAut_apply h hr hε τ u).symm
  have hFinv : F⁻¹ = hypFieldAut h hr hε σ⁻¹ := by
    show (hypFieldAutHom h hr hε σ)⁻¹ = hypFieldAutHom h hr hε σ⁻¹
    rw [← map_inv]
  have hle' : U ≤ U.map F.toMonoidHom := by
    intro x hx
    have hx1 : ((F⁻¹).toMonoidHom) x ∈ U := by
      rw [hFinv]
      exact hle_all σ⁻¹ (Subgroup.mem_map_of_mem (hypFieldAut h hr hε σ⁻¹).toMonoidHom hx)
    simpa using Subgroup.mem_map_of_mem F.toMonoidHom hx1
  exact le_antisymm (hle_all σ) hle'

private theorem primeFormFieldAut_hypTransport_conj {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K)
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (σ : K ≃+* K) (g : hypSU h r ε) :
    let hC1 : IsPrimeFormGram (1 : GL (Fin (2 * r + ε)) K) := isPrimeFormGram_one
    let S : primeFormUnitary h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) :=
      ⟨semiTransportGL hR (1 : GL (HypIndex r ε) K) σ, by
        rw [mem_primeFormUnitary]
        simpa using semiTransportGL_unitary hR (B := (1 : GL (HypIndex r ε) K))
          (by simp) σ⟩
    (primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) S)
      (primeFormFieldAut h hC1 σ
        (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.suIota h (2 * r + ε)
          (hypTransport h hR g) : primeFormP h ((1 : GL (Fin (2 * r + ε)) K) :
            Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K))) =
      (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.suIota h (2 * r + ε)
        (hypTransport h hR ⟨glAut σ (g : GL (HypIndex r ε) K),
          glAut_mem_hypSU h σ g.2⟩) :
        primeFormP h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
          (Fin (2 * r + ε)) K)) := by
  intro hC1 S
  let C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K := 1
  let x : unitarySU 2 f K (2 * r + ε) := hypTransport h hR g
  let x' : unitarySU 2 f K (2 * r + ε) :=
    hypTransport h hR ⟨glAut σ (g : GL (HypIndex r ε) K), glAut_mem_hypSU h σ g.2⟩
  let y1 : gramSU h C :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.suIota h (2 * r + ε) x
  let y2 : gramSU h C :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.suIota h (2 * r + ε) x'
  let z : gramSU h C :=
    ⟨(S : GL (Fin (2 * r + ε)) K) *
        ((primeFormFieldSU h hC1 σ y1 : GL (Fin (2 * r + ε)) K)) *
        (S : GL (Fin (2 * r + ε)) K)⁻¹,
      conj_mem_gramSU h C S.2 (primeFormFieldSU h hC1 σ y1).2⟩
  have hz : (primeFormConjHom h C S)
      ((primeFormFieldSU h hC1 σ y1 : gramSU h C) : primeFormP h C) =
      (z : primeFormP h C) :=
    primeFormConjHom_mk h C S (primeFormFieldSU h hC1 σ y1)
  rw [primeFormFieldAut_mk]
  change (primeFormConjHom h C S)
      ((primeFormFieldSU h hC1 σ y1 : gramSU h C) : primeFormP h C) =
    (y2 : primeFormP h C)
  rw [hz]
  rw [show z = y2 from by
    apply Subtype.ext
    change (S : GL (Fin (2 * r + ε)) K) *
      (primeFormFieldSU h hC1 σ y1 : GL (Fin (2 * r + ε)) K) *
      (S : GL (Fin (2 * r + ε)) K)⁻¹ = (y2 : GL (Fin (2 * r + ε)) K)
    change (semiTransportGL hR (1 : GL (HypIndex r ε) K) σ) *
      (glAut σ (transportGL hR (g : GL (HypIndex r ε) K))) *
      (semiTransportGL hR (1 : GL (HypIndex r ε) K) σ)⁻¹ =
      transportGL hR (glAut σ (g : GL (HypIndex r ε) K))
    simpa using (transportGL_conj hR (1 : GL (HypIndex r ε) K) σ
      (g : GL (HypIndex r ε) K)).symm]

private theorem hypProjTransport_trans_unitaryProj {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K)
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (g : hypSU h r ε) :
    ((hypProjTransport h hR).trans (unitaryPSUEquivPrimeFormOne h (2 * r + ε)))
      (hypProj h r ε g) =
    (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.suIota h (2 * r + ε)
      (hypTransport h hR g) : primeFormP h ((1 : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) := by
  change (unitaryPSUEquivPrimeFormOne h (2 * r + ε))
    (hypProjTransport h hR (hypProj h r ε g)) = _
  rw [hypProjTransport_hypProj, CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.psi_unitaryProj]

private theorem congr_hypFieldAut_eq_primeFormConj_fieldHom {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (σ : K ≃+* K) :
    let eP := (hypProjTransport h hR).trans
      (unitaryPSUEquivPrimeFormOne h (2 * r + ε))
    let S : primeFormUnitary h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) :=
      ⟨semiTransportGL hR (1 : GL (HypIndex r ε) K) σ, by
        rw [mem_primeFormUnitary]
        simpa using semiTransportGL_unitary hR (B := (1 : GL (HypIndex r ε) K))
          (by simp) σ⟩
    MulAut.congr eP (hypFieldAut h hr hε σ) =
      primeFormConjHom h _ S * primeFormFieldHom h (isPrimeFormGram_one (n := 2 * r + ε)) σ := by
  intro eP S
  let hC1 : IsPrimeFormGram (1 : GL (Fin (2 * r + ε)) K) := isPrimeFormGram_one
  apply MulEquiv.ext
  intro z
  obtain ⟨y, rfl⟩ := (unitaryPSUEquivPrimeFormOne h (2 * r + ε)).surjective z
  obtain ⟨g, hg⟩ := hypProj_surjective h r ε ((hypProjTransport h hR).symm y)
  have hy : y = hypProjTransport h hR (hypProj h r ε g) := by
    calc y = hypProjTransport h hR ((hypProjTransport h hR).symm y) :=
          (MulEquiv.apply_symm_apply (hypProjTransport h hR) y).symm
      _ = hypProjTransport h hR (hypProj h r ε g) := congrArg _ hg.symm
  rw [hy]
  let u : hypSU h r ε := ⟨glAut σ (g : GL (HypIndex r ε) K), glAut_mem_hypSU h σ g.2⟩
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change eP (hypFieldAut h hr hε σ (eP.symm (eP (hypProj h r ε g)))) = _
  rw [MulEquiv.symm_apply_apply, hypFieldAut_apply]
  change eP (hypProj h r ε u) =
    (primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
      (Fin (2 * r + ε)) K) S * primeFormFieldHom h hC1 σ) (eP (hypProj h r ε g))
  rw [hypProjTransport_trans_unitaryProj h hR u,
    hypProjTransport_trans_unitaryProj h hR g, MulAut.mul_apply]
  exact (primeFormFieldAut_hypTransport_conj h hR σ g).symm

private theorem exists_primeForm_conj_mul_field_of_pow {K : Type} [Field K] {f m r k : ℕ}
    (h : UnitaryFieldData 2 f K) (hm3 : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2))
    (hr : r.Prime) (hr5 : 5 ≤ r) (hgcd : ¬ r ∣ Nat.gcd m (2 ^ f + 1))
    {β : MulAut (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))}
    (hβord : orderOf β = r ^ k)
    (hβinn : Subgroup.zpowers β ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) = ⊥) :
    ∃ (φ : K ≃+* K) (A : primeFormUnitary h ((1 : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K)),
      β = primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) A *
        primeFormFieldHom h (isPrimeFormGram_one (n := m)) φ ∧
      Odd (orderOf φ) ∧
      (primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) A *
        primeFormFieldHom h (isPrimeFormGram_one (n := m)) φ) ^ orderOf φ = 1 := by
  obtain ⟨-, -, -, -, hdecomp, -, -, -, hDnormal, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (n := m)) hm3 hmq
  obtain ⟨φ, ⟨A, hβA⟩, -⟩ := hdecomp β
  have hφdvd : orderOf φ ∣ r ^ k := by
    have hfac : primeFormFieldFactor h (isPrimeFormGram_one (n := m)) hm3 hmq β = φ := by
      rw [hβA, primeFormFieldFactor_apply]
    rw [← hfac, ← hβord]
    exact orderOf_map_dvd _ _
  have hoddφ : Odd (orderOf φ) :=
    Odd.of_dvd_nat (Odd.pow (n := k) (hr.odd_of_ne_two (by omega))) hφdvd
  have hDr : ∀ δ ∈ primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K),
      ∀ j : ℕ, δ ^ (r ^ j) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) →
      δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
    intro δ hδ j hδH
    exact primeFormD_pow_mem_inner_of_not_dvd h hm3 hmq hr hgcd hδ j hδH
  have hαk : (primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) A *
      primeFormFieldHom h (isPrimeFormGram_one (n := m)) φ) ^ (r ^ k) = 1 := by
    rw [← hβA, ← hβord]
    exact pow_orderOf_eq_one β
  have hβinn' : Subgroup.zpowers (primeFormConjHom h ((1 : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) A *
      primeFormFieldHom h (isPrimeFormGram_one (n := m)) φ) ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h
        ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) = ⊥ := by
    rwa [hβA] at hβinn
  have hf_ord : orderOf (primeFormFieldHom h (isPrimeFormGram_one (n := m)) φ : MulAut
      (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))) = orderOf φ :=
    orderOf_injective _ (primeFormFieldHom_injective h hm3 hmq) φ
  have hpowβ : β ^ orderOf φ = 1 := by
    have h := pow_orderOf_eq_one_of_mul
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)))
      (D := primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) hDr
      ⟨A, rfl⟩ (fun g hg => hDnormal.conj_mem g hg _) hαk hβinn'
    rw [← hβA, hf_ord] at h
    exact h
  refine ⟨φ, A, hβA, hoddφ, ?_⟩
  rw [← hβA]
  exact hpowβ

private theorem exists_hypFieldAut_conj_of_primeForm {K : Type} [Field K] {f r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hm3 : 3 ≤ 2 * r + ε) (hmq : ¬(2 * r + ε = 3 ∧ 2 ^ f = 2))
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (α : MulAut (hypPSU h r ε)) (φ : K ≃+* K)
    (A : primeFormUnitary h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
      (Fin (2 * r + ε)) K))
    (hβA : MulAut.congr ((hypProjTransport h hR).trans
        (unitaryPSUEquivPrimeFormOne h (2 * r + ε))) α =
      primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) A *
        primeFormFieldHom h (isPrimeFormGram_one (n := 2 * r + ε)) φ)
    (hoddφ : Odd (orderOf φ))
    (hpow : (primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) A *
      primeFormFieldHom h (isPrimeFormGram_one (n := 2 * r + ε)) φ) ^ orderOf φ = 1) :
    ∃ X : MulAut (hypPSU h r ε), α = X * hypFieldAut h hr hε φ * X⁻¹ := by
  let eP := (hypProjTransport h hR).trans (unitaryPSUEquivPrimeFormOne h (2 * r + ε))
  let hC1 : IsPrimeFormGram (1 : GL (Fin (2 * r + ε)) K) := isPrimeFormGram_one
  have : NeZero (2 * r + ε) := ⟨by omega⟩
  obtain ⟨H1, hH1⟩ := primeForm_conj_of_pow_orderOf_eq_one h hm3 hmq A φ hoddφ hpow
  let S : primeFormUnitary h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
      (Fin (2 * r + ε)) K) :=
    ⟨semiTransportGL hR (1 : GL (HypIndex r ε) K) φ, by
      rw [mem_primeFormUnitary]
      simpa using semiTransportGL_unitary hR (B := (1 : GL (HypIndex r ε) K)) (by simp) φ⟩
  have htransport : MulAut.congr eP (hypFieldAut h hr hε φ) =
      primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) S *
        primeFormFieldHom h hC1 φ := by
    simpa [eP, S, hC1] using congr_hypFieldAut_eq_primeFormConj_fieldHom h hr hε hR φ
  have hpowS : (primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) S *
      primeFormFieldHom h hC1 φ) ^ orderOf φ = 1 := by
    rw [← htransport, ← map_pow, hypFieldAut_pow_orderOf, map_one]
  obtain ⟨H2, hH2⟩ := primeForm_conj_of_pow_orderOf_eq_one h hm3 hmq S φ hoddφ hpowS
  let γ : MulAut (primeFormP h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
      (Fin (2 * r + ε)) K)) :=
    primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
      (Fin (2 * r + ε)) K) H1 *
      (primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) H2)⁻¹
  have hβconj : MulAut.congr eP α = γ *
      (primeFormConjHom h ((1 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K) S *
        primeFormFieldHom h hC1 φ) * γ⁻¹ := by
    rw [hβA, hH1, hH2]
    simp only [γ]
    group
  let X : MulAut (hypPSU h r ε) := (MulAut.congr eP).symm γ
  have hX : MulAut.congr eP X = γ := (MulAut.congr eP).apply_symm_apply γ
  refine ⟨X, ?_⟩
  apply (MulAut.congr eP).injective
  rw [map_mul, map_mul, map_inv, hX]
  change MulAut.congr eP α = γ * MulAut.congr eP (hypFieldAut h hr hε φ) * γ⁻¹
  rw [hβconj, htransport]

private theorem exists_sylow_map_eq_of_conj_normalizes {G : Type} [Group G] [Finite G]
    {U : Subgroup G} (P : Sylow 2 G) (hP : (P : Subgroup G) = U)
    {X ψ α : MulAut G} (hα : α = X * ψ * X⁻¹) (hψ : U.map ψ.toMonoidHom = U) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G).map α.toMonoidHom = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (U.map X.toMonoidHom).map α.toMonoidHom = U.map X.toMonoidHom := by
    rw [hα, Subgroup.map_map]
    have hcomp : ((X * ψ * X⁻¹).toMonoidHom.comp X.toMonoidHom) =
        (X.toMonoidHom.comp ψ.toMonoidHom) := by
      ext x
      simp
    rw [hcomp, ← Subgroup.map_map, hψ]
  refine ⟨Sylow.mapSurjective (f := X.toMonoidHom)
    (fun y => ⟨X.symm y, by simp⟩) P, ?_⟩
  change ((P : Subgroup G).map X.toMonoidHom).map α.toMonoidHom =
    (P : Subgroup G).map X.toMonoidHom
  rw [hP]
  exact hnorm

private theorem oddAutSylowFixAt_hypPSU {K : Type} [Field K] {f n r : ℕ}
    (h : UnitaryFieldData 2 f K) (hn3 : 3 ≤ n) (hnq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hr : r.Prime) (hr5 : 5 ≤ r) (hgcd : ¬ r ∣ Nat.gcd n (2 ^ f + 1)) :
    OddAutSylowFixAt r (hypPSU h (n / 2) (n % 2)) := by
  classical
  let m := 2 * (n / 2) + n % 2
  have hn_eq : n = m := by omega
  have hm3 : 3 ≤ m := by omega
  have hmq : ¬(m = 3 ∧ 2 ^ f = 2) := by
    rw [← hn_eq]
    exact hnq
  have hmgcd : ¬ r ∣ Nat.gcd m (2 ^ f + 1) := by
    rw [← hn_eq]
    exact hgcd
  have hr0 : 1 ≤ n / 2 := by omega
  have hε : n % 2 ≤ 1 := by omega
  intro α k hα hinn
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := n / 2) (ε := n % 2) h
  let eP : hypPSU h (n / 2) (n % 2) ≃* primeFormP h ((1 : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) :=
    (hypProjTransport h hR).trans
      (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h m)
  let β : MulAut (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :=
    MulAut.congr eP α
  have hβord : orderOf β = r ^ k := by
    change orderOf (MulAut.congr eP α) = r ^ k
    rw [MulEquiv.orderOf_eq, hα]
  have hβinn : Subgroup.zpowers β ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) = ⊥ := by
    have hmap := congrArg (fun S : Subgroup (MulAut (hypPSU h (n / 2) (n % 2))) =>
      S.map (MulAut.congr eP).toMonoidHom) hinn
    rw [Subgroup.map_inf _ _ _ (MulAut.congr eP).injective, MonoidHom.map_zpowers,
      inner_map_congr, Subgroup.map_bot] at hmap
    simpa [β, MulEquiv.coe_toMonoidHom] using hmap
  obtain ⟨φ, A, hβA, hoddφ, hpowβ'⟩ :=
    exists_primeForm_conj_mul_field_of_pow h hm3 hmq hr hr5 hmgcd hβord hβinn
  obtain ⟨X, hαconj⟩ := exists_hypFieldAut_conj_of_primeForm h hr0 hε hm3 hmq hR α φ A
    hβA hoddφ hpowβ'
  have hFU : (hypProjUnitriangular h (n / 2) (n % 2)).map
      (hypFieldAut h hr0 hε φ).toMonoidHom = hypProjUnitriangular h (n / 2) (n % 2) :=
    map_hypProjUnitriangular_hypFieldAut h hr0 hε φ
  obtain ⟨-, -, -, -, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h hr0 hε
  exact exists_sylow_map_eq_of_conj_normalizes P hP hαconj hFU



theorem oddAutSylowFixAt_psu {Y : Type} [Group Y] [Finite Y] {n f r : ℕ}
    (hC : CFSG.Open.StatedClassicalModel Y .PSU n 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hgcd : ¬ r ∣ Nat.gcd n (2 ^ f + 1)) : OddAutSylowFixAt r Y := by
  obtain ⟨⟨hp, hf1, hn3, hnq⟩, K, hKfield, hKfin, hKcard, ⟨eY⟩⟩ := hC
  have hU : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf1, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have hn_eq : n = 2 * (n / 2) + n % 2 := by omega
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := n / 2) (ε := n % 2) hU
  let eStated : hypPSU hU (n / 2) (n % 2) ≃* StatedProj (StatedSU n (2 ^ f) K) :=
    (hypPSUEquivStatedProj hU hR (by omega : 1 ≤ 2 * (n / 2) + n % 2)).trans
      (MulEquiv.cast (M := fun k => StatedProj (StatedSU k (2 ^ f) K)) hn_eq.symm)
  let e : Y ≃* hypPSU hU (n / 2) (n % 2) := eY.trans eStated.symm
  have hnq' : ¬(n = 3 ∧ 2 ^ f = 2) := fun hc => hnq (Prod.ext hc.1 hc.2)
  have hhyp : OddAutSylowFixAt r (hypPSU hU (n / 2) (n % 2)) :=
    oddAutSylowFixAt_hypPSU hU hn3 hnq' hr hr5 hgcd
  exact OddAutSylowFixAt.of_mulEquiv e.symm hhyp


end

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
