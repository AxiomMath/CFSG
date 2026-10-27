module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsUniLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLin
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAFactors
import CFSG.GroupTheory.PrimeField.SteinbergBNNoncyclicFixedVector
import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverSwap
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.RankThree.PartOne.FOC.PSLDecomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
  (toLinSU exists_good_block_of_component primaryData_toLin')
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement Matrix

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem planeNoComp_primeFormP_of_dvd (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hℓ : ℓ ≠ 2) (hpQ : p ∣ ℓ ^ f + 1) :
    PlaneNoComp p (primeFormP h (idGram K n)) := by
  classical
  intro P hP hcard J hJ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := h.finite
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨-, h2⟩
    apply hℓ
    have h1 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by have := h.one_le; omega)
    rw [h2] at h1
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h1
  have hq2 : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have hpK : (p : K) ≠ 0 := by
    haveI := h.charP
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  obtain ⟨-, -, hker1, -, hexu, hfac, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  have hact : ∀ (B : GL (Fin n) K) (v : Fin n → K),
      ((Matrix.GeneralLinearGroup.toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = (B : Matrix (Fin n) (Fin n) K) *ᵥ v := fun _ _ => rfl
  have hscal : ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X = 1 →
      ∃ c : Kˣ, h.norm (c : K) = 1 ∧
        (X : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c :=
    fun X hX => eq_scalar_of_primeFormConjHom_eq_one h hC hn hX
  have hc1 : ∀ (u : Kˣ) (hu : h.norm (u : K) = 1), primeFormConjHom h (idGram K n)
      ⟨Matrix.GeneralLinearGroup.scalar (Fin n) u, scalar_mem_primeFormUnitary_one h hu⟩ = 1 := by
    intro u hu
    have h1 := (hker1 ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin n) u,
      scalar_mem_primeFormUnitary_one h hu⟩, 1⟩).2 ⟨rfl, u, hu, rfl⟩
    rwa [primeFormPsi_apply, map_one, mul_one] at h1
  have hpow : ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ P →
      ∃ c : Kˣ, h.norm (c : K) = 1 ∧
        (X : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro X hX
    obtain ⟨c, hcN, hXc⟩ := hscal (X ^ p) (by rw [map_pow]; exact hP.2 _ hX)
    exact ⟨c, hcN, by rw [← hXc, SubgroupClass.coe_pow]⟩
  have hcompOf : ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ P →
      primeFormConjHom h (idGram K n) X ≠ 1 →
      ∃ (c : Kˣ) (a : primaryFactors ((Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))),
        (X : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
        dualPoly h.bar (a : K[X]) = a ∧
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K)) a ∧
        J = ((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))
          (a : K[X])).comap (toLinSU h n)).map
            (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := by
    intro X hX hX1
    obtain ⟨c, hcN, hc⟩ := hpow X hX
    have hJX := hJ _ hX hX1
    have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJX
    have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
      hJX (perfectInLayer_primeFormConjHom h hp hpℓ X hc J hJX.1 hperfJ)).1
    have H := primaryData_toLin' h X.2 hp hpℓ hc
    obtain ⟨⟨a, hgood⟩, hJeq⟩ := exists_good_block_of_component hq2 X rfl H J hcomp
    have hζ : (c : K) ^ (ℓ ^ f + 1) = 1 := by
      rw [pow_succ, ← UnitaryFieldData.bar_apply, mul_comm, ← UnitaryFieldData.norm]
      exact hcN
    have hxp : aeval ((Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
        (Polynomial.X ^ p - Polynomial.C (c : K)) = 0 := by
      have e : ((Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) ^ p =
          algebraMap K (Module.End K (Fin n → K)) (c : K) := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, hc]
        refine LinearMap.ext fun v => ?_
        rw [Module.algebraMap_end_apply, ← glScalar_mulVec c v]
        rfl
      rw [map_sub, map_pow, aeval_X, aeval_C, e, sub_self]
    have hself := CFSG.AGLEmbedding.ToralCensus.dualPoly_eq_of_dvd_add_one h H hp hp2 hpQ hζ hxp
      (a : K[X]) a.2
    exact ⟨c, a, hc, hself, hgood, hJeq⟩
  have hcommP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsmulAt : ∀ (A' : primeFormUnitary h (idGram K n)) {c' : Kˣ},
      (A' : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c' →
      primeFormConjHom h (idGram K n) A' ∈ P →
      ∀ {a' : primaryFactors ((Matrix.GeneralLinearGroup.toLin (A' : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))},
      dualPoly h.bar (a' : K[X]) = a' →
      IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (A' : GL (Fin n) K)) a' →
      J = ((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A' : GL (Fin n) K))
          (a' : K[X])).comap (toLinSU h n)).map
            (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) →
      ∀ (B : primeFormUnitary h (idGram K n)) (τ : K ≃+* K),
        primeFormConjHom h (idGram K n) B * primeFormFieldHom h hC τ ∈ P → τ ^ p = 1 →
        τ = 1 ∧ ∃ e : AdjoinRoot (a' : K[X]),
          ∀ w : primaryComponent ((Matrix.GeneralLinearGroup.toLin (A' : GL (Fin n) K) :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a' : K[X]),
            ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
              ((e • w : primaryComponent ((Matrix.GeneralLinearGroup.toLin
                (A' : GL (Fin n) K) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
                  Module.End K (Fin n → K)) (a' : K[X])) : Fin n → K) := by
    intro A' c' hA' hA'P a' hself' hgood' hJ' B τ hzP hτ
    set z := primeFormConjHom h (idGram K n) B * primeFormFieldHom h hC τ with hz
    have hfix : ∀ g ∈ (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin
        (A' : GL (Fin n) K)) (a' : K[X])).comap (toLinSU h n),
        z (g : primeFormP h (idGram K n)) = g := by
      intro g hg
      by_cases hz1 : z = 1
      · rw [hz1]
        rfl
      · have hmem : (g : primeFormP h (idGram K n)) ∈ J := by
          rw [hJ']
          exact ⟨g, hg, rfl⟩
        exact (hJ z hzP hz1).1 hmem
    obtain ⟨μ, hμ⟩ : ∃ μ : K, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
        (μ • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have h1 : primeFormConjHom h (idGram K n)
          (B * primeFormFieldU h hC τ A' * B⁻¹ * A'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← primeFormField_conj_eq h hC τ A']
        have e1 : primeFormConjHom h (idGram K n) B * (primeFormFieldHom h hC τ *
            primeFormConjHom h (idGram K n) A' * (primeFormFieldHom h hC τ)⁻¹) *
            (primeFormConjHom h (idGram K n) B)⁻¹ * (primeFormConjHom h (idGram K n) A')⁻¹ =
            z * primeFormConjHom h (idGram K n) A' * z⁻¹ *
              (primeFormConjHom h (idGram K n) A')⁻¹ := by
          rw [hz]
          group
        rw [e1, hcommP z hzP _ hA'P]
        group
      obtain ⟨u, -, hu⟩ := hscal _ h1
      refine ⟨(u : K), ?_⟩
      have h2 : (B : GL (Fin n) K) * glAut τ (A' : GL (Fin n) K) =
          Matrix.GeneralLinearGroup.scalar (Fin n) u * (A' : GL (Fin n) K) * B := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, coe_primeFormFieldU] at hu
        rw [← hu]
        group
      have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = (u : K) • (1 : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
      have h3 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h2
      rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_glAut, hsc, Matrix.smul_mul,
        Matrix.one_mul] at h3
      exact h3
    exact exists_smul_of_fix_specialBlock_uni h hℓ hp hp2 hpℓ A' hA' rfl hself' hgood' B τ hτ μ
      hμ hfix
  have hform : ∀ z ∈ P, ∃ (B : primeFormUnitary h (idGram K n)) (τ : K ≃+* K),
      z = primeFormConjHom h (idGram K n) B * primeFormFieldHom h hC τ ∧ τ ^ p = 1 := by
    intro z hz
    obtain ⟨τ, ⟨B, hzB⟩, -⟩ := hexu z
    refine ⟨B, τ, hzB, ?_⟩
    have h1 : primeFormFieldFactor h hC hn hq z = τ := by
      rw [hzB]
      exact hfac B τ
    rw [← h1, ← map_pow, hP.2 z hz, map_one]
  haveI hVe : IsElementaryAbelian p ↥P :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p P).2 hP
  obtain ⟨x₀, hx₀P, hx₀1, hx₀Φ⟩ : ∃ x₀ ∈ P, x₀ ≠ 1 ∧ primeFormFieldFactor h hC hn hq x₀ = 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective ((primeFormFieldFactor h hC hn hq).comp P.subtype) := by
      rw [injective_iff_map_eq_one]
      intro v hv
      by_contra hv1
      exact hcon v v.2 (fun h1 => hv1 (Subtype.ext h1)) hv
    haveI := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_ringAut K
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard (isCyclic_of_injective _ hinj)
  have hx₀D : x₀ ∈ (primeFormFieldFactor h hC hn hq).ker := hx₀Φ
  rw [hkerD, primeFormD, MonoidHom.mem_range] at hx₀D
  obtain ⟨A, rfl⟩ := hx₀D
  obtain ⟨c, a, hc, hself, hgood, hJeq⟩ := hcompOf A hx₀P hx₀1
  have H := primaryData_toLin' h A.2 hp hpℓ hc
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  set F := (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (a : K[X])).comap (toLinSU h n) with hFdef
  have hperfF : ⁅F, F⁆ = F := commutator_comap_specialBlock_eq h H hgood
  set W := primaryComponent ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) :
    LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]) with hWdef
  obtain ⟨w₀, hw₀⟩ : ∃ w : W, w ≠ 0 := by
    have h2 : 2 ≤ finrank (AdjoinRoot (a : K[X])) W := hgood.1
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := AdjoinRoot (a : K[X])) (by omega)
    exact exists_ne 0
  have hw₀' : (w₀ : Fin n → K) ≠ 0 := fun h0 => hw₀ (Subtype.ext h0)
  have hker : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
      Subgroup.center _ := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hSBle : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.mem_range_toLinSU
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 a hgood hg)
  have hinner : ∀ z ∈ P, ∃ B : primeFormUnitary h (idGram K n), primeFormConjHom h _ B = z := by
    intro z hz
    obtain ⟨B, τ, rfl, hτ⟩ := hform z hz
    obtain ⟨hτ1, -⟩ := hsmulAt A hc hx₀P hself hgood hJeq B τ hz hτ
    exact ⟨B, by rw [hτ1, map_one, mul_one]⟩
  set S : Subgroup (GL (Fin n) K) := (P.comap (primeFormConjHom h (idGram K n))).map
    (primeFormUnitary h (idGram K n)).subtype with hSdef
  have hsmulB : ∀ B ∈ S, ∃ e : AdjoinRoot (a : K[X]), ∀ w : W,
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = ((e • w : W) : Fin n → K) := by
    rintro _ ⟨B₀, hB₀, rfl⟩
    obtain ⟨-, e, he⟩ := hsmulAt A hc hx₀P hself hgood hJeq B₀ 1
      (by rw [map_one, mul_one]; exact hB₀) (one_pow p)
    exact ⟨e, he⟩
  obtain ⟨ρ, hρ⟩ := exists_unitsHom_of_smul ⟨w₀, hw₀⟩ S hsmulB
  have hexB : ∃ B : primeFormUnitary h (idGram K n), primeFormConjHom h _ B ∈ P ∧
      primeFormConjHom h _ B ≠ 1 ∧
      ∀ w : W, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥ρ.range)
    obtain ⟨g₀, hg₀⟩ := γ.2
    obtain ⟨B₀, hB₀, hB₀g⟩ := g₀.2
    refine IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard ?_
    have hle : P ≤ Subgroup.zpowers (primeFormConjHom h (idGram K n) B₀) := by
      intro z hz
      obtain ⟨B, rfl⟩ := hinner z hz
      have hBS : (B : GL (Fin n) K) ∈ S := ⟨B, hz, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨ρ ⟨B, hBS⟩, ⟨B, hBS⟩, rfl⟩)
      have hk' : ρ (g₀ ^ k) = ρ ⟨B, hBS⟩ := by
        rw [map_zpow, hg₀]
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_zpow] at this
      set B' : ↥S := ⟨B, hBS⟩ * (g₀ ^ k)⁻¹ with hB'
      have hρB' : ρ B' = 1 := by rw [hB', map_mul, map_inv, hk', mul_inv_cancel]
      have hfixB' : ∀ w : W, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (w : Fin n → K) = w := by
        intro w
        rw [hρ B' w, hρB']
        exact congrArg Subtype.val (one_smul _ w)
      have hB''val : ((B * (B₀ ^ k)⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
          (B' : GL (Fin n) K) := by
        have hB₀g' : (B₀ : GL (Fin n) K) = (g₀ : GL (Fin n) K) := hB₀g
        rw [hB', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
          Subgroup.coe_zpow, Subgroup.coe_zpow, hB₀g']
      have hB''P : primeFormConjHom h (idGram K n) (B * (B₀ ^ k)⁻¹) ∈ P := by
        rw [map_mul, map_inv, map_zpow]
        exact mul_mem hz (inv_mem (zpow_mem (Subgroup.mem_comap.mp hB₀) k))
      have hB''1 : primeFormConjHom h (idGram K n) (B * (B₀ ^ k)⁻¹) = 1 := by
        by_contra hne
        obtain ⟨w, hw⟩ := hcon _ hB''P hne
        exact hw (by rw [hB''val]; exact hfixB' w)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have h1 : primeFormConjHom h (idGram K n) (B * (B₀ ^ k)⁻¹) =
          primeFormConjHom h (idGram K n) B * (primeFormConjHom h (idGram K n) B₀ ^ k)⁻¹ := by
        rw [map_mul, map_inv, map_zpow]
      rw [hB''1] at h1
      exact (mul_inv_eq_one.1 h1.symm).symm
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hdata : ∀ B' : primeFormUnitary h (idGram K n), primeFormConjHom h _ B' ∈ P →
      primeFormConjHom h _ B' ≠ 1 →
      (∀ w : W, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w) →
      ∃ (d : Kˣ) (b : primaryFactors ((Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))),
        (B' : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) d ∧
        dualPoly h.bar (b : K[X]) = b ∧
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K)) b ∧
        J = ((specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K))
          (b : K[X])).comap (toLinSU h n)).map
            (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) ∧
        primaryComponent ((Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (b : K[X]) = W ∧
        (b : K[X]).eval 1 = 0 := by
    intro B' hB'P hB'1 hB'fix
    obtain ⟨d, b, hd, hself', hgood', hJeq'⟩ := hcompOf B' hB'P hB'1
    have H' := primaryData_toLin' h B'.2 hp hpℓ hd
    have hperf' := commutator_comap_specialBlock_eq h H' hgood'
    have hFeq : (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K))
        (b : K[X])).comap (toLinSU h n) = F := le_antisymm
      (CFSG.ComponentClassification.SolMax.le_of_map_le_of_perfect _ hker hperf'
        (by rw [← hJeq', ← hJeq]))
      (CFSG.ComponentClassification.SolMax.le_of_map_le_of_perfect _ hker hperfF
        (by rw [← hJeq', ← hJeq]))
    have hSBle' : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K))
        (b : K[X]) ≤ (toLinSU h n).range := fun g hg =>
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.mem_range_toLinSU
        (specialBlock_le_sesqSpecialUnitaryGroup_of_good H' hq2 b hgood' hg)
    have hSBeq : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K))
        (b : K[X]) = specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
          (a : K[X]) := by
      rw [← Subgroup.map_comap_eq_self hSBle', ← Subgroup.map_comap_eq_self hSBle, hFeq]
    have hWeq : primaryComponent ((Matrix.GeneralLinearGroup.toLin (B' : GL (Fin n) K) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (b : K[X]) =
        W := le_antisymm
      (primaryComponent_le_of_specialBlock_eq hℓ H' H hself' hself hgood' hSBeq)
      (primaryComponent_le_of_specialBlock_eq hℓ H H' hself hself' hgood hSBeq.symm)
    have hev : (b : K[X]).eval 1 = 0 := by
      have hmem : (w₀ : Fin n → K) ∈ primaryComponent ((Matrix.GeneralLinearGroup.toLin
          (B' : GL (Fin n) K) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) (b : K[X]) := by
        rw [hWeq]
        exact w₀.2
      have h1 := mem_primaryComponent.mp hmem
      rw [aeval_apply_eq_eval_one_smul (by rw [hact]; exact hB'fix w₀) (b : K[X])] at h1
      exact (smul_eq_zero.mp h1).resolve_right hw₀'
    exact ⟨d, b, hd, hself', hgood', hJeq', hWeq, hev⟩
  have hfixW : ∀ B' : primeFormUnitary h (idGram K n), primeFormConjHom h _ B' ∈ P →
      primeFormConjHom h _ B' ≠ 1 →
      (∀ w : W, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w) →
      ∀ u : Fin n → K, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u → u ∈ W := by
    intro B' hB'P hB'1 hB'fix u hu
    obtain ⟨d, b, -, -, -, -, hWeq, hev⟩ := hdata B' hB'P hB'1 hB'fix
    rw [← hWeq, mem_primaryComponent,
      aeval_apply_eq_eval_one_smul (by rw [hact]; exact hu) (b : K[X]), hev, zero_smul]
  obtain ⟨B, hBP, hB1, hBfix⟩ := hexB
  obtain ⟨dB, bB, hdB, hselfB, hgoodB, hJB, hWB, hevB⟩ := hdata B hBP hB1 hBfix
  have HB := primaryData_toLin' h B.2 hp hpℓ hdB
  have hcop : Nat.Coprime p (ℓ ^ f - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h1 => hp2 ?_
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub hpQ h1
      rwa [show ℓ ^ f + 1 - (ℓ ^ f - 1) = 2 by omega] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  have hnorm : ∀ z ∈ P, ∃ B₂ : primeFormUnitary h (idGram K n), primeFormConjHom h _ B₂ = z ∧
      ∀ w : W, ((B₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w := by
    intro z hz
    obtain ⟨B₂', rfl⟩ := hinner z hz
    obtain ⟨-, e, he⟩ := hsmulAt B hdB hBP hselfB hgoodB hJB B₂' 1
      (by rw [map_one, mul_one]; exact hz) (one_pow p)
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective e
    have hactW : ∀ w : W, ((B₂' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
        g.eval 1 • (w : Fin n → K) := by
      intro w
      have hwB : (w : Fin n → K) ∈ primaryComponent ((Matrix.GeneralLinearGroup.toLin
          (B : GL (Fin n) K) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) (bB : K[X]) := by
        rw [hWB]
        exact w.2
      have h1 := he ⟨w, hwB⟩
      rw [coe_mk_smul_primaryComponent,
        aeval_apply_eq_eval_one_smul (by rw [hact]; exact hBfix w) g] at h1
      exact h1
    have hl0 : g.eval 1 ≠ 0 := by
      intro h0
      have h1 := hactW w₀
      rw [h0, zero_smul] at h1
      apply hw₀'
      have h2 : (((B₂'⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ
          (((B₂' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w₀ : Fin n → K)) = w₀ := by
        rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      rw [h1, Matrix.mulVec_zero] at h2
      exact h2.symm
    obtain ⟨d₂, hd₂N, hd₂⟩ := hpow B₂' hz
    have hpowW : ∀ m : ℕ, (((B₂' : GL (Fin n) K) ^ m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (w₀ : Fin n → K) = (g.eval 1) ^ m • (w₀ : Fin n → K) := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, Units.val_one, Matrix.one_mulVec, one_smul]
      | succ m ih =>
        rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hactW w₀, Matrix.mulVec_smul, ih,
          smul_smul, pow_succ, mul_comm]
    have hlp : (g.eval 1) ^ p = (d₂ : K) := by
      have h1 := hpowW p
      rw [hd₂, glScalar_mulVec] at h1
      have h2 : ((g.eval 1) ^ p - (d₂ : K)) • (w₀ : Fin n → K) = 0 := by
        rw [sub_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw₀')
    have hlN : h.norm (g.eval 1) = 1 := by
      have hN : h.norm (g.eval 1) = (g.eval 1) ^ (ℓ ^ f + 1) := by
        rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, pow_succ, mul_comm]
      have e1 : ((g.eval 1) ^ (ℓ ^ f + 1)) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hlp, pow_succ, ← UnitaryFieldData.bar_apply, mul_comm,
          ← UnitaryFieldData.norm]
        exact hd₂N
      have e2 : ((g.eval 1) ^ (ℓ ^ f + 1)) ^ (ℓ ^ f - 1) = 1 := by
        have := Fintype.ofFinite K
        rw [← pow_mul, show (ℓ ^ f + 1) * (ℓ ^ f - 1) = Fintype.card K - 1 by
          rw [← Nat.card_eq_fintype_card, h.card, pow_mul', ← Nat.sq_sub_sq, one_pow]]
        exact FiniteField.pow_card_sub_one_eq_one _ hl0
      have e3 := pow_gcd_eq_one.mpr ⟨e1, e2⟩
      rw [hcop.gcd_eq_one, pow_one] at e3
      rw [hN, e3]
    have hlinv : h.norm (((Units.mk0 (g.eval 1) hl0)⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, UnitaryFieldData.norm, map_inv₀, ← mul_inv,
        ← UnitaryFieldData.norm, hlN, inv_one]
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 (g.eval 1) hl0)⁻¹,
      scalar_mem_primeFormUnitary_one h hlinv⟩ * B₂', ?_, fun w => ?_⟩
    · rw [map_mul, hc1 _ hlinv, one_mul]
    · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hactW w, Matrix.mulVec_smul,
        Subtype.coe_mk, glScalar_mulVec, smul_smul, Units.val_inv_eq_inv_val, Units.val_mk0,
        mul_inv_cancel₀ hl0, one_smul]
  let S1 : Subgroup (primeFormUnitary h (idGram K n)) :=
    { carrier := {B' | primeFormConjHom h (idGram K n) B' ∈ P ∧
        ∀ w : W, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w}
      mul_mem' := by
        rintro a b ⟨haP, haW⟩ ⟨hbP, hbW⟩
        refine ⟨by rw [map_mul]; exact mul_mem haP hbP, fun w => ?_⟩
        rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hbW w, haW w]
      one_mem' := ⟨by rw [map_one]; exact one_mem P, fun w => by
        rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]⟩
      inv_mem' := by
        rintro a ⟨haP, haW⟩
        refine ⟨by rw [map_inv]; exact inv_mem haP, fun w => ?_⟩
        conv_lhs => rw [← haW w]
        rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec] }
  have hscalW : ∀ B' : primeFormUnitary h (idGram K n), primeFormConjHom h _ B' = 1 →
      (∀ w : W, ((B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w) →
      B' = 1 := by
    intro B' h1 hW'
    obtain ⟨s, -, hs⟩ := hscal B' h1
    have h2 := hW' w₀
    rw [hs] at h2
    apply Subtype.ext
    rw [hs, scalar_eq_one_of_mulVec_eq hw₀' h2, map_one, Subgroup.coe_one]
  have hcomm : ∀ a ∈ S1, ∀ b ∈ S1, a * b = b * a := by
    intro a ha b hb
    have hc1' : primeFormConjHom h (idGram K n) (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommP _ ha.1 _ hb.1]
      group
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ S1 :=
      S1.mul_mem (S1.mul_mem (S1.mul_mem ha hb) (S1.inv_mem ha)) (S1.inv_mem hb)
    have h1 := hscalW _ hc1' hmem.2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hsqB := HB.squarefree
  set π := primaryProjection ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) :
    LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (bB : K[X]) with hπ
  set U : Submodule K (Fin n → K) := LinearMap.ker π with hU
  have hBS : B ∈ S1 := ⟨hBP, hBfix⟩
  have hπcomm : ∀ a ∈ S1, Commute ((Matrix.GeneralLinearGroup.toLin (a : GL (Fin n) K) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) π := by
    intro a ha
    have h1 : Commute ((Matrix.GeneralLinearGroup.toLin (a : GL (Fin n) K) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
        ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
      have := hcomm a ha B hBS
      change ((Matrix.GeneralLinearGroup.toLin (a : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) *
          ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) :
            LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
        ((Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) *
          ((Matrix.GeneralLinearGroup.toLin (a : GL (Fin n) K) :
            LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, this]
    exact commute_aeval h1 _
  have hUinv : ∀ a ∈ S1, ∀ u ∈ U, ((Matrix.GeneralLinearGroup.toLin (a : GL (Fin n) K) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) u ∈ U := by
    intro a ha u hu
    rw [hU, LinearMap.mem_ker] at hu ⊢
    rw [← Module.End.mul_apply, ← (hπcomm a ha).eq, Module.End.mul_apply, hu, map_zero]
  letI : CommGroup ↥S1 :=
    { (inferInstance : Group ↥S1) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let ρU : Representation K ↥S1 ↥U :=
    { toFun := fun a => ((Matrix.GeneralLinearGroup.toLin ((a : primeFormUnitary h (idGram K n)) :
        GL (Fin n) K) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)).restrict (hUinv a a.2)
      map_one' := by
        refine LinearMap.ext fun u => Subtype.ext ?_
        rw [LinearMap.restrict_coe_apply, hact, OneMemClass.coe_one, OneMemClass.coe_one,
          Units.val_one, Matrix.one_mulVec]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun u => Subtype.ext ?_
        rw [LinearMap.restrict_coe_apply, hact, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
          ← Matrix.mulVec_mulVec, Module.End.mul_apply, LinearMap.restrict_coe_apply,
          LinearMap.restrict_coe_apply, hact, hact] }
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hB1
    have hfixall : ∀ v : Fin n → K, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
      intro v
      have hvπ : v - π v ∈ U := by
        rw [hU, LinearMap.mem_ker, map_sub,
          primaryProjection_of_mem hsqB bB.2 (primaryProjection_mem hsqB bB.2 v), sub_self]
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hvπ
      have hvW : v ∈ W := by
        rw [← hWB, hvπ]
        exact primaryProjection_mem hsqB bB.2 v
      exact hBfix ⟨v, hvW⟩
    have hB1' : B = 1 := Subtype.ext (by
      rw [Subgroup.coe_one]
      exact eq_one_of_mulVec_eq_self hfixall)
    rw [hB1', map_one]
  haveI : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.2 hUne
  have hWU : ∀ u : Fin n → K, u ∈ U → u ∈ W → u = 0 := by
    intro u huU huW
    have h1 : π u = u := primaryProjection_of_mem hsqB bB.2 (by rw [hWB]; exact huW)
    rw [← h1]
    exact huU
  obtain ⟨z₂, hz₂P, hz₂⟩ : ∃ z₂ ∈ P, z₂ ∉ Subgroup.zpowers (primeFormConjHom h (idGram K n) B) := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card P ≤ Nat.card (Subgroup.zpowers (primeFormConjHom h (idGram K n) B)) :=
      Subgroup.card_le_of_le hcon
    rw [Nat.card_zpowers, hcard] at hle
    have h2 : orderOf (primeFormConjHom h (idGram K n) B) ≤ p :=
      orderOf_le_of_pow_eq_one hp.pos (hP.2 _ hBP)
    have h3 := hle.trans h2
    nlinarith [hp.two_le]
  obtain ⟨B₂, hB₂z, hB₂W⟩ := hnorm z₂ hz₂P
  have hB₂S : B₂ ∈ S1 := ⟨by rw [hB₂z]; exact hz₂P, hB₂W⟩
  have hpow1 : ∀ a ∈ S1, a ^ p = 1 := by
    intro a ha
    obtain ⟨d, -, hd⟩ := hpow a ha.1
    have hmem : a ^ p ∈ S1 := S1.pow_mem ha p
    have h2 := hmem.2 w₀
    rw [SubgroupClass.coe_pow, hd] at h2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hd, scalar_eq_one_of_mulVec_eq hw₀' h2, map_one, Subgroup.coe_one]
  have hy : (⟨B, hBS⟩ : ↥S1) ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hpow1 B hBS)
  have hx : (⟨B₂, hB₂S⟩ : ↥S1) ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hpow1 B₂ hB₂S)
  have hy1 : (⟨B, hBS⟩ : ↥S1) ≠ 1 := by
    intro h1
    apply hB1
    have h2 : B = 1 := congrArg Subtype.val h1
    rw [h2, map_one]
  have hxy : (⟨B₂, hB₂S⟩ : ↥S1) ∉ Subgroup.zpowers (⟨B, hBS⟩ : ↥S1) := by
    rintro ⟨k, hk⟩
    apply hz₂
    refine ⟨k, ?_⟩
    have h1 := congrArg (fun a : ↥S1 => primeFormConjHom h (idGram K n)
      (a : primeFormUnitary h (idGram K n))) hk
    simp only [SubgroupClass.coe_zpow, map_zpow] at h1
    rw [← hB₂z, ← h1]
  obtain ⟨a, ha1, v, hv0, hav⟩ :=
    CFSG.GroupTheory.PrimeField.exists_fixed_of_pow_eq_one ρU hp hpK hx hy hy1 hxy
  have hav' : (((a : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ (v : Fin n → K) = (v : Fin n → K) := by
    have := congrArg Subtype.val hav
    rw [← hact]
    exact this
  have ha1' : primeFormConjHom h (idGram K n) (a : primeFormUnitary h (idGram K n)) ≠ 1 := by
    intro h1
    exact ha1 (Subtype.ext (hscalW _ h1 a.2.2))
  have hvW := hfixW _ a.2.1 ha1' a.2.2 _ hav'
  exact hv0 (Subtype.ext (hWU _ v.2 hvW))

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
