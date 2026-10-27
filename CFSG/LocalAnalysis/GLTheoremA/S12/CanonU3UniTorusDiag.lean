module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniBlock
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitary
public import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAFactors

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open Matrix Polynomial Module
open scoped Classical
open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks

theorem isComponentOf_blockImage {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    (A : primeFormUnitary h (idGram K N)) {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K))
    (H : UnitaryPrimaryData h.bar (idForm h N) x)
    {a : primaryFactors (x : Module.End K (Fin N → K))} (hgood : IsGoodBlock h x a) :
    CFSG.Open.IsComponentOf (blockImage h x (a : K[X]))
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom h (idGram K N) A)) := by
  classical
  subst hx
  haveI := h.finite
  let F := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryGlue.specialSU
    h (A : GL (Fin N) K) (a : K[X])
  have hcomp := isComponentOf_map_fixSubgroup_aux
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K N)) N))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact normOneScalars_le_center h _ N)
    (primeFormConjSU h (idGram K N) A) (primeFormConjHom h (idGram K N) A)
    (fun g => (primeFormConjHom_mk h (idGram K N) A g).symm)
    (F := F) (fun g hg => ?_) (fun c hc g hg => ?_) (by
      exact UnitaryGlue.isQuasisimple_specialSU
        h H (j := (a : K[X])) a.2 hgood)
  · exact hcomp
  · rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryGlue.mem_specialSU] at hg
    refine (mem_fixSubgroup_primeFormConjSU_iff A rfl g).mpr ?_
    exact (specialBlock_le_unitaryCentralizer hg).2
  · rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryGlue.mem_specialSU] at hg ⊢
    have hcU : toLinSU h N c ∈ unitaryCentralizer (idForm h N)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) :=
      toLinSU_mem_unitaryCentralizer A rfl hc
    have hconj := conj_mem_specialBlock hcU hg
    simpa [map_mul, map_inv] using hconj

theorem blockImage_ne_of_good_ne {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    (A : primeFormUnitary h (idGram K N)) {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K))
    (H : UnitaryPrimaryData h.bar (idForm h N) x)
    {a b : primaryFactors (x : Module.End K (Fin N → K))}
    (hgooda : IsGoodBlock h x a) (hgoodb : IsGoodBlock h x b)
    (hba : (b : K[X]) ≠ (a : K[X]))
    (hbd : (b : K[X]) ≠ dualPoly h.bar (a : K[X])) :
    blockImage h x (a : K[X]) ≠ blockImage h x (b : K[X]) := by
  classical
  haveI := h.finite
  intro hEq
  have hca := isComponentOf_blockImage h A hx H hgooda
  have hqa : CFSG.Open.IsQuasisimple ↥(blockImage h x (a : K[X])) := hca.2.2
  have hqa' : CFSG.IsQuasisimple ↥(blockImage h x (a : K[X])) :=
    ⟨⟨hqa.1⟩, hqa.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hqa⟩
  have hcomm : ∀ u ∈ blockImage h x (a : K[X]), ∀ v ∈ blockImage h x (b : K[X]), Commute u v := by
    intro u hu v hv
    obtain ⟨gu, hgu, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨gv, hgv, rfl⟩ := Subgroup.mem_map.mp hv
    have hgu' : toLinSU h N gu ∈ specialBlock (idForm h N) x (a : K[X]) :=
      Subgroup.mem_comap.mp hgu
    have hgv' : toLinSU h N gv ∈ specialBlock (idForm h N) x (b : K[X]) :=
      Subgroup.mem_comap.mp hgv
    have hc := (commute_specialBlock_of_ne H a b hba hbd hgu' hgv').eq
    have hc' : gu * gv = gv * gu := by
      apply toLinSU_injective (h := h) (n := N)
      rw [map_mul, map_mul]
      exact hc
    show (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K N)) N)) gu *
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K N)) N)) gv =
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K N)) N)) gv *
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K N)) N)) gu
    simpa only [map_mul] using congrArg (QuotientGroup.mk'
      (normOneScalars h (gramSU h (idGram K N)) N)) hc'
  obtain ⟨u, hu, v, hv, huv⟩ :=
    CFSG.ClassicalInvolution.Balance.LocalBalance.exists_noncomm_of_isQuasisimple hqa'
  exact huv (hcomm u hu v (hEq ▸ hv))

theorem primaryMultiplicity_le_one_of_ne {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f)
    (A : primeFormUnitary h (idGram K N)) {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K))
    (H : UnitaryPrimaryData h.bar (idForm h N) x)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors (x : Module.End K (Fin N → K)))
    (hm : primaryMultiplicity (x : Module.End K (Fin N → K)) (X - C μ) = 3)
    (hunique : ∀ T' : Subgroup (primeFormP h (idGram K N)),
      CFSG.Open.IsComponentOf T'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (primeFormConjHom h (idGram K N) A)) →
      T' = blockImage h x (X - C μ))
    (b : primaryFactors (x : Module.End K (Fin N → K)))
    (hb : b ≠ ⟨X - C μ, ha⟩) :
    primaryMultiplicity (x : Module.End K (Fin N → K)) (b : K[X]) ≤ 1 := by
  classical
  haveI := h.finite
  let a : primaryFactors (x : Module.End K (Fin N → K)) := ⟨X - C μ, ha⟩
  have hma : primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]) = 3 := by
    simpa [a] using hm
  have hselfa : dualPoly h.bar (a : K[X]) = (a : K[X]) := by
    simpa [a] using CFSG.HardMathSupport.Timmesfeld.CrossChar.dualPoly_X_sub_C_self hμ
  have hdega : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hQ4a : 4 ≤ 2 ^ (f * (a : K[X]).natDegree) :=
    hq.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right f hdega))
  have hgooda : IsGoodBlock h x a := by
    refine ⟨by omega, ?_⟩
    intro _
    intro hmem
    have h' : (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]) = 2 ∧
        (2 : ℕ) ^ (f * (a : K[X]).natDegree) = 2) ∨
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]) = 2 ∧
        (2 : ℕ) ^ (f * (a : K[X]).natDegree) = 3) ∨
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]) = 3 ∧
        (2 : ℕ) ^ (f * (a : K[X]).natDegree) = 2) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using hmem
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  by_contra hle
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K (Fin N → K)) (b : K[X]) := by omega
  have hgoodb : IsGoodBlock h x b := by
    refine ⟨hm2, ?_⟩
    intro _
    have hdeg : 1 ≤ (b : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors b.2)
    have hfd : f ≤ f * (b : K[X]).natDegree := Nat.le_mul_of_pos_right f hdeg
    have hQ4 : 4 ≤ 2 ^ (f * (b : K[X]).natDegree) :=
      hq.trans (Nat.pow_le_pow_right (by norm_num) hfd)
    intro hmem
    have h' : (primaryMultiplicity (x : Module.End K (Fin N → K)) (b : K[X]) = 2 ∧
        (2 : ℕ) ^ (f * (b : K[X]).natDegree) = 2) ∨
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (b : K[X]) = 2 ∧
        (2 : ℕ) ^ (f * (b : K[X]).natDegree) = 3) ∨
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (b : K[X]) = 3 ∧
        (2 : ℕ) ^ (f * (b : K[X]).natDegree) = 2) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using hmem
    rcases h' with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
  have hba : (b : K[X]) ≠ (a : K[X]) := fun hEq => hb (Subtype.ext hEq)
  have hcomp := isComponentOf_blockImage h A hx H hgoodb
  have heq : blockImage h x (b : K[X]) = blockImage h x (a : K[X]) := by
    simpa [a] using hunique (blockImage h x (b : K[X])) hcomp
  by_cases hbd : (b : K[X]) = dualPoly h.bar (a : K[X])
  · have hbaeq : b = a := Subtype.ext (hbd.trans hselfa)
    exact hb hbaeq
  · exact (blockImage_ne_of_good_ne h A hx H hgooda hgoodb hba hbd) heq.symm

theorem exists_linear_of_mem_primaryFactors {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h3 : 3 ∣ 2 ^ f + 1)
    (A : primeFormUnitary h (idGram K N)) {c : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {μ : K} (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    (b : primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))) :
    ∃ ν : K, (b : K[X]) = X - C ν ∧ ν ^ 3 = (c : K) := by
  classical
  haveI := h.finite
  let x : LinearMap.GeneralLinearGroup K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  have H : UnitaryPrimaryData h.bar (idForm h N) x :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA
  have hx3u : x ^ 3 = Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.scalar (Fin N) c) := by
    rw [show x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) from rfl, ← map_pow, hA]
  have hx3 : ((x : Module.End K (Fin N → K)) ^ 3 =
      (c : K) • (1 : Module.End K (Fin N → K))) := by
    have h1 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (u : Module.End K (Fin N → K))) hx3u
    rw [← Units.val_pow_eq_pow_val, h1]
    apply LinearMap.ext
    intro v
    simpa using toLin_scalar_apply c v
  have hxaeval : aeval (x : Module.End K (Fin N → K)) (X ^ 3 - C (c : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx3, Algebra.algebraMap_eq_smul_one, sub_self]
  have hμ3 : μ ^ 3 = (c : K) := by
    have ha' : (X - C μ) ∈ primaryFactors (x : Module.End K (Fin N → K)) := by
      simpa [x] using ha
    have hne : primaryComponent (x : Module.End K (Fin N → K)) (X - C μ) ≠ ⊥ :=
      primaryComponent_ne_bot H.squarefree ha'
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxv : (x : Module.End K (Fin N → K)) v = μ • v :=
      (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hv
    have h1 : ((x : Module.End K (Fin N → K)) ^ 3) v = (μ ^ 3) • v := by
      rw [pow_three]
      simp only [Module.End.mul_apply, map_smul, hxv, smul_smul]
      ring_nf
    have h2 : ((x : Module.End K (Fin N → K)) ^ 3) v = (c : K) • v := by
      rw [hx3]
      rfl
    have h3 : ((μ ^ 3 - (c : K)) • v) = 0 := by
      rw [sub_smul, ← h1, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hvne)
  obtain ⟨ω, hω3, hω1, -⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_cube_root_bar h h3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hωprim : IsPrimitiveRoot ω 3 := by
    have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    exact hord ▸ IsPrimitiveRoot.orderOf ω
  exact CFSG.AGLEmbedding.ToralCensus.exists_eq_X_sub_C_of_mem_primaryFactors
    (by norm_num : 0 < 3) hωprim hμ3 hxaeval b.2

theorem commute_of_conjHom_commute {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) (hN : 4 ≤ N)
    (A B : primeFormUnitary h (idGram K N)) {c : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    (hm : primaryMultiplicity
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
      (X - C μ) = 3)
    (hunique : ∀ T' : Subgroup (primeFormP h (idGram K N)),
      CFSG.Open.IsComponentOf T'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (primeFormConjHom h (idGram K N) A)) →
      T' = blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ))
    (hc : Commute (primeFormConjHom h (idGram K N) A) (primeFormConjHom h (idGram K N) B)) :
    Commute (A : GL (Fin N) K) (B : GL (Fin N) K) := by
  classical
  haveI := h.finite
  have hn3 : 3 ≤ N := by omega
  have hne : ¬(N = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨rfl, hq2⟩
    omega
  let x : Module.End K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let y : Module.End K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (B : GL (Fin N) K)
  have H : UnitaryPrimaryData h.bar (idForm h N)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA
  let z : primeFormUnitary h (idGram K N) := (B * A)⁻¹ * (A * B)
  have hzρ : primeFormConjHom h (idGram K N) z = 1 := by
    change primeFormConjHom h (idGram K N) ((B * A)⁻¹ * (A * B)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hc.eq, inv_mul_cancel]
  obtain ⟨c, -, hzc⟩ := (mem_idScalarKernel (h := h) (n := N)).mp
    ((primeFormConjHom_eq_one_iff_of_ne hn3 hne z).mp hzρ)
  have hz' : (A : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) *
      (B : GL (Fin N) K) = GeneralLinearGroup.scalar (Fin N) c := by
    rw [← hzc]
    simp only [z, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h1 : (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) * (B : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) c * (A : GL (Fin N) K) := by
    calc (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) * (B : GL (Fin N) K)
        = (A : GL (Fin N) K) * ((A : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K)⁻¹ *
            (A : GL (Fin N) K) * (B : GL (Fin N) K)) := by group
      _ = (A : GL (Fin N) K) * GeneralLinearGroup.scalar (Fin N) c := by rw [hz']
      _ = GeneralLinearGroup.scalar (Fin N) c * (A : GL (Fin N) K) :=
          (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (A : GL (Fin N) K)).eq
  have hconj' : (B : GL (Fin N) K) * (GeneralLinearGroup.scalar (Fin N) c *
      (A : GL (Fin N) K)) * (B : GL (Fin N) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin N) c *
        ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) := by
    calc (B : GL (Fin N) K) * (GeneralLinearGroup.scalar (Fin N) c *
          (A : GL (Fin N) K)) * (B : GL (Fin N) K)⁻¹
        = ((B : GL (Fin N) K) * GeneralLinearGroup.scalar (Fin N) c) *
            (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin N) c * (B : GL (Fin N) K)) *
            (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c
            (B : GL (Fin N) K)).eq]
      _ = GeneralLinearGroup.scalar (Fin N) c * ((B : GL (Fin N) K) *
            (A : GL (Fin N) K)) * (B : GL (Fin N) K)⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin N) c *
            ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) := by group
  have hconj : GeneralLinearGroup.scalar (Fin N) c *
      ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) =
      (A : GL (Fin N) K) := by
    rw [← hconj', ← h1]
    group
  let lam : Kˣ := c⁻¹
  have hrel : (B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin N) lam * (A : GL (Fin N) K) := by
    calc (B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹
        = (GeneralLinearGroup.scalar (Fin N) c)⁻¹ *
            (GeneralLinearGroup.scalar (Fin N) c *
              ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹)) := by
          group
      _ = (GeneralLinearGroup.scalar (Fin N) c)⁻¹ * (A : GL (Fin N) K) := by rw [hconj]
      _ = GeneralLinearGroup.scalar (Fin N) lam * (A : GL (Fin N) K) := by
          rw [show (GeneralLinearGroup.scalar (Fin N) c)⁻¹ =
            GeneralLinearGroup.scalar (Fin N) c⁻¹ by
              rw [← map_inv]]
  have htoLinScalar : (Matrix.GeneralLinearGroup.toLin
      (GeneralLinearGroup.scalar (Fin N) lam) : Module.End K (Fin N → K)) =
      (lam : K) • (1 : Module.End K (Fin N → K)) := by
    apply LinearMap.ext
    intro v
    simpa using toLin_scalar_apply lam v
  let yinv : Module.End K (Fin N → K) :=
    ↑((Matrix.GeneralLinearGroup.toLin (B : GL (Fin N) K))⁻¹)
  have hyinv : yinv * y = 1 := by
    simpa [y, yinv] using Units.inv_mul (Matrix.GeneralLinearGroup.toLin (B : GL (Fin N) K))
  have hyinv' : y * yinv = 1 := by
    simpa [y, yinv] using Units.mul_inv (Matrix.GeneralLinearGroup.toLin (B : GL (Fin N) K))
  have hrelEnd : y * x * yinv = (lam : K) • x := by
    have h' := congrArg (fun g : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin g : Module.End K (Fin N → K))) hrel
    rw [map_mul, map_mul, map_inv, map_mul] at h'
    simp only [Units.val_mul] at h'
    rw [htoLinScalar, smul_mul_assoc, one_mul] at h'
    simpa [x, y, yinv] using h'
  have hrelEnd' : y * x = (lam : K) • (x * y) := by
    calc y * x = (y * x * yinv) * y := by
          rw [mul_assoc, mul_assoc, hyinv, mul_one]
      _ = ((lam : K) • x) * y := by rw [hrelEnd]
      _ = (lam : K) • (x * y) := by rw [smul_mul_assoc]
  have hmap : ∀ u : Fin N → K,
      u ∈ primaryComponent x (X - C μ) → x (y u) = (lam⁻¹ * μ) • (y u) := by
    intro u hu
    have hxu : x u = μ • u :=
      (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hu
    have h' := congrArg (fun T : Module.End K (Fin N → K) => T u) hrelEnd'
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h'
    rw [hxu, map_smul] at h'
    have h'' := congrArg (fun w : Fin N → K => (lam : K)⁻¹ • w) h'
    simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using h''.symm
  have hμ0 : μ ≠ 0 := right_ne_zero_of_mul_eq_one hμ
  have hlam1 : lam = 1 := by
    by_contra hlam
    have hνne : lam⁻¹ * μ ≠ μ := by
      intro hν
      have h1 : (↑(lam⁻¹) : K) * μ = 1 * μ := by simpa using hν
      have h2 : (↑(lam⁻¹) : K) = 1 := mul_right_cancel₀ hμ0 h1
      have h2u : lam⁻¹ = 1 := Units.ext h2
      exact hlam (inv_eq_one.mp h2u)
    obtain ⟨v0, hv0, hv0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot H.squarefree ha)
    have hyinj : Function.Injective y :=
      Function.LeftInverse.injective (g := yinv) fun w =>
        congrArg (fun T : Module.End K (Fin N → K) => T w) hyinv
    have hyv0ne : y v0 ≠ 0 := fun h0 => hv0ne (hyinj (by simpa using h0))
    let ν : K := lam⁻¹ * μ
    have hνne' : ν ≠ μ := by simpa [ν] using hνne
    have heig : x.HasEigenvalue ν := by
      rw [Module.End.hasEigenvalue_iff]
      intro hbot
      have hmem : y v0 ∈ x.eigenspace ν := by
        rw [Module.End.mem_eigenspace_iff]
        exact hmap v0 hv0
      rw [hbot] at hmem
      exact hyv0ne (by simpa using hmem)
    have hbmem : (X - C ν) ∈ primaryFactors x :=
      CFSG.RankThree.PartOne.KCUnitaryScalar.X_sub_C_mem_primaryFactors heig
    let b : primaryFactors x := ⟨X - C ν, hbmem⟩
    have hbne : b ≠ ⟨X - C μ, ha⟩ := by
      intro hEq
      have hp : (X - C ν : K[X]) = X - C μ := congrArg Subtype.val hEq
      have hcoeff := congrArg (fun p : K[X] => p.coeff 0) hp
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero] at hcoeff
      exact hνne' (neg_inj.mp (by simpa using hcoeff))
    have hmν : primaryMultiplicity x (X - C ν) ≤ 1 :=
      primaryMultiplicity_le_one_of_ne h hq A rfl H hμ ha hm hunique b hbne
    have hdimμ : Module.finrank K (primaryComponent x (X - C μ)) = 3 := by
      rw [← CFSG.RankThree.PartOne.KCUnitaryScalar.primaryMultiplicity_X_sub_C x μ, hm]
    have hmνpos : 0 < primaryMultiplicity x (X - C ν) :=
      primaryMultiplicity_pos H.squarefree b
    have hdimν : Module.finrank K (primaryComponent x (X - C ν)) = 1 := by
      rw [← CFSG.RankThree.PartOne.KCUnitaryScalar.primaryMultiplicity_X_sub_C x ν]
      omega
    let e : (Fin N → K) ≃ₗ[K] (Fin N → K) :=
      { toFun := y
        invFun := yinv
        left_inv := fun u => congrArg (fun T : Module.End K (Fin N → K) => T u) hyinv
        right_inv := fun u => congrArg (fun T : Module.End K (Fin N → K) => T u) hyinv'
        map_add' := map_add y
        map_smul' := map_smul y }
    have hmaple : Submodule.map (e : (Fin N → K) →ₗ[K] (Fin N → K))
        (primaryComponent x (X - C μ)) ≤ primaryComponent x (X - C ν) := by
      intro w hw
      rw [Submodule.mem_map] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      rw [CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C]
      exact hmap u hu
    have hdimle := Submodule.finrank_mono hmaple
    rw [LinearEquiv.finrank_map_eq, hdimμ, hdimν] at hdimle
    omega
  have hBA : (B : GL (Fin N) K) * (A : GL (Fin N) K) = (A : GL (Fin N) K) * (B : GL (Fin N) K) := by
    have h := hrel
    rw [hlam1, map_one, one_mul] at h
    calc (B : GL (Fin N) K) * (A : GL (Fin N) K)
        = ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) *
            (B : GL (Fin N) K) := by group
      _ = (A : GL (Fin N) K) * (B : GL (Fin N) K) := by rw [h]
  exact hBA.symm

theorem exists_scalar_conj_eq_of_conjHom_commute {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) (hN : 4 ≤ N)
    (A B : primeFormUnitary h (idGram K N))
    (hc : Commute (primeFormConjHom h (idGram K N) A) (primeFormConjHom h (idGram K N) B)) :
    ∃ lam : Kˣ, (B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin N) lam * (A : GL (Fin N) K) := by
  classical
  haveI := h.finite
  have hn3 : 3 ≤ N := by omega
  have hne : ¬(N = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨rfl, hq2⟩
    omega
  let z : primeFormUnitary h (idGram K N) := (B * A)⁻¹ * (A * B)
  have hzρ : primeFormConjHom h (idGram K N) z = 1 := by
    change primeFormConjHom h (idGram K N) ((B * A)⁻¹ * (A * B)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hc.eq, inv_mul_cancel]
  obtain ⟨c, -, hzc⟩ := (mem_idScalarKernel (h := h) (n := N)).mp
    ((primeFormConjHom_eq_one_iff_of_ne hn3 hne z).mp hzρ)
  have hz' : (A : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) *
      (B : GL (Fin N) K) = GeneralLinearGroup.scalar (Fin N) c := by
    rw [← hzc]
    simp only [z, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h1 : (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) * (B : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) c * (A : GL (Fin N) K) := by
    calc (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) * (B : GL (Fin N) K)
        = (A : GL (Fin N) K) * ((A : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K)⁻¹ *
            (A : GL (Fin N) K) * (B : GL (Fin N) K)) := by group
      _ = (A : GL (Fin N) K) * GeneralLinearGroup.scalar (Fin N) c := by rw [hz']
      _ = GeneralLinearGroup.scalar (Fin N) c * (A : GL (Fin N) K) :=
          (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (A : GL (Fin N) K)).eq
  have hconj' : (B : GL (Fin N) K) * (GeneralLinearGroup.scalar (Fin N) c *
      (A : GL (Fin N) K)) * (B : GL (Fin N) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin N) c *
        ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) := by
    calc (B : GL (Fin N) K) * (GeneralLinearGroup.scalar (Fin N) c *
          (A : GL (Fin N) K)) * (B : GL (Fin N) K)⁻¹
        = ((B : GL (Fin N) K) * GeneralLinearGroup.scalar (Fin N) c) *
            (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin N) c * (B : GL (Fin N) K)) *
            (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (B : GL (Fin N) K)).eq]
      _ = GeneralLinearGroup.scalar (Fin N) c * ((B : GL (Fin N) K) *
            (A : GL (Fin N) K)) * (B : GL (Fin N) K)⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin N) c *
            ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) := by group
  have hconj : GeneralLinearGroup.scalar (Fin N) c *
      ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹) =
      (A : GL (Fin N) K) := by
    rw [← hconj', ← h1]
    group
  let lam : Kˣ := c⁻¹
  refine ⟨lam, ?_⟩
  calc (B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹
      = (GeneralLinearGroup.scalar (Fin N) c)⁻¹ *
          (GeneralLinearGroup.scalar (Fin N) c *
            ((B : GL (Fin N) K) * (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹)) := by
        group
    _ = (GeneralLinearGroup.scalar (Fin N) c)⁻¹ * (A : GL (Fin N) K) := by rw [hconj]
    _ = GeneralLinearGroup.scalar (Fin N) lam * (A : GL (Fin N) K) := by
        rw [show (GeneralLinearGroup.scalar (Fin N) c)⁻¹ =
          GeneralLinearGroup.scalar (Fin N) c⁻¹ by rw [← map_inv]]

theorem commute_of_commute_of_commute {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) (hN : 4 ≤ N)
    (h3 : 3 ∣ 2 ^ f + 1)
    (A A₁ A₂ : primeFormUnitary h (idGram K N)) {c : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    (hm : primaryMultiplicity
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
      (X - C μ) = 3)
    (htop : primaryComponent
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
      (X - C μ) ≠ ⊤)
    (hunique : ∀ T' : Subgroup (primeFormP h (idGram K N)),
      CFSG.Open.IsComponentOf T'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (primeFormConjHom h (idGram K N) A)) →
      T' = blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ))
    (hcA1 : Commute (primeFormConjHom h (idGram K N) A) (primeFormConjHom h (idGram K N) A₁))
    (hcA2 : Commute (primeFormConjHom h (idGram K N) A) (primeFormConjHom h (idGram K N) A₂))
    (hc12 : Commute (primeFormConjHom h (idGram K N) A₁) (primeFormConjHom h (idGram K N) A₂)) :
    Commute (A₁ : GL (Fin N) K) (A₂ : GL (Fin N) K) := by
  classical
  haveI := h.finite
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let y₁ : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A₁ : GL (Fin N) K)
  let y₂ : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A₂ : GL (Fin N) K)
  have H : UnitaryPrimaryData h.bar (idForm h N)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA
  have hcommA1 : Commute (A : GL (Fin N) K) (A₁ : GL (Fin N) K) :=
    commute_of_conjHom_commute h hq hN A A₁ (by simpa [x] using hA) hμ
      (by simpa [x] using ha) (by simpa [x] using hm) hunique hcA1
  have hcommA2 : Commute (A : GL (Fin N) K) (A₂ : GL (Fin N) K) :=
    commute_of_conjHom_commute h hq hN A A₂ (by simpa [x] using hA) hμ
      (by simpa [x] using ha) (by simpa [x] using hm) hunique hcA2
  have hxy1 : Commute y₁ x := by
    have h' := congrArg (fun z : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin z : Module.End K (Fin N → K))) hcommA1
    rw [map_mul, map_mul] at h'
    exact h'.symm
  have hxy2 : Commute y₂ x := by
    have h' := congrArg (fun z : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin z : Module.End K (Fin N → K))) hcommA2
    rw [map_mul, map_mul] at h'
    exact h'.symm
  let a : primaryFactors x := ⟨X - C μ, by simpa [x] using ha⟩
  have htop' : primaryComponent x (a : K[X]) ≠ ⊤ := by simpa [x, a] using htop
  obtain ⟨b, hbne⟩ := exists_ne_primaryFactor_of_primaryComponent_ne_top H htop'
  have hm_b_le : primaryMultiplicity x (b : K[X]) ≤ 1 :=
    primaryMultiplicity_le_one_of_ne h hq A rfl H hμ
      (by simpa [x] using ha) (by simpa [x] using hm) hunique b hbne
  obtain ⟨ν, hb_lin, -⟩ := exists_linear_of_mem_primaryFactors h h3 A
    (by simpa [x] using hA) (by simpa [x] using ha) b
  have hb_m_pos : 0 < primaryMultiplicity x (b : K[X]) :=
    primaryMultiplicity_pos H.squarefree b
  have hdim : Module.finrank K (primaryComponent x (b : K[X])) = 1 := by
    rw [hb_lin, ← CFSG.RankThree.PartOne.KCUnitaryScalar.primaryMultiplicity_X_sub_C x ν]
    have hle : primaryMultiplicity x (X - C ν) ≤ 1 := by simpa [hb_lin] using hm_b_le
    have hpos : 0 < primaryMultiplicity x (X - C ν) := by simpa [hb_lin] using hb_m_pos
    omega
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot H.squarefree b.2)
  let v' : primaryComponent x (b : K[X]) := ⟨v, hv⟩
  have hv'ne : v' ≠ 0 := fun h => hvne (congrArg Subtype.val h)
  have hspan : K ∙ v' = ⊤ := (finrank_eq_one_iff_of_nonzero v' hv'ne).mp hdim
  have hy1v : y₁ v ∈ primaryComponent x (b : K[X]) := apply_mem_primaryComponent hxy1 hv
  have hy2v : y₂ v ∈ primaryComponent x (b : K[X]) := apply_mem_primaryComponent hxy2 hv
  have hy1mem : (⟨y₁ v, hy1v⟩ : primaryComponent x (b : K[X])) ∈ K ∙ v' := by
    rw [hspan]
    exact Submodule.mem_top
  have hy2mem : (⟨y₂ v, hy2v⟩ : primaryComponent x (b : K[X])) ∈ K ∙ v' := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨s₁, hs₁'⟩ := Submodule.mem_span_singleton.mp hy1mem
  obtain ⟨s₂, hs₂'⟩ := Submodule.mem_span_singleton.mp hy2mem
  have hs₁ : s₁ • v = y₁ v := congrArg Subtype.val hs₁'
  have hs₂ : s₂ • v = y₂ v := congrArg Subtype.val hs₂'
  have hy1inj : Function.Injective y₁ := by
    intro a b hab
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin N → K)
      (Matrix.GeneralLinearGroup.toLin (A₁ : GL (Fin N) K))).injective hab
  have hy2inj : Function.Injective y₂ := by
    intro a b hab
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin N → K)
      (Matrix.GeneralLinearGroup.toLin (A₂ : GL (Fin N) K))).injective hab
  have hs1ne : s₁ ≠ 0 := by
    intro h0
    have hzero : y₁ v = 0 := by rw [← hs₁, h0, zero_smul]
    exact hvne (hy1inj (by simpa using hzero))
  have hs2ne : s₂ ≠ 0 := by
    intro h0
    have hzero : y₂ v = 0 := by rw [← hs₂, h0, zero_smul]
    exact hvne (hy2inj (by simpa using hzero))
  obtain ⟨lam, hlam⟩ := exists_scalar_conj_eq_of_conjHom_commute h hq hN A₁ A₂ hc12
  let y₂inv : Module.End K (Fin N → K) :=
    ↑((Matrix.GeneralLinearGroup.toLin (A₂ : GL (Fin N) K))⁻¹)
  have hy2inv : y₂inv * y₂ = 1 := by
    simpa [y₂, y₂inv] using Units.inv_mul (Matrix.GeneralLinearGroup.toLin (A₂ : GL (Fin N) K))
  have htoLinScalar2 : (Matrix.GeneralLinearGroup.toLin
      (GeneralLinearGroup.scalar (Fin N) lam) : Module.End K (Fin N → K)) =
      (lam : K) • (1 : Module.End K (Fin N → K)) := by
    apply LinearMap.ext
    intro w
    simpa using toLin_scalar_apply lam w
  have hrelEnd : y₂ * y₁ * y₂inv = (lam : K) • y₁ := by
    have h' := congrArg (fun g : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin g : Module.End K (Fin N → K))) hlam
    rw [map_mul, map_mul, map_inv, map_mul] at h'
    simp only [Units.val_mul] at h'
    rw [htoLinScalar2, smul_mul_assoc, one_mul] at h'
    simpa [y₁, y₂, y₂inv] using h'
  have hrelEnd' : y₂ * y₁ = (lam : K) • (y₁ * y₂) := by
    calc y₂ * y₁ = (y₂ * y₁ * y₂inv) * y₂ := by
          rw [mul_assoc, mul_assoc, hy2inv, mul_one]
      _ = ((lam : K) • y₁) * y₂ := by rw [hrelEnd]
      _ = (lam : K) • (y₁ * y₂) := by rw [smul_mul_assoc]
  have heval := congrArg (fun T : Module.End K (Fin N → K) => T v) hrelEnd'
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at heval
  have heval' : s₁ • (s₂ • v) = (lam : K) • (s₂ • (s₁ • v)) := by
    calc s₁ • (s₂ • v) = y₂ (y₁ v) := by rw [← hs₁, map_smul, ← hs₂]
      _ = (lam : K) • (y₁ (y₂ v)) := heval
      _ = (lam : K) • (s₂ • (s₁ • v)) := by rw [← hs₂, map_smul, ← hs₁]
  have h1 : (s₁ * s₂) • v = ((lam : K) * (s₂ * s₁)) • v := by
    simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using heval'
  have hzero : ((s₁ * s₂ - (lam : K) * (s₂ * s₁)) • v) = 0 := by
    rw [sub_smul, h1, sub_self]
  have hcoef : s₁ * s₂ = (lam : K) * (s₂ * s₁) :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hvne)
  have hcoef' : s₁ * s₂ = (lam : K) * (s₁ * s₂) := by
    simpa [mul_comm s₂ s₁] using hcoef
  have hprod : s₁ * s₂ ≠ 0 := mul_ne_zero hs1ne hs2ne
  have hlam1 : lam = 1 := by
    have h' : (1 : K) * (s₁ * s₂) = (lam : K) * (s₁ * s₂) := by
      rw [one_mul]
      exact hcoef'
    exact Units.ext (mul_right_cancel₀ hprod h').symm
  have hEnd : y₂ * y₁ = y₁ * y₂ := by
    rw [hlam1] at hrelEnd'
    simpa using hrelEnd'
  have hunits : Matrix.GeneralLinearGroup.toLin (A₂ : GL (Fin N) K) *
      Matrix.GeneralLinearGroup.toLin (A₁ : GL (Fin N) K) =
      Matrix.GeneralLinearGroup.toLin (A₁ : GL (Fin N) K) *
        Matrix.GeneralLinearGroup.toLin (A₂ : GL (Fin N) K) := by
    apply Units.ext
    simpa [y₁, y₂] using hEnd
  have hunits' : Matrix.GeneralLinearGroup.toLin
      ((A₂ : GL (Fin N) K) * (A₁ : GL (Fin N) K)) =
      Matrix.GeneralLinearGroup.toLin ((A₁ : GL (Fin N) K) * (A₂ : GL (Fin N) K)) := by
    rw [map_mul, map_mul]
    exact hunits
  have hGL : (A₂ : GL (Fin N) K) * (A₁ : GL (Fin N) K) =
      (A₁ : GL (Fin N) K) * (A₂ : GL (Fin N) K) :=
    Matrix.GeneralLinearGroup.toLin.injective hunits'
  exact hGL.symm

theorem toLin_pow_three_eq_smul_one {n : ℕ} {K : Type} [Field K]
    {B : GL (Fin n) K} {c : Kˣ}
    (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    (Matrix.GeneralLinearGroup.toLin B : Module.End K (Fin n → K)) ^ 3 =
      (c : K) • (1 : Module.End K (Fin n → K)) := by
  have hx3u : Matrix.GeneralLinearGroup.toLin B ^ 3 =
      Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin n) c) := by
    rw [← map_pow, hB]
  have h1 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (u : Module.End K (Fin n → K))) hx3u
  rw [← Units.val_pow_eq_pow_val, h1]
  apply LinearMap.ext
  intro v
  simpa using toLin_scalar_apply c v

theorem pow_three_eq_of_mem_primaryFactors {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    (A : primeFormUnitary h (idGram K N)) {c : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {μ : K} (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))) :
    μ ^ 3 = (c : K) := by
  classical
  haveI := h.finite
  let x : LinearMap.GeneralLinearGroup K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  have H : UnitaryPrimaryData h.bar (idForm h N) x :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA
  have hne : primaryComponent (x : Module.End K (Fin N → K)) (X - C μ) ≠ ⊥ :=
    primaryComponent_ne_bot H.squarefree ha
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxv : (x : Module.End K (Fin N → K)) v = μ • v :=
    (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hv
  have h1 : ((x : Module.End K (Fin N → K)) ^ 3) v = (μ ^ 3) • v := by
    rw [pow_three]
    simp only [Module.End.mul_apply, map_smul, hxv, smul_smul]
    ring_nf
  have hx3 := toLin_pow_three_eq_smul_one (n := N) hA
  have h2 : ((x : Module.End K (Fin N → K)) ^ 3) v = (c : K) • v := by
    rw [hx3]
    rfl
  have h3 : ((μ ^ 3 - (c : K)) • v) = 0 := by
    rw [sub_smul, ← h1, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hvne)

theorem norm_eq_one_of_pow_three_eq {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h3 : 3 ∣ 2 ^ f + 1) {s c : K}
    (hs3 : s ^ 3 = c) (hc : h.bar c * c = 1) :
    h.bar s * s = 1 := by
  classical
  haveI := h.finite
  have hqmod : 2 ^ f % 3 = 2 := by
    have hq0 : (2 ^ f + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    have hqlt : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h : (2 ^ f % 3 + 1) % 3 = 0 := by
      simpa [Nat.add_mod] using hq0
    interval_cases hq : 2 ^ f % 3 <;> simp [hq] at h ⊢
  have hcn : h.norm c = 1 := by
    simpa [UnitaryFieldData.norm, mul_comm] using hc
  let x : h.fixedField := ⟨h.norm s, h.norm_mem_fixedField s⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (h.norm s) ^ 3 = 1
    calc (h.norm s) ^ 3 = (s ^ (2 ^ f + 1)) ^ 3 := by
          rw [UnitaryFieldData.norm_eq_pow]
      _ = s ^ ((2 ^ f + 1) * 3) := by rw [pow_mul]
      _ = s ^ (3 * (2 ^ f + 1)) := by rw [Nat.mul_comm]
      _ = (s ^ 3) ^ (2 ^ f + 1) := by rw [pow_mul]
      _ = c ^ (2 ^ f + 1) := by rw [hs3]
      _ = h.norm c := by rw [UnitaryFieldData.norm_eq_pow]
      _ = 1 := hcn
  have hx0 : x ≠ 0 := by
    intro h0
    have hzero : x ^ 3 = 0 := by rw [h0]; ring
    rw [hx3] at hzero
    exact one_ne_zero hzero
  let u : h.fixedFieldˣ := Units.mk0 x hx0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    change (x : h.fixedField) ^ 3 = 1
    exact hx3
  haveI : Fintype h.fixedField := Fintype.ofFinite h.fixedField
  have hum : u ^ (Nat.card h.fixedField - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (u : h.fixedField) (Units.ne_zero u)
    rw [← Nat.card_eq_fintype_card] at h
    exact Units.ext h
  have hm3 : ¬ 3 ∣ Nat.card h.fixedField - 1 := by
    rw [h.card_fixedField]
    have hq2 : 2 ≤ 2 ^ f := by
      have hf0 : f ≠ 0 := Nat.one_le_iff_ne_zero.mp h.one_le
      have := Nat.one_lt_pow hf0 (by norm_num : 1 < 2)
      omega
    omega
  have hcop : Nat.Coprime (Nat.card h.fixedField - 1) 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
  have h1 : u ^ Nat.gcd (Nat.card h.fixedField - 1) 3 = 1 :=
    pow_gcd_eq_one.mpr ⟨hum, hu3⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  have hx1 : x = 1 := by
    have := congrArg Units.val h1
    simpa [u] using this
  have hns : h.norm s = 1 := congrArg Subtype.val hx1
  simpa [UnitaryFieldData.norm, mul_comm] using hns

theorem exists_scalar_of_commute {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) (hN : 4 ≤ N)
    (h3 : 3 ∣ 2 ^ f + 1)
    (A B : primeFormUnitary h (idGram K N)) {c cB : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hB : (B : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) cB)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    (hm : primaryMultiplicity
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
      (X - C μ) = 3)
    (htop : primaryComponent
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
      (X - C μ) ≠ ⊤)
    (hunique : ∀ T' : Subgroup (primeFormP h (idGram K N)),
      CFSG.Open.IsComponentOf T'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (primeFormConjHom h (idGram K N) A)) →
      T' = blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ))
    (hcomm : Commute (A : GL (Fin N) K) (B : GL (Fin N) K)) :
    ∃ s : Kˣ, s ^ 3 = cB ∧ h.bar s * s = 1 := by
  classical
  haveI := h.finite
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let y : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (B : GL (Fin N) K)
  have H : UnitaryPrimaryData h.bar (idForm h N)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA
  have hxy : Commute y x := by
    have h' := congrArg (fun z : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin z : Module.End K (Fin N → K))) hcomm
    rw [map_mul, map_mul] at h'
    exact h'.symm
  let a : primaryFactors x := ⟨X - C μ, by simpa [x] using ha⟩
  have htop' : primaryComponent x (a : K[X]) ≠ ⊤ := by simpa [x, a] using htop
  obtain ⟨b, hbne⟩ := exists_ne_primaryFactor_of_primaryComponent_ne_top H htop'
  have hm_b_le : primaryMultiplicity x (b : K[X]) ≤ 1 :=
    primaryMultiplicity_le_one_of_ne h hq A rfl H hμ
      (by simpa [x] using ha) (by simpa [x] using hm) hunique b hbne
  obtain ⟨ν, hb_lin, -⟩ := exists_linear_of_mem_primaryFactors h h3 A
    (by simpa [x] using hA) (by simpa [x] using ha) b
  have hb_m_pos : 0 < primaryMultiplicity x (b : K[X]) :=
    primaryMultiplicity_pos H.squarefree b
  have hdim : Module.finrank K (primaryComponent x (b : K[X])) = 1 := by
    rw [hb_lin, ← CFSG.RankThree.PartOne.KCUnitaryScalar.primaryMultiplicity_X_sub_C x ν]
    have hle : primaryMultiplicity x (X - C ν) ≤ 1 := by simpa [hb_lin] using hm_b_le
    have hpos : 0 < primaryMultiplicity x (X - C ν) := by simpa [hb_lin] using hb_m_pos
    omega
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot H.squarefree b.2)
  let v' : primaryComponent x (b : K[X]) := ⟨v, hv⟩
  have hv'ne : v' ≠ 0 := fun h => hvne (congrArg Subtype.val h)
  have hspan : K ∙ v' = ⊤ := (finrank_eq_one_iff_of_nonzero v' hv'ne).mp hdim
  have hyv : y v ∈ primaryComponent x (b : K[X]) := apply_mem_primaryComponent hxy hv
  have hymem : (⟨y v, hyv⟩ : primaryComponent x (b : K[X])) ∈ K ∙ v' := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp hymem
  have hs : s • v = y v := congrArg Subtype.val hs'
  have hyv' : y v = s • v := hs.symm
  have hy3 : (y : Module.End K (Fin N → K)) ^ 3 =
      (cB : K) • (1 : Module.End K (Fin N → K)) :=
    toLin_pow_three_eq_smul_one hB
  have hs3 : s ^ 3 = (cB : K) := by
    have h1 : ((y : Module.End K (Fin N → K)) ^ 3) v = (s ^ 3) • v := by
      rw [pow_three]
      simp only [Module.End.mul_apply, map_smul, hyv', smul_smul]
      ring_nf
    have h2 : ((y : Module.End K (Fin N → K)) ^ 3) v = (cB : K) • v := by
      rw [hy3]
      rfl
    have h3 : ((s ^ 3 - (cB : K)) • v) = 0 := by
      rw [sub_smul, ← h1, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hvne)
  have hcB_norm : h.norm (cB : K) = 1 := by
    have hmem : GeneralLinearGroup.scalar (Fin N) cB ∈ primeFormUnitary h (idGram K N) := by
      rw [← hB]
      exact pow_mem B.2 3
    exact norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) (1 : GL (Fin N) K) hmem
  have hcB : h.bar (cB : K) * (cB : K) = 1 := by
    simpa [UnitaryFieldData.norm, mul_comm] using hcB_norm
  have hnorm_s : h.bar s * s = 1 :=
    norm_eq_one_of_pow_three_eq h h3 hs3 hcB
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0] at hnorm_s
    norm_num at hnorm_s
  refine ⟨Units.mk0 s hsne, ?_, hnorm_s⟩
  ext
  exact hs3

theorem finrank_eigenspace_diagonal {n : ℕ} {K : Type} [Field K]
    (d : Fin n → K) (μ : K) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' (Matrix.diagonal d)) μ) =
      (Finset.univ.filter fun i => d i = μ).card := by
  classical
  let w : Fin n → K := fun i => d i - μ
  have hker : Module.End.eigenspace (Matrix.toLin' (Matrix.diagonal d)) μ =
      LinearMap.ker (Matrix.toLin' (Matrix.diagonal w)) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.toLin'_apply]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hi
      rw [Matrix.mulVec_diagonal, sub_mul, hi, sub_self]
      rfl
    · intro h
      funext i
      have hi := congrFun h i
      rw [Matrix.mulVec_diagonal, Pi.zero_apply] at hi
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      linear_combination hi
  rw [hker]
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (Matrix.diagonal w))
  rw [Module.finrank_fin_fun] at hrank
  have hr : Module.finrank K (LinearMap.range (Matrix.toLin' (Matrix.diagonal w))) =
      Fintype.card {i // w i ≠ 0} := by
    rw [← Matrix.rank_diagonal w]
    rfl
  have hc : Fintype.card {i // w i ≠ 0} =
      n - (Finset.univ.filter fun i => d i = μ).card := by
    have hcard : Fintype.card {i // w i ≠ 0} =
        Fintype.card {i // i ∉ Finset.univ.filter (fun i => d i = μ)} := by
      apply Fintype.card_congr
      refine Equiv.subtypeEquivRight ?_
      intro i
      simp [w, sub_ne_zero, Finset.mem_filter]
    rw [hcard, Fintype.card_subtype_compl, Fintype.card_fin]
    simp only [Fintype.card_subtype]
    simp
  have hfil : (Finset.univ.filter fun i => d i = μ).card ≤ n := by
    simpa using Finset.card_le_univ (Finset.univ.filter fun i => d i = μ)
  rw [hr, hc] at hrank
  omega

theorem finrank_eigenspace_conj {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (T : Module.End K V) (μ : K) :
    Module.finrank K (Module.End.eigenspace (e.symm.conj T) μ) =
      Module.finrank K (Module.End.eigenspace T μ) := by
  let f : Module.End.eigenspace (e.symm.conj T) μ ≃ₗ[K] Module.End.eigenspace T μ :=
    { toFun := fun v => ⟨e v, by
        refine (Module.End.mem_eigenspace_iff).2 ?_
        have hv : e.symm.conj T v.1 = μ • v.1 :=
          (Module.End.mem_eigenspace_iff).1 v.2
        have hv' := congrArg e hv
        simpa [LinearEquiv.conj_apply] using hv'⟩
      invFun := fun v => ⟨e.symm v, by
        refine (Module.End.mem_eigenspace_iff).2 ?_
        have hv : T v.1 = μ • v.1 := (Module.End.mem_eigenspace_iff).1 v.2
        have hv' := congrArg e.symm hv
        simpa [LinearEquiv.conj_apply] using hv'⟩
      left_inv := fun v => by ext; simp
      right_inv := fun v => by ext; simp
      map_add' := fun v w => by ext; simp
      map_smul' := fun c v => by ext; simp }
  exact LinearEquiv.finrank_eq f

theorem exists_diagonal_of_unique {f N : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (hf : 2 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    (A A₁ A₂ : primeFormUnitary h (idGram K N)) {c c₁ c₂ : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hA₁ : (A₁ : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c₁)
    (hA₂ : (A₂ : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c₂)
    (hc₁ : Commute (primeFormConjHom h (idGram K N) A) (primeFormConjHom h (idGram K N) A₁))
    (hc₂ : Commute (primeFormConjHom h (idGram K N) A) (primeFormConjHom h (idGram K N) A₂))
    (hc₁₂ : Commute (primeFormConjHom h (idGram K N) A₁) (primeFormConjHom h (idGram K N) A₂))
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    (hm : primaryMultiplicity
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) :
        Module.End K (Fin N → K))) (X - C μ) = 3)
    (htop : primaryComponent
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) :
        Module.End K (Fin N → K))) (X - C μ) ≠ ⊤)
    (hunique : ∀ T' : Subgroup (primeFormP h (idGram K N)),
      CFSG.Open.IsComponentOf T'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (primeFormConjHom h (idGram K N) A)) →
      T' = blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ)) :
    ∃ (P : primeFormUnitary h (idGram K N)) (d e₁ e₂ : Fin N → K),
      (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = Matrix.diagonal d ∧
      (((P⁻¹ * A₁ * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = Matrix.diagonal e₁ ∧
      (((P⁻¹ * A₂ * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = Matrix.diagonal e₂ ∧
      (Finset.univ.filter fun r => d r = μ).card = 3 := by
  classical
  haveI := h.finite
  have hq : 4 ≤ 2 ^ f := by
    have h := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hf
    norm_num at h
    exact h
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  have H : UnitaryPrimaryData h.bar (idForm h N)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA
  have hN : 4 ≤ N := by
    have hfr : Module.finrank K (primaryComponent x (X - C μ)) = 3 := by
      rw [← CFSG.RankThree.PartOne.KCUnitaryScalar.primaryMultiplicity_X_sub_C x μ]
      exact hm
    have hlt := Submodule.finrank_lt (s := primaryComponent x (X - C μ))
      (by simpa [x] using htop)
    rw [Module.finrank_fin_fun, hfr] at hlt
    omega
  have hμ3 : μ ^ 3 = (c : K) := pow_three_eq_of_mem_primaryFactors h A hA ha
  have hcommA1 : Commute (A : GL (Fin N) K) (A₁ : GL (Fin N) K) :=
    commute_of_conjHom_commute h hq hN A A₁ hA hμ ha hm hunique hc₁
  have hcommA2 : Commute (A : GL (Fin N) K) (A₂ : GL (Fin N) K) :=
    commute_of_conjHom_commute h hq hN A A₂ hA hμ ha hm hunique hc₂
  have hcomm12 : Commute (A₁ : GL (Fin N) K) (A₂ : GL (Fin N) K) :=
    commute_of_commute_of_commute h hq hN h3 A A₁ A₂ hA hμ ha hm htop hunique
      hc₁ hc₂ hc₁₂
  obtain ⟨s₁, hs₁cube, hs₁norm⟩ :=
    exists_scalar_of_commute h hq hN h3 A A₁ hA hA₁ hμ ha hm htop hunique hcommA1
  obtain ⟨s₂, hs₂cube, hs₂norm⟩ :=
    exists_scalar_of_commute h hq hN h3 A A₂ hA hA₂ hμ ha hm htop hunique hcommA2
  have hμ0 : μ ≠ 0 := right_ne_zero_of_mul_eq_one hμ
  let mu : Kˣ := Units.mk0 μ hμ0
  have hmu3 : (mu : K) ^ 3 = (c : K) := by simpa [mu] using hμ3
  have hmu3u : mu ^ 3 = c := Units.ext (by simpa using hmu3)
  have hnormμ : h.norm (mu : K) = 1 := by
    simpa [UnitaryFieldData.norm, mul_comm, mu] using hμ
  have hnormμinv : h.norm ((mu⁻¹ : Kˣ) : K) = 1 := by
    rw [UnitaryFieldData.norm_eq_pow h, Units.val_inv_eq_inv_val, inv_pow,
      ← UnitaryFieldData.norm_eq_pow h, hnormμ, inv_one]
  have hnorm₁ : h.norm (s₁ : K) = 1 := by
    simpa [UnitaryFieldData.norm, mul_comm] using hs₁norm
  have hnorm₁inv : h.norm ((s₁⁻¹ : Kˣ) : K) = 1 := by
    rw [UnitaryFieldData.norm_eq_pow h, Units.val_inv_eq_inv_val, inv_pow,
      ← UnitaryFieldData.norm_eq_pow h, hnorm₁, inv_one]
  have hnorm₂ : h.norm (s₂ : K) = 1 := by
    simpa [UnitaryFieldData.norm, mul_comm] using hs₂norm
  have hnorm₂inv : h.norm ((s₂⁻¹ : Kˣ) : K) = 1 := by
    rw [UnitaryFieldData.norm_eq_pow h, Units.val_inv_eq_inv_val, inv_pow,
      ← UnitaryFieldData.norm_eq_pow h, hnorm₂, inv_one]
  have hscalarμ : GeneralLinearGroup.scalar (Fin N) mu⁻¹ ∈ primeFormUnitary h (idGram K N) :=
    scalar_mem_primeFormUnitary_one h hnormμinv
  have hscalar₁ : GeneralLinearGroup.scalar (Fin N) s₁⁻¹ ∈ primeFormUnitary h (idGram K N) :=
    scalar_mem_primeFormUnitary_one h hnorm₁inv
  have hscalar₂ : GeneralLinearGroup.scalar (Fin N) s₂⁻¹ ∈ primeFormUnitary h (idGram K N) :=
    scalar_mem_primeFormUnitary_one h hnorm₂inv
  let A' : primeFormUnitary h (idGram K N) :=
    ⟨GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K), mul_mem hscalarμ A.2⟩
  let A₁' : primeFormUnitary h (idGram K N) :=
    ⟨GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K), mul_mem hscalar₁ A₁.2⟩
  let A₂' : primeFormUnitary h (idGram K N) :=
    ⟨GeneralLinearGroup.scalar (Fin N) s₂⁻¹ * (A₂ : GL (Fin N) K), mul_mem hscalar₂ A₂.2⟩
  have hA'3 : (A' : GL (Fin N) K) ^ 3 = 1 := by
    change (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K)) ^ 3 = 1
    rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar mu⁻¹ (A : GL (Fin N) K)).symm.mul_pow,
      hA, ← map_pow, ← map_mul]
    congr 1
    rw [inv_pow, hmu3u, inv_mul_cancel, map_one]
  have hA₁'3 : (A₁' : GL (Fin N) K) ^ 3 = 1 := by
    change (GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K)) ^ 3 = 1
    rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₁⁻¹ (A₁ : GL (Fin N) K)).symm.mul_pow,
      hA₁, ← map_pow, ← map_mul]
    congr 1
    rw [inv_pow, hs₁cube, inv_mul_cancel, map_one]
  have hA₂'3 : (A₂' : GL (Fin N) K) ^ 3 = 1 := by
    change (GeneralLinearGroup.scalar (Fin N) s₂⁻¹ * (A₂ : GL (Fin N) K)) ^ 3 = 1
    rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₂⁻¹ (A₂ : GL (Fin N) K)).symm.mul_pow,
      hA₂, ← map_pow, ← map_mul]
    congr 1
    rw [inv_pow, hs₂cube, inv_mul_cancel, map_one]
  have hcommA'A₁' : Commute (A' : GL (Fin N) K) (A₁' : GL (Fin N) K) := by
    change Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
      (GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K))
    have hsc : Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹)
        (GeneralLinearGroup.scalar (Fin N) s₁⁻¹) :=
      CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₁⁻¹
        (GeneralLinearGroup.scalar (Fin N) mu⁻¹)
    have h1 : Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
        (GeneralLinearGroup.scalar (Fin N) s₁⁻¹) :=
      Commute.mul_left hsc
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₁⁻¹ (A : GL (Fin N) K))
    have h2 : Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
        (A₁ : GL (Fin N) K) :=
      Commute.mul_left
        ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar mu⁻¹ (A₁ : GL (Fin N) K)).symm)
        hcommA1
    exact Commute.mul_right h1 h2
  have hcommA'A₂' : Commute (A' : GL (Fin N) K) (A₂' : GL (Fin N) K) := by
    change Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
      (GeneralLinearGroup.scalar (Fin N) s₂⁻¹ * (A₂ : GL (Fin N) K))
    have hsc : Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹)
        (GeneralLinearGroup.scalar (Fin N) s₂⁻¹) :=
      CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₂⁻¹
        (GeneralLinearGroup.scalar (Fin N) mu⁻¹)
    have h1 : Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
        (GeneralLinearGroup.scalar (Fin N) s₂⁻¹) :=
      Commute.mul_left hsc
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₂⁻¹ (A : GL (Fin N) K))
    have h2 : Commute (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
        (A₂ : GL (Fin N) K) :=
      Commute.mul_left
        ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar mu⁻¹ (A₂ : GL (Fin N) K)).symm)
        hcommA2
    exact Commute.mul_right h1 h2
  have hcommA₁'A₂' : Commute (A₁' : GL (Fin N) K) (A₂' : GL (Fin N) K) := by
    change Commute (GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K))
      (GeneralLinearGroup.scalar (Fin N) s₂⁻¹ * (A₂ : GL (Fin N) K))
    have hsc : Commute (GeneralLinearGroup.scalar (Fin N) s₁⁻¹)
        (GeneralLinearGroup.scalar (Fin N) s₂⁻¹) :=
      CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₂⁻¹
        (GeneralLinearGroup.scalar (Fin N) s₁⁻¹)
    have h1 : Commute (GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K))
        (GeneralLinearGroup.scalar (Fin N) s₂⁻¹) :=
      Commute.mul_left hsc
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₂⁻¹ (A₁ : GL (Fin N) K))
    have h2 : Commute (GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K))
        (A₂ : GL (Fin N) K) :=
      Commute.mul_left
        ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₁⁻¹ (A₂ : GL (Fin N) K)).symm)
        hcomm12
    exact Commute.mul_right h1 h2
  let E : Set (GL (Fin N) K) := {(A' : GL (Fin N) K), (A₁' : GL (Fin N) K),
    (A₂' : GL (Fin N) K)}
  have hEU : ∀ z ∈ E, z ∈ primeFormUnitary h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · simpa [idGram] using A'.2
    · simpa [idGram] using A₁'.2
    · simpa [idGram] using A₂'.2
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro z hz w hw
    rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact (Commute.refl _).eq
    · exact hcommA'A₁'.eq
    · exact hcommA'A₂'.eq
    · exact hcommA'A₁'.symm.eq
    · exact (Commute.refl _).eq
    · exact hcommA₁'A₂'.eq
    · exact hcommA'A₂'.symm.eq
    · exact hcommA₁'A₂'.symm.eq
    · exact (Commute.refl _).eq
  have hE3 : ∀ z ∈ E, z ^ 3 = 1 := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hA'3
    · exact hA₁'3
    · exact hA₂'3
  obtain ⟨P, hPU, hPdiag⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj h h3 E hEU hEc hE3
  let P' : primeFormUnitary h (idGram K N) :=
    ⟨(P : GL (Fin N) K), by simpa [idGram] using hPU⟩
  have hPdiag' : ∀ z ∈ E,
      ((((P' : GL (Fin N) K)⁻¹ * z * (P' : GL (Fin N) K)) :
        Matrix (Fin N) (Fin N) K)).IsDiag := by
    intro z hz
    simpa [P'] using hPdiag z hz
  let D' : Matrix (Fin N) (Fin N) K :=
    (((P'⁻¹ * A' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K)
  let D₁' : Matrix (Fin N) (Fin N) K :=
    (((P'⁻¹ * A₁' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K)
  let D₂' : Matrix (Fin N) (Fin N) K :=
    (((P'⁻¹ * A₂' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K)
  let d' : Fin N → K := fun i => D' i i
  let d₁' : Fin N → K := fun i => D₁' i i
  let d₂' : Fin N → K := fun i => D₂' i i
  have hD'diag : D' = Matrix.diagonal d' := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d', Matrix.diagonal_apply]
    · rw [Matrix.diagonal_apply, if_neg hij]
      simpa [D'] using hPdiag' (A' : GL (Fin N) K) (by simp [E]) hij
  have hD₁'diag : D₁' = Matrix.diagonal d₁' := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d₁', Matrix.diagonal_apply]
    · rw [Matrix.diagonal_apply, if_neg hij]
      simpa [D₁'] using hPdiag' (A₁' : GL (Fin N) K) (by simp [E]) hij
  have hD₂'diag : D₂' = Matrix.diagonal d₂' := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d₂', Matrix.diagonal_apply]
    · rw [Matrix.diagonal_apply, if_neg hij]
      simpa [D₂'] using hPdiag' (A₂' : GL (Fin N) K) (by simp [E]) hij
  let d : Fin N → K := fun i => (mu : K) * d' i
  let e₁ : Fin N → K := fun i => (s₁ : K) * d₁' i
  let e₂ : Fin N → K := fun i => (s₂ : K) * d₂' i
  have hAeq : (A : GL (Fin N) K) = GeneralLinearGroup.scalar (Fin N) mu * (A' : GL (Fin N) K) := by
    change (A : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) mu *
        (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hA₁eq : (A₁ : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) s₁ * (A₁' : GL (Fin N) K) := by
    change (A₁ : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) s₁ *
        (GeneralLinearGroup.scalar (Fin N) s₁⁻¹ * (A₁ : GL (Fin N) K))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hA₂eq : (A₂ : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) s₂ * (A₂' : GL (Fin N) K) := by
    change (A₂ : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) s₂ *
        (GeneralLinearGroup.scalar (Fin N) s₂⁻¹ * (A₂ : GL (Fin N) K))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hMA : ((P'⁻¹ * A * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) mu *
        (((P'⁻¹ * A' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) := by
    let Pg : GL (Fin N) K := P'
    let S : GL (Fin N) K := GeneralLinearGroup.scalar (Fin N) mu
    change Pg⁻¹ * (A : GL (Fin N) K) * Pg =
      S * (Pg⁻¹ * (A' : GL (Fin N) K) * Pg)
    rw [hAeq]
    calc Pg⁻¹ * (S * (A' : GL (Fin N) K)) * Pg
        = (Pg⁻¹ * S) * (A' : GL (Fin N) K) * Pg := by group
      _ = (S * Pg⁻¹) * (A' : GL (Fin N) K) * Pg := by
          rw [(Commute.inv_right
            ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar mu Pg).symm)).symm.eq]
      _ = S * (Pg⁻¹ * (A' : GL (Fin N) K) * Pg) := by group
  have hMA₁ : ((P'⁻¹ * A₁ * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) s₁ *
        (((P'⁻¹ * A₁' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) := by
    let Pg : GL (Fin N) K := P'
    let S : GL (Fin N) K := GeneralLinearGroup.scalar (Fin N) s₁
    change Pg⁻¹ * (A₁ : GL (Fin N) K) * Pg =
      S * (Pg⁻¹ * (A₁' : GL (Fin N) K) * Pg)
    rw [hA₁eq]
    calc Pg⁻¹ * (S * (A₁' : GL (Fin N) K)) * Pg
        = (Pg⁻¹ * S) * (A₁' : GL (Fin N) K) * Pg := by group
      _ = (S * Pg⁻¹) * (A₁' : GL (Fin N) K) * Pg := by
          rw [(Commute.inv_right
            ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₁ Pg).symm)).symm.eq]
      _ = S * (Pg⁻¹ * (A₁' : GL (Fin N) K) * Pg) := by group
  have hMA₂ : ((P'⁻¹ * A₂ * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
      GeneralLinearGroup.scalar (Fin N) s₂ *
        (((P'⁻¹ * A₂' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) := by
    let Pg : GL (Fin N) K := P'
    let S : GL (Fin N) K := GeneralLinearGroup.scalar (Fin N) s₂
    change Pg⁻¹ * (A₂ : GL (Fin N) K) * Pg =
      S * (Pg⁻¹ * (A₂' : GL (Fin N) K) * Pg)
    rw [hA₂eq]
    calc Pg⁻¹ * (S * (A₂' : GL (Fin N) K)) * Pg
        = (Pg⁻¹ * S) * (A₂' : GL (Fin N) K) * Pg := by group
      _ = (S * Pg⁻¹) * (A₂' : GL (Fin N) K) * Pg := by
          rw [(Commute.inv_right
            ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s₂ Pg).symm)).symm.eq]
      _ = S * (Pg⁻¹ * (A₂' : GL (Fin N) K) * Pg) := by group
  have hMAmat : (((P'⁻¹ * A * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d := by
    rw [hMA, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change (Matrix.diagonal fun _ => (mu : K)) * D' = Matrix.diagonal d
    rw [hD'diag, Matrix.diagonal_mul_diagonal]
  have hMA₁mat : (((P'⁻¹ * A₁ * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal e₁ := by
    rw [hMA₁, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change (Matrix.diagonal fun _ => (s₁ : K)) * D₁' = Matrix.diagonal e₁
    rw [hD₁'diag, Matrix.diagonal_mul_diagonal]
  have hMA₂mat : (((P'⁻¹ * A₂ * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal e₂ := by
    rw [hMA₂, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change (Matrix.diagonal fun _ => (s₂ : K)) * D₂' = Matrix.diagonal e₂
    rw [hD₂'diag, Matrix.diagonal_mul_diagonal]
  have hcount_d' : (Finset.univ.filter fun i => d' i = 1).card = 3 := by
    have hdimD : Module.finrank K (Module.End.eigenspace (Matrix.toLin' D') 1) =
        (Finset.univ.filter fun i => d' i = 1).card := by
      rw [hD'diag]
      exact finrank_eigenspace_diagonal d' 1
    have hdimD3 : Module.finrank K (Module.End.eigenspace (Matrix.toLin' D') 1) = 3 := by
      let e : (Fin N → K) ≃ₗ[K] (Fin N → K) :=
        { toFun := (Matrix.GeneralLinearGroup.toLin (P' : GL (Fin N) K) :
            Module.End K (Fin N → K))
          invFun := (Matrix.GeneralLinearGroup.toLin ((P' : GL (Fin N) K)⁻¹) :
            Module.End K (Fin N → K))
          left_inv := by
            intro v
            have h : (↑(Matrix.GeneralLinearGroup.toLin ((P' : GL (Fin N) K)⁻¹)) :
                Module.End K (Fin N → K)) *
                (↑(Matrix.GeneralLinearGroup.toLin (P' : GL (Fin N) K)) :
                  Module.End K (Fin N → K)) = 1 := by
              simpa using Units.inv_mul (Matrix.GeneralLinearGroup.toLin (P' : GL (Fin N) K))
            exact congrArg (fun T : Module.End K (Fin N → K) => T v) h
          right_inv := by
            intro v
            have h : (↑(Matrix.GeneralLinearGroup.toLin (P' : GL (Fin N) K)) :
                Module.End K (Fin N → K)) *
                (↑(Matrix.GeneralLinearGroup.toLin ((P' : GL (Fin N) K)⁻¹)) :
                  Module.End K (Fin N → K)) = 1 := by
              simpa using Units.mul_inv (Matrix.GeneralLinearGroup.toLin (P' : GL (Fin N) K))
            exact congrArg (fun T : Module.End K (Fin N → K) => T v) h
          map_add' := map_add _
          map_smul' := map_smul _ }
      have hconj : (Matrix.GeneralLinearGroup.toLin
          ((P'⁻¹ * A' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
            Module.End K (Fin N → K)) =
          e.symm.conj (Matrix.GeneralLinearGroup.toLin (A' : GL (Fin N) K)) := by
        apply LinearMap.ext
        intro v
        change (Matrix.GeneralLinearGroup.toLin
            ((P'⁻¹ * A' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
              Module.End K (Fin N → K)) v =
          e.symm ((Matrix.GeneralLinearGroup.toLin (A' : GL (Fin N) K) :
            Module.End K (Fin N → K)) (e v))
        dsimp only [e]
        rw [LinearEquiv.coe_symm_mk]
        simp [Matrix.GeneralLinearGroup.toLin_apply, map_mul]
      have htoLinD' : Matrix.toLin' D' =
          (Matrix.GeneralLinearGroup.toLin
            ((P'⁻¹ * A' * P' : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
            Module.End K (Fin N → K)) := by
        apply LinearMap.ext
        intro v
        rw [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.toLin_apply]
        rfl
      have htoLinScalar : (Matrix.GeneralLinearGroup.toLin
          (GeneralLinearGroup.scalar (Fin N) mu⁻¹) : Module.End K (Fin N → K)) =
          ((mu⁻¹ : Kˣ) : K) • (1 : Module.End K (Fin N → K)) := by
        apply LinearMap.ext
        intro v
        simpa using toLin_scalar_apply mu⁻¹ v
      have htoLinA' : (Matrix.GeneralLinearGroup.toLin (A' : GL (Fin N) K) :
          Module.End K (Fin N → K)) = ((mu⁻¹ : Kˣ) : K) • x := by
        change (Matrix.GeneralLinearGroup.toLin
          (GeneralLinearGroup.scalar (Fin N) mu⁻¹ * (A : GL (Fin N) K)) :
          Module.End K (Fin N → K)) = ((mu⁻¹ : Kˣ) : K) • x
        rw [map_mul, Units.val_mul, htoLinScalar, smul_mul_assoc, one_mul]
      have heig : Module.End.eigenspace (((mu⁻¹ : Kˣ) : K) • x) 1 =
          Module.End.eigenspace x μ := by
        ext v
        rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
          LinearMap.smul_apply, one_smul]
        constructor
        · intro h
          have h' := congrArg (fun w => (mu : K) • w) h
          simpa [smul_smul, mu, mul_inv_cancel₀ hμ0] using h'
        · intro h
          rw [h]
          simpa [mu, smul_smul] using congrArg (fun c : K => c • v) (Units.inv_mul mu)
      have hdimx : Module.finrank K (Module.End.eigenspace x μ) = 3 := by
        have hpc : primaryComponent x (X - C μ) = Module.End.eigenspace x μ := by
          ext v
          rw [CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C,
            Module.End.mem_eigenspace_iff]
        rw [← hpc, ← CFSG.RankThree.PartOne.KCUnitaryScalar.primaryMultiplicity_X_sub_C x μ]
        exact hm
      rw [htoLinD', hconj, finrank_eigenspace_conj, htoLinA', heig]
      exact hdimx
    rw [← hdimD]
    exact hdimD3
  have hfilter : (Finset.univ.filter fun i => d i = μ).card =
      (Finset.univ.filter fun i => d' i = 1).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, d]
    constructor
    · intro h
      have h' : (mu : K) * d' i = (mu : K) * 1 := by simpa [mu] using h
      exact mul_left_cancel₀ (Units.ne_zero mu) h'
    · intro h
      show (mu : K) * d' i = μ
      rw [h, mul_one]
      rfl
  refine ⟨P', d, e₁, e₂, hMAmat, hMA₁mat, hMA₂mat, ?_⟩
  rw [hfilter]
  exact hcount_d'

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
