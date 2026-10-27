module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxOrthogonal
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.RankThree.PartOne.S15K.OrthModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open TauCeti CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial

theorem exists_lift_of_commute {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ringChar K)
    {a c : ProjOrthDerived Q} (ha : a ^ p = 1) (ha1 : a ≠ 1) (hac : a * c = c * a) :
    ∃ x y : ↥(orthDerived Q),
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x = a ∧
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y = c ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a) =
        centralizerImage Q (x : V ≃ₗ[K] V) ∧
      (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have haord : orderOf a = p := orderOf_eq_prime ha ha1
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxmk, hxord⟩, -, hxcent⟩ := hlift p hp hp2 a haord
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxord
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a) =
      centralizerImage Q (x : V ≃ₗ[K] V) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.fixSubgroup_conj_eq_centralizer',
      hxcent, CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage]
  have hc : c ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hac.symm
  rw [hxcent] at hc
  obtain ⟨y, hycent, hymk⟩ := Subgroup.mem_map.mp hc
  refine ⟨x, y, ?_, ?_, hx, hfix, ?_⟩
  · simpa only [QuotientGroup.mk'_apply] using hxmk
  · exact hymk
  · refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup y.2) v
    · have hcomm : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hycent
      have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V) v) hcomm
      simpa using h

theorem compAlgInnerAt_projOrthDerived_eight {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hK8 : Nat.card K = 8) : CompAlgInnerAt (ProjOrthDerived Q) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [Fintype.card_eq_nat_card, hK8]; norm_num)
  have hring : ringChar K = 2 := ringChar.eq (R := K) 2
  have h3ℓ : 3 ≠ ringChar K := by rw [hring]; norm_num
  haveI : Nontrivial V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ := CFSG.RankThree.PartOne.KCOrthogonalModel.center_projOrthDerived_eq_bot hQ hT
  intro β hβmem hβ3 hβ1 J hJ e he hiso γ hγmem hγ3 hβγ hR hγstab
  obtain ⟨a, ha3, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ hR.1 hβ3
  obtain ⟨c, hc3, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ hR.2 hγ3
  have ha1 : a ≠ 1 := by
    intro h
    exact hβ1 (by rw [h]; exact map_one _)
  have hac : a * c = c * a := by
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
    rw [map_mul, map_mul]
    exact hβγ
  obtain ⟨x, y, rfl, rfl, hx, hfix, hy⟩ :=
    exists_lift_of_commute hQ hT Nat.prime_three (by norm_num) h3ℓ ha3 ha1 hac
  rw [hfix] at hJ
  have hy3 : y ^ 3 = 1 := by
    apply CFSG.RankThree.PartOne.S15K.mk_injective_orth (Q := Q) hQ
    rw [map_pow, hc3, map_one]
  rcases exists_component_dichotomy Nat.prime_three (by norm_num) hQ hT h3ℓ hx J hJ with
    ⟨h, hh, hne, hq, hJeq⟩ | ⟨hlist, F, hFq, hFle, hFn, hJeq⟩
  · have hself := (primaryFactor_eq_X_sq_add_X_add_one_of_card_eq_eight hx hK8 hh hne).2
    haveI : Fact (Irreducible h) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh⟩
    have hq' : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
      ⟨hq.1.commutator_eq_top, hq.2.1⟩
    obtain ⟨ℓ, f, hU, B, hBs, hBl, hperf, g, π', hsurj, hker, hconj⟩ :=
      exists_sesqSUConjData hx (by decide) hh hne hself.symm hq' y hy J hJeq hγstab
    have hy3' : (MulAut.conj (QuotientGroup.mk'
        ((scalars K V).subgroupOf (orthDerived Q)) y)) ^ 3 = 1 := by
      rw [← map_pow, hc3, map_one]
    have hstab3 : (⟨MulAut.conj (QuotientGroup.mk'
        ((scalars K V).subgroupOf (orthDerived Q)) y), hγstab⟩ :
        CFSG.GroupActions.subgroupStabAut J) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hy3'
    have hpow : centerQuotientHom ↥J
        (CFSG.GroupActions.subgroupStabRestrict J
          ⟨MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y),
            hγstab⟩) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hstab3]
      simp
    exact centerQuotientHom_mem_innAutDerived_of_sesqSUConj hU hBs hBl hperf Nat.prime_three
      (by norm_num) g π' hsurj hker hconj hpow
  · exact centerQuotientHom_mem_innAutDerived_of_fixedFactor hx hK8 hlist hFq hFle hFn J hJeq
      hy hy3 hγstab

theorem compAlgInnerAt_of_statedClassicalModel_eight
    {t : CFSG.Open.StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : CFSG.Open.StatedClassicalModel G t n ℓ f) (h8 : ℓ ^ f = 8) :
    CompAlgInnerAt G := by
  obtain ⟨K, hfield, hfinite, V, _, _, _, Q, hQ, hT, hcard, -, ⟨e⟩⟩ :=
    exists_projOrth_model_card ht hG
  letI := hfield
  letI := hfinite
  have hK8 : Nat.card K = 8 := by rw [hcard, h8]
  exact compAlgInnerAt_of_mulEquiv e.symm
    (compAlgInnerAt_projOrthDerived_eight hQ hT hK8)

theorem compAlgAt_pomegaPlus_eight {n ℓ f : ℕ} {G : Type}
    [Group G] [Finite G] (hG : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f)
    (hn : 5 ≤ n) (h8 : ℓ ^ f = 8) : CompAlgAt G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G (coordinatePlusWitnessEquiv K e).toEquiv
  have hM : CFSG.Open.StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K))
      .POmegaPlus n ℓ f :=
    ⟨hadm, K, hfield, hfinite, hK,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n K)
        (coe_quadPlus n K)).symm⟩⟩
  have hinner : CompAlgInnerAt (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    compAlgInnerAt_of_statedClassicalModel_eight (Or.inr (Or.inl rfl)) hM h8
  have hS : ∀ β ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadPlus n K)),
      β ^ 3 = 1 → β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    fun β hβ hβ3 => (matrixModel_facts_pomegaPlus hG0 hn hK e).2.2.2 3
      Nat.prime_three (by norm_num) β hβ hβ3
  exact compAlgAt_of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (compAlgAt_of_inner hS hinner)

theorem compAlgAt_pomegaMinus_eight {n ℓ f : ℕ} {G : Type}
    [Group G] [Finite G] (hG : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (h8 : ℓ ^ f = 8) : CompAlgAt G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn1 : 1 ≤ n := by have := hadm.2.2; omega
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv
  have hM : CFSG.Open.StatedClassicalModel
      (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) .POmegaMinus n ℓ f :=
    ⟨hadm, K, hfield, hfinite, hK, b, c, hirr,
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn1) (quadMinus n K b c)
        (coe_quadMinus n K b c)).symm⟩⟩
  have hinner : CompAlgInnerAt (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    compAlgInnerAt_of_statedClassicalModel_eight (Or.inr (Or.inr rfl)) hM h8
  have hS : ∀ β ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)),
      β ^ 3 = 1 → β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    fun β hβ hβ3 => (matrixModel_facts_pomegaMinus hG0 hK hn1 b c hirr e).2.2.2 3
      Nat.prime_three (by norm_num) β hβ hβ3
  exact compAlgAt_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm
    (compAlgAt_of_inner hS hinner)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
