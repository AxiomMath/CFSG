module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalGrowth

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem oddCoreIn_le_of_isPComponent {C M : Subgroup X} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) : oddCoreIn M ≤ oddCoreIn C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : (M.subgroupOf C).IsSubnormal := hM.choose_spec.2.1
  have h1 := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 (M.subgroupOf C) hsub
  let φ : ↥(M.subgroupOf C) ≃* ↥M := subgroupOfEquivOfLe hMC
  show (pPrimeCore 2 ↥M).map M.subtype ≤ (pPrimeCore 2 ↥C).map C.subtype
  rw [← pPrimeCore_map_iso 2 φ, h1]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨(x : C), hx, rfl⟩

omit [Finite X] in
theorem centralizer_zpowers_eq' (z : X) :
    centralizer ((zpowers z : Subgroup X) : Set X) = centralizer ({z} : Set X) := by
  rw [zpowers_eq_closure, centralizer_closure]

omit [Finite X] in
theorem isPGroup_zpowers_of_mul_self {z : X} (hz : z * z = 1) : IsPGroup 2 (zpowers z) := by
  intro w
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp w.2
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hz, one_zpow]

theorem fixedLayer_facts {C J M : Subgroup X} {z : X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) (hMC : M ≤ C) (hM : IsPComponent 2 (M.subgroupOf C))
    (hMJ : M ≠ J) (hzJ : z ∈ J) (hz : z * z = 1) :
    GSLit.fixedLayer M (zpowers z) ≤ C ⊓ centralizer ({z} : Set X) ∧
      IsPComponent 2 ((GSLit.fixedLayer M (zpowers z)).subgroupOf
        (C ⊓ centralizer ({z} : Set X))) ∧
      GSLit.fixedLayer M (zpowers z) ⊔ (pPrimeCore 2 M).map M.subtype = M ∧
      (pPrimeCore 2 (GSLit.fixedLayer M (zpowers z))).map
          (GSLit.fixedLayer M (zpowers z)).subtype =
        GSLit.fixedLayer M (zpowers z) ⊓ (pPrimeCore 2 M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMsub : (M.subgroupOf C).IsSubnormal := hM.choose_spec.2.1
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hMC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hM)
  have hJM : J ≤ coreActionKernel M := B5a.le_coreActionKernel_of_ne hMC hJC hM hJ hMJ
  have hzK : zpowers z ≤ coreActionKernel M := zpowers_le.mpr (hJM hzJ)
  have hz2 := isPGroup_zpowers_of_mul_self hz
  have h1 := GSLit.fixedLayer_isPComponent hMC hMsub (zpowers_le.mpr (hJC hzJ)) hzK hz2 hMq
  rw [centralizer_zpowers_eq'] at h1
  have h2 := GSLit.fixedLayer_sup_pPrimeCore hMq hzK hz2
  have h3 := GSLit.fixedLayer_le_inf M (zpowers z)
  rw [centralizer_zpowers_eq'] at h3
  exact ⟨h3.trans (inf_le_inf_right _ hMC), h1, h2.1, h2.2⟩

theorem exists_isPComponent_of_isPComponent_inf {C J N : Subgroup X} {z a : X}
    (hJC : J ≤ C) (hJ : IsPComponent 2 (J.subgroupOf C)) (hCJ : C ≤ normalizer (J : Set X))
    (hzJ : z ∈ J) (hz : z * z = 1) (hNC : N ≤ C ⊓ centralizer ({z} : Set X))
    (hN : IsPComponent 2 (N.subgroupOf (C ⊓ centralizer ({z} : Set X)))) (hNL : N ≤ layerIn C)
    (haN : a ∈ N) (hJa : J ≤ centralizer ({a} : Set X)) (ha : a * a = 1) (haJ : a ∉ J) :
    ∃ M : Subgroup X, M ≤ C ∧ IsPComponent 2 (M.subgroupOf C) ∧ M ≠ J ∧ a ∈ M ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* ↥M ⧸ pPrimeCore 2 ↥M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C' := C ⊓ centralizer ({z} : Set X) with hC'
  have hNC0 : N ≤ C := hNC.trans inf_le_left
  have hclaim : ∃ M : Subgroup X, M ≤ C ∧ IsPComponent 2 (M.subgroupOf C) ∧ M ≠ J ∧
      N = GSLit.fixedLayer M (zpowers z) := by
    by_contra hno
    push Not at hno
    set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hJn : (J.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hJC).mpr hCJ
    set A := (J.subgroupOf C).map π with hA
    have hAn : A.Normal := hJn.map π hπs
    set B := ⨆ (M : Subgroup X) (_ : M ≤ C ∧ IsPComponent 2 (M.subgroupOf C) ∧ M ≠ J),
      (M.subgroupOf C).map π with hB
    set Q := (N.subgroupOf C).map π with hQ
    have hcomm_core : ∀ U V : Subgroup X, U ≤ C → V ≤ C → ⁅U, V⁆ ≤ oddCoreIn C →
        ⁅(U.subgroupOf C).map π, (V.subgroupOf C).map π⁆ = ⊥ := by
      intro U V hU hV hUV
      rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      have h1 : (⁅U.subgroupOf C, V.subgroupOf C⁆).map C.subtype ≤
          (pPrimeCore 2 ↥C).map C.subtype := by
        rw [map_commutator, map_subgroupOf_eq_of_le hU, map_subgroupOf_eq_of_le hV]
        exact hUV
      exact (map_le_map_iff_of_injective C.subtype_injective).mp h1
    have hQAB : Q ≤ A ⊔ B := by
      have hNlay : N.subgroupOf C ≤ pLayer ↥C 2 := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := mem_map.mp (hNL (mem_subgroupOf.mp hx))
        rw [show y = x from Subtype.ext hyx] at hy
        exact hy
      refine (map_mono hNlay).trans (map_le_iff_le_comap.mpr (sSup_le fun K hK => ?_))
      rw [← map_le_iff_le_comap]
      set M := K.map C.subtype with hM
      have hKM : M.subgroupOf C = K := comap_map_eq_self_of_injective C.subtype_injective K
      have hMC : M ≤ C := map_subtype_le K
      have hMpc : IsPComponent 2 (M.subgroupOf C) := by rw [hKM]; exact hK
      by_cases hMJ : M = J
      · rw [← hKM, hMJ]
        exact le_sup_left
      · rw [← hKM]
        exact le_sup_of_le_right (le_iSup₂_of_le M ⟨hMC, hMpc, hMJ⟩ le_rfl)
    have hBQ : B ≤ centralizer (Q : Set _) := by
      refine iSup₂_le fun M ⟨hMC, hM, hMJ⟩ => ?_
      obtain ⟨hMzC, hMz, hsup, hcore⟩ := fixedLayer_facts hJC hJ hMC hM hMJ hzJ hz
      set Mz := GSLit.fixedLayer M (zpowers z) with hMzdef
      have hne : N.subgroupOf C' ≠ Mz.subgroupOf C' := by
        intro h
        rw [subgroupOf_inj, inf_of_le_left hNC, inf_of_le_left hMzC] at h
        exact hno M hMC hM hMJ h
      obtain ⟨-, hd⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
        Nat.prime_two _ _ hN hMz
      obtain ⟨-, -, hc, -⟩ := hd hne
      have hOM := oddCoreIn_le_of_isPComponent hMC hM
      have hNMz : ⁅N, Mz⁆ ≤ oddCoreIn C := by
        have h1 := map_mono (f := C'.subtype) (hc.trans inf_le_right)
        rw [map_commutator, map_subgroupOf_eq_of_le hNC, map_subgroupOf_eq_of_le hMzC,
          pPrimeCore_map_subgroupOf 2 Mz C' hMzC, hcore] at h1
        exact h1.trans (inf_le_right.trans hOM)
      have hMeq : (M.subgroupOf C).map π = (Mz.subgroupOf C).map π := by
        have hMzM : Mz ≤ C := hMzC.trans inf_le_left
        have hOMC : (pPrimeCore 2 M).map M.subtype ≤ C := (map_subtype_le _).trans hMC
        rw [← hsup, subgroupOf_sup hMzM hOMC, Subgroup.map_sup]
        have h0 : (((pPrimeCore 2 M).map M.subtype).subgroupOf C).map π = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
          intro x hx
          obtain ⟨y, hy, hyx⟩ := mem_map.mp (hOM (mem_subgroupOf.mp hx))
          rw [show y = x from Subtype.ext hyx] at hy
          exact hy
        rw [h0, sup_bot_eq]
      rw [hMeq, ← commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact hcomm_core N Mz hNC0 (hMzC.trans inf_le_left) hNMz
    have hperf : ⁅Q, Q⁆ = Q := by
      have h1 : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hN
      have h2 : ⁅N.subgroupOf C, N.subgroupOf C⁆ = N.subgroupOf C := by
        apply map_injective C.subtype_injective
        rw [map_commutator, map_subgroupOf_eq_of_le hNC0, h1]
      rw [hQ, ← map_commutator, h2]
    have hQA := le_of_le_sup_of_le_centralizer hQAB hBQ hperf
    have haC : a ∈ C := hNC0 haN
    have hJa' : J.subgroupOf C ≤ centralizer ({(⟨a, haC⟩ : ↥C)} : Set ↥C) := by
      intro x hx
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJa (mem_subgroupOf.mp hx)))
    have haJ' : (⟨a, haC⟩ : ↥C) ∈ J.subgroupOf C := mem_of_mk_mem hJa' (Subtype.ext ha)
      (hQA (mem_map_of_mem π (show (⟨a, haC⟩ : ↥C) ∈ N.subgroupOf C from haN)))
    exact haJ haJ'
  obtain ⟨M, hMC, hM, hMJ, hNM⟩ := hclaim
  obtain ⟨-, -, hsup, hcore⟩ := fixedLayer_facts hJC hJ hMC hM hMJ hzJ hz
  have hMzM : GSLit.fixedLayer M (zpowers z) ≤ M :=
    (GSLit.fixedLayer_le_inf M (zpowers z)).trans inf_le_left
  refine ⟨M, hMC, hM, hMJ, hMzM (hNM ▸ haN), ?_⟩
  obtain ⟨e, -⟩ := UnbalancedCorr.exists_quotient_equiv_of_sup hMzM hsup hcore
  subst hNM
  exact ⟨e⟩

end Seven

end CFSG.ComponentClassification.GSThmB
