module

public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting)
open CFSG.Assembly (pCoreOf)

theorem exists_component_of_conj_involution {H X : Type} [Group H] [Group X] (e : H ≃* X) {τ : H}
    (hconj : ∀ u : H, u * u = 1 → u ≠ 1 → ∃ g : H, g * u * g⁻¹ = τ)
    {Q : Subgroup H} (hQC : Q ≤ Subgroup.centralizer ({τ} : Set H))
    (hQn : (Q.subgroupOf (Subgroup.centralizer ({τ} : Set H))).Normal)
    (hq : CFSG.IsQuasisimple ↥Q) {t : X} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ E : Subgroup X, E ≤ Subgroup.centralizer ({t} : Set X) ∧
      (E.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal ∧ CFSG.IsQuasisimple ↥E := by
  obtain ⟨g, hg⟩ := hconj (e.symm t) (by rw [← map_mul, ht2, map_one])
    (fun h => ht1 (by simpa using congrArg e h))
  let φ : H ≃* X := (MulAut.conj g⁻¹).trans e
  have hφ : ∀ h : H, φ h = e (g⁻¹ * h * g) := fun h => by simp [φ]
  have hφτ : φ τ = t := by
    rw [hφ, ← hg]
    have : g⁻¹ * (g * e.symm t * g⁻¹) * g = e.symm t := by group
    rw [this, MulEquiv.apply_symm_apply]
  have hφsymm : φ.symm t = τ := by rw [MulEquiv.symm_apply_eq, hφτ]
  refine ⟨Q.map φ.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq', rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hQC hq')
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ q * t = t * φ q
    rw [← hφτ, ← map_mul, ← map_mul, h1]
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨q, hq', hqx⟩ := Subgroup.mem_subgroupOf.mp hx
    have hy := y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hyτ : φ.symm y * τ = τ * φ.symm y := by
      have := congrArg φ.symm hy
      rwa [map_mul, map_mul, hφsymm] at this
    have hyC : φ.symm y ∈ Subgroup.centralizer ({τ} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyτ
    have hmem := hQn.conj_mem ⟨q, hQC hq'⟩ (Subgroup.mem_subgroupOf.mpr hq') ⟨φ.symm y, hyC⟩
    have hmem' := Subgroup.mem_subgroupOf.mp hmem
    refine Subgroup.mem_subgroupOf.mpr ⟨_, hmem', ?_⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv]
    rw [← hqx]
    simp
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Q.equivMapOfInjective φ.toMonoidHom φ.injective) hq

theorem false_of_normal_quasisimple_in_normalizer {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (S : STSetting G K) {E : Subgroup G}
    (hEM : E ≤ Subgroup.normalizer (K : Set G))
    (hEn : (E.subgroupOf (Subgroup.normalizer (K : Set G))).Normal)
    (hq : CFSG.IsQuasisimple ↥E) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (K : Set G) with hM
  have hUM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hMU : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hU2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hUn : ((pCoreOf 2 M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mpr hMU
  have hUsolv : Group.IsSolvable ↥((pCoreOf 2 M).subgroupOf M) := by
    have hp : IsPGroup 2 ↥((pCoreOf 2 M).subgroupOf M) :=
      hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm
    have := hp.isNilpotent
    infer_instance
  have hq' : CFSG.IsQuasisimple ↥(E.subgroupOf M) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEM).symm hq
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hUsolv hUn.isSubnormal).1
    (E.subgroupOf M) ⟨hq', hEn.isSubnormal⟩
  have hEU : E ≤ pCoreOf 2 M := by
    intro x hx
    refine S.fstar ⟨hEM hx, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hm := Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.2 hx : (⟨x, hEM hx⟩ : M) ∈ E.subgroupOf M)
      (Subgroup.mem_subgroupOf.2 hu : (⟨u, hUM hu⟩ : M) ∈ (pCoreOf 2 M).subgroupOf M)
    rw [hcomm, Subgroup.mem_bot] at hm
    exact (congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hm)).symm
  have hE2 : IsPGroup 2 ↥E := hU2.to_le hEU
  have hnil : Group.IsNilpotent ↥E := hE2.isNilpotent
  have hnt : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E).ne (Group.isPerfect_def.mp hq.1)

end CFSG.CGT.PushingUpLit.SolKNA
