module

public import CFSG.HardMathSupport.Malle.Proving.CoverThreeModel
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup conjAut
  conjAut_mem_linearAutGroup)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField)

section Action

variable {Y : Type*} [Group Y] (K : Subgroup Y) [hKn : K.Normal] {M : Type*} [Group M]
  (e : K ⧸ Subgroup.center K ≃* M)

theorem modelAct_apply_mk (y : Y) (k : K) :
    modelAct K e y (e (QuotientGroup.mk k)) =
      e (QuotientGroup.mk ⟨y * k * y⁻¹, hKn.conj_mem k k.2 y⟩) := by
  change e ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
    (MulAut.conjNormal y)) (e.symm (e (QuotientGroup.mk' _ k)))) = _
  rw [MulEquiv.symm_apply_apply,
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  rfl

theorem modelAct_coe (k : K) :
    modelAct K e k = MulAut.conj (e (QuotientGroup.mk k)) := by
  ext m
  obtain ⟨k', hk'⟩ := QuotientGroup.mk_surjective (e.symm m)
  have hm : m = e (QuotientGroup.mk k') := by rw [hk', MulEquiv.apply_symm_apply]
  rw [hm, modelAct_apply_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem exists_modelAct_eq_conj (m : M) : ∃ k : K, modelAct K e k = MulAut.conj m := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm m)
  exact ⟨k, by rw [modelAct_coe, hk, MulEquiv.apply_symm_apply]⟩

end Action

theorem sup_sylow_normal_of_out {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    {M : Type*} [Group M] (e : K ⧸ Subgroup.center K ≃* M) (D : Subgroup (MulAut M))
    (hcomm : ∀ α β : MulAut M, α * β * α⁻¹ * β⁻¹ ∈ D)
    (hcube : ∀ d ∈ D, d ^ 3 ∈ (MulAut.conj : M →* MulAut M).range)
    (hker : (modelAct K e).ker ≤ Subgroup.centralizer (K : Set Y))
    (R : Sylow 3 Y) (hC : Subgroup.centralizer (K : Set Y) ≤ (R : Subgroup Y)) :
    (K ⊔ (R : Subgroup Y)).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ := modelAct K e with hφ
  have hDn : D.Normal := ⟨fun d hd α => by
    have h : α * d * α⁻¹ = (α * d * α⁻¹ * d⁻¹) * d := by group
    rw [h]
    exact D.mul_mem (hcomm α d) hd⟩
  set N : Subgroup Y := D.comap φ with hN
  have hNn : N.Normal := hDn.comap φ
  set H : Subgroup Y := K ⊔ Subgroup.centralizer (K : Set Y) with hH
  have : (Subgroup.centralizer (K : Set Y)).Normal := Subgroup.normal_centralizer
  have hHn : H.Normal := Subgroup.sup_normal _ _
  have hHR : H ≤ K ⊔ (R : Subgroup Y) := sup_le le_sup_left (hC.trans le_sup_right)
  have hN3 : ∀ n ∈ N, n ^ 3 ∈ H := by
    intro n hn
    obtain ⟨m, hm⟩ := hcube (φ n) hn
    obtain ⟨k, hk⟩ := exists_modelAct_eq_conj K e m
    have hker' : n ^ 3 * (k : Y)⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv, hk, hm, mul_inv_cancel]
    have h : n ^ 3 = (n ^ 3 * (k : Y)⁻¹) * k := by group
    rw [h]
    exact H.mul_mem (Subgroup.mem_sup_right (hker hker')) (Subgroup.mem_sup_left k.2)
  have hNle : N ≤ K ⊔ (R : Subgroup Y) := by
    have hp : IsPGroup 3 (N.map (QuotientGroup.mk' H)) := by
      rintro ⟨_, n, hn, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hN3 n hn
    have hmapn : (N.map (QuotientGroup.mk' H)).Normal :=
      hNn.map _ (QuotientGroup.mk'_surjective H)
    have hle := hp.le_sylow_of_normal (R.mapSurjective (QuotientGroup.mk'_surjective H))
    intro n hn
    obtain ⟨r, hr, hrn⟩ := hle ⟨n, hn, rfl⟩
    have hrn' : r⁻¹ * n ∈ H := by
      rw [← QuotientGroup.eq]
      exact hrn
    have h : n = r * (r⁻¹ * n) := by group
    rw [h]
    exact (K ⊔ (R : Subgroup Y)).mul_mem (Subgroup.mem_sup_right hr) (hHR hrn')
  have hRc : ∀ g : Y, ∀ r ∈ (R : Subgroup Y), g * r * g⁻¹ ∈ K ⊔ (R : Subgroup Y) := by
    intro g r hr
    have hcm : g * r * g⁻¹ * r⁻¹ ∈ N := by
      change φ (g * r * g⁻¹ * r⁻¹) ∈ D
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hcomm _ _
    have h : g * r * g⁻¹ = (g * r * g⁻¹ * r⁻¹) * r := by group
    rw [h]
    exact (K ⊔ (R : Subgroup Y)).mul_mem (hNle hcm) (Subgroup.mem_sup_right hr)
  refine ⟨fun x hx g => ?_⟩
  have hle : K ⊔ (R : Subgroup Y) ≤
      (K ⊔ (R : Subgroup Y)).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun k hk => ?_) (fun r hr => hRc g r hr)
    exact Subgroup.mem_sup_left (‹K.Normal›.conj_mem k hk g)
  exact hle hx

theorem commutator_mem_linearAutGroup {F : Type} [Field F] [Finite F]
    (α β : MulAut (projectiveSL 3 F)) : α * β * α⁻¹ * β⁻¹ ∈ linearAutGroup 3 F :=
  CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup le_rfl α β

theorem commutator_mem_psuConj_range {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (hq : 2 < p ^ f) (α β : MulAut (unitaryPSU h 3)) :
    α * β * α⁻¹ * β⁻¹ ∈ (psuConj h).range :=
  CFSG.RankThree.PartTwo.KFacts.commutator_mem_psuConj_range h hq α β

theorem sup_sylow_normal_linear {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hK : Open.IsQuasisimple K) {F : Type} [Field F] [Finite F]
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F) (R : Sylow 3 Y)
    (hC : Subgroup.centralizer (K : Set Y) ≤ (R : Subgroup Y)) :
    (K ⊔ (R : Subgroup Y)).Normal :=
  sup_sylow_normal_of_out e (linearAutGroup 3 F) commutator_mem_linearAutGroup
    (fun _ hd => pow_three_mem_range_conj_of_mem_linearAutGroup hd) (modelAct_ker hK e).le R hC

theorem sup_sylow_normal_unitary {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hK : Open.IsQuasisimple K) {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    (hq : 2 < ℓ ^ f) (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3) (R : Sylow 3 Y)
    (hC : Subgroup.centralizer (K : Set Y) ≤ (R : Subgroup Y)) :
    (K ⊔ (R : Subgroup Y)).Normal :=
  sup_sylow_normal_of_out e (psuConj h).range (commutator_mem_psuConj_range hq)
    (fun _ hd => pow_three_mem_range_conj_of_mem_psuConj_range hd) (modelAct_ker hK e).le R hC

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
