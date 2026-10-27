module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCZ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidXtCore

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoClassical.URigid (conjAut coe_conjAut mulAut_mem_center)
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Psi

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))
  {Q : QuadraticForm K (ι → K)}

@[expose] noncomputable def oPsi (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q) :
    ↥(oXt oe Q₂) →* StatedProj (StatedOmega ⇑Q) :=
  (oProj ⇑Q).comp (Subgroup.inclusion hle)

variable {oe Q₂}

theorem oPsi_apply (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q) (x : ↥(oXt oe Q₂)) :
    oPsi oe Q₂ hle x = oProj ⇑Q ⟨x, hle x.2⟩ :=
  rfl

theorem oPsi_injective (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hinj : Function.Injective (oProj ⇑Q)) : Function.Injective (oPsi oe Q₂ hle) :=
  hinj.comp (Subgroup.inclusion_injective hle)

theorem range_oPsi (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q) :
    (oPsi oe Q₂ hle).range = ((oXt oe Q₂).subgroupOf (StatedOmega ⇑Q)).map (oProj ⇑Q) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, hle x.2⟩, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qEGL_zero_mul_self (a : K) : qEGL oe Q₂ 0 a * qEGL oe Q₂ 0 a = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_qEGL, qE_mul, Units.val_one, ← qE_zero oe Q₂]
  congr 1
  · simp
  · simp only [Pi.zero_apply, map_zero, add_zero]
    linear_combination a * CharTwo.two_eq_zero (R := K)

end Psi

section Range

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤) (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤) [Nonempty ι₂]
  (hnd : Q₂.polarBilin.Nondegenerate) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
include hQ hSL hperf₂ hnd ht0 ht1

theorem perfectCore_centralizer_oPsi (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hinj : Function.Injective (oProj ⇑Q)) :
    perfectCore (centralizer ({oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1))} :
      Set (StatedProj (StatedOmega ⇑Q)))) = (oPsi oe Q₂ hle).range := by
  set M₀ := oRhoOne oe hQ hSL (slTr 1)
  have hC : centralizer ({oProj ⇑Q M₀} : Set (StatedProj (StatedOmega ⇑Q))) =
      (centralizer ({M₀} : Set ↥(StatedOmega ⇑Q))).map (oProj ⇑Q) := by
    refine le_antisymm (fun z hz => ?_) ?_
    · obtain ⟨g, rfl⟩ := oProj_surjective ⇑Q z
      refine ⟨g, ?_, rfl⟩
      simp only [SetLike.mem_coe, mem_centralizer_singleton_iff] at hz ⊢
      exact hinj (by rw [map_mul, map_mul, hz])
    · rintro _ ⟨g, hg, rfl⟩
      simp only [SetLike.mem_coe, mem_centralizer_singleton_iff] at hg ⊢
      rw [← map_mul, ← map_mul, hg]
  have hX : perfectCore (centralizer ({M₀} : Set ↥(StatedOmega ⇑Q))) =
      (oXt oe Q₂).subgroupOf (StatedOmega ⇑Q) := by
    apply Subgroup.map_injective (StatedOmega ⇑Q).subtype_injective
    rw [← perfectCore_inf_centralizer_eq_map, subgroupOf_map_subtype, inf_of_le_left hle]
    exact perfectCore_eq_oXt hQ hSL hperf₂ hnd ht0 ht1
  rw [hC, ← CFSG.Quasithin.map_perfectCore, hX, range_oPsi]

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {θ : ↥A →* StatedProj (StatedOmega ⇑Q)}

theorem map_perfectCore_eq_range_oPsi (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hinj : Function.Injective (oProj ⇑Q)) (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1) (hθp : θ ⟨p, hpA⟩ = oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1))) :
    (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map θ = (oPsi oe Q₂ hle).range := by
  have hx2 : (⟨p, hpA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
  rw [map_perfectCore_centralizer_eq_of_quot hθ hker hodd hx2, hθp,
    perfectCore_centralizer_oPsi hQ hSL hperf₂ hnd ht0 ht1 hle hinj]

theorem exists_theta_oXt (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hinj : Function.Injective (oProj ⇑Q)) (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1) (hθp : θ ⟨p, hpA⟩ = oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1))) :
    ∃ Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* ↥(oXt oe Q₂),
      Function.Surjective Θ ∧
        ∀ x, oPsi oe Q₂ hle (Θ x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x) := by
  have hmap := map_perfectCore_eq_range_oPsi hQ hSL hperf₂ hnd ht0 ht1 hle hinj hθ hker hodd hpA
    hp2 hθp
  have hX : perfectCore (A ⊓ centralizer ({p} : Set G)) =
      (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map A.subtype :=
    perfectCore_inf_centralizer_eq_map ⟨p, hpA⟩
  have hmem : ∀ x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))),
      θ (Subgroup.inclusion (perfectCore_inf_le A p) x) ∈ (oPsi oe Q₂ hle).range := by
    intro x
    rw [← hmap]
    obtain ⟨y, hy, hyx⟩ : (x : G) ∈
        (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map A.subtype := by
      rw [← hX]
      exact x.2
    refine ⟨y, hy, ?_⟩
    congr 1
    exact Subtype.ext hyx
  set e := MonoidHom.ofInjective (oPsi_injective hle hinj)
  set Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* ↥(oXt oe Q₂) :=
    e.symm.toMonoidHom.comp
      ((θ.comp (Subgroup.inclusion (perfectCore_inf_le A p))).codRestrict _ hmem)
  have hΘ : ∀ x, oPsi oe Q₂ hle (Θ x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x) := by
    intro x
    change oPsi oe Q₂ hle (e.symm _) = _
    rw [← MonoidHom.ofInjective_apply (oPsi_injective hle hinj), MulEquiv.apply_symm_apply]
    rfl
  refine ⟨Θ, fun g => ?_, hΘ⟩
  have hg : oPsi oe Q₂ hle g ∈ (perfectCore (centralizer ({⟨p, hpA⟩} : Set ↥A))).map θ := by
    rw [hmap]
    exact ⟨g, rfl⟩
  obtain ⟨y, hy, hyg⟩ := hg
  have hyX : (y : G) ∈ perfectCore (A ⊓ centralizer ({p} : Set G)) := by
    rw [hX]
    exact ⟨y, hy, rfl⟩
  refine ⟨⟨y, hyX⟩, oPsi_injective hle hinj ?_⟩
  rw [hΘ, ← hyg]
  rfl

end Range

section Center

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  [Nonempty ι₂] (hnd : Q₂.polarBilin.Nondegenerate) (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
include hQ hnd hle

theorem exists_qEGL_zero_of_mem_center_oXt {z : ↥(oXt oe Q₂)} (hz : z ∈ center ↥(oXt oe Q₂)) :
    ∃ a : K, (z : GL ι K) = qEGL oe Q₂ 0 a := by
  refine eq_qEGL_zero_of_commute hQ hnd (quad_mulVec_of_mem_statedOmega (hle z.2))
    fun u c => ?_
  have hq : qEGL oe Q₂ u c ∈ oXt oe Q₂ := mem_sup_left (qEGL_mem_oQE oe Q₂ u c)
  exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨_, hq⟩)).symm

theorem eq_one_of_mem_center_oXt {z : ↥(oXt oe Q₂)} (hz : z ∈ center ↥(oXt oe Q₂)) {m : ℕ}
    (hm : Odd m) (hzm : z ^ m = 1) : z = 1 := by
  obtain ⟨a, ha⟩ := exists_qEGL_zero_of_mem_center_oXt hQ hnd hle hz
  have h2 : z ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, _root_.sq, ha, qEGL_zero_mul_self, OneMemClass.coe_one]
  have h1 := orderOf_dvd_of_pow_eq_one h2
  have h3 := orderOf_dvd_of_pow_eq_one hzm
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hm) h1 h3)

theorem theta_eq_one_of_mem_center_oXt {X : Type*} [Group X] {Θ : X →* ↥(oXt oe Q₂)}
    (hΘ : Function.Surjective Θ) {x : X} (hx : x ∈ center X) (hodd : Odd (orderOf x)) :
    Θ x = 1 := by
  have hc : Θ x ∈ center ↥(oXt oe Q₂) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hΘ g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  exact eq_one_of_mem_center_oXt hQ hnd hle hc hodd
    (by rw [← map_pow, pow_orderOf_eq_one, map_one])

theorem exists_beta_oXt {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {θ : ↥A →* StatedProj (StatedOmega ⇑Q)} (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {p : G}
    {Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* ↥(oXt oe Q₂)}
    (hΘs : Function.Surjective Θ)
    (hΘ : ∀ x, oPsi oe Q₂ hle (Θ x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    {x : G} (hXx : rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) x =
      perfectCore (A ⊓ centralizer ({p} : Set G))) :
    ∃ β : MulAut ↥(oXt oe Q₂), ∀ y, β (Θ y) = Θ (conjAut hXx y) := by
  have hXA := perfectCore_inf_le A p
  refine exists_mulAut_comp_eq_of_ker Θ hΘs (conjAut hXx) fun y hy => ?_
  have hyA : Subgroup.inclusion hXA y ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, ← hΘ, hy, map_one]
  have hyc : y ∈ center ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) := by
    rw [mem_center_iff]
    intro z
    apply Subgroup.inclusion_injective hXA
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hyA _
  have hyo : Odd (orderOf y) := by
    rw [← orderOf_injective (Subgroup.inclusion hXA) (Subgroup.inclusion_injective hXA) y]
    have h1 := orderOf_dvd_natCard (⟨_, hyA⟩ : center ↥A)
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  refine theta_eq_one_of_mem_center_oXt hQ hnd hle hΘs (mulAut_mem_center (conjAut hXx) hyc) ?_
  rwa [MulEquiv.orderOf_eq]

end Center

end CFSG.ComponentClassification.RankTwoClassical.ORigid
