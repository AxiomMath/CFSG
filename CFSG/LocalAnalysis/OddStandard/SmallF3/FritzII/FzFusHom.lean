module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36Hom
public import Certificates.Data.FzFusN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

structure FzfDict (t x₁ x₂ lam : G) (T₂ : Subgroup G) (a₁₂ a₂₂ a₃₂ : G) (π : Model →* G) :
    Prop where
  t_eq : π tM = t
  x₁_eq : π x1M = x₁
  x₂_eq : π x2M = x₂
  lam_eq : π lamM = lam
  range_eq : π.range = T₂
  eq_iff : ∀ g h : Model, π g = π h ↔ KEq g h
  rangeR_eq : (π.comp SemidirectProduct.inl).range = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂

private theorem fzfus_dict_q8Hom_mem {K : Subgroup G} {p q : G} (hpq : IsQ8Pair p q)
    (hp : p ∈ K) (hq : q ∈ K) (r : Q8) : q8Hom hpq r ∈ K := by
  cases r with
  | a i => change p ^ i.val ∈ K; exact K.pow_mem hp _
  | xa i => change q * p ^ i.val ∈ K; exact K.mul_mem hq (K.pow_mem hp _)

theorem fzfus_dict {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}
    (hs : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (ht : t ^ 2 = 1) (h1 : t * x₁ = x₁ * t)
    (h2 : t * x₂ = x₂ * t) (h12 : x₁ * x₂ = x₂ * x₁) :
    ∃ π : Model →* G, FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π := by
  obtain ⟨π, hπ1, hπ2, hπ3, hπlam, hrange, hiff⟩ := fzl_model_hom hs
  have ht2 : t * t = 1 := by rw [← pow_two]; exact ht
  have htprod : t = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) := fzFus_t_eq_prod ht2 h2
  have hqL1 : qL 1 = QuaternionGroup.a 1 := by decide
  have htM : π tM = t := by
    have h : π tM = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) := by
      simp only [tM_eq, map_mul, mkE, hπ1, hπ2, hπ3, hqL1, fzl_q8Hom_a_one hs.quat₁,
        fzl_q8Hom_a_one hs.quat₂, fzl_q8Hom_a_one hs.quat₃]
    exact h.trans htprod.symm
  have hx1M : π x1M = x₁ := by
    have h : π x1M = (x₁ * t) * t := by
      simp only [x1M_eq, map_mul, mkE, hπ1, htM, hqL1, fzl_q8Hom_a_one hs.quat₁]
    rw [h, mul_assoc, ht2, mul_one]
  have hx2M : π x2M = x₂ := by
    have h : π x2M = (x₂ * t) * t := by
      simp only [x2M_eq, map_mul, mkE, hπ2, htM, hqL1, fzl_q8Hom_a_one hs.quat₂]
    rw [h, mul_assoc, ht2, mul_one]
  have hrangeR :
      (π.comp SemidirectProduct.inl).range = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ := by
    apply le_antisymm
    · rintro g ⟨n, rfl⟩
      obtain ⟨a, b, c⟩ := n
      change π (⟨(a, b, c), 1⟩ : Model) ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂
      have hsplit : (⟨(a, b, c), (1 : Multiplicative (ZMod 2))⟩ : Model)
          = ⟨(a, 1, 1), 1⟩ * ⟨(1, b, 1), 1⟩ * (⟨(1, 1, c), 1⟩ : Model) := by
        ext <;> simp
      simp only [hsplit, map_mul, mul_assoc, hπ1, hπ2, hπ3]
      refine (fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂).mul_mem ?_ ?_
      · exact fzfus_dict_q8Hom_mem hs.quat₁
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) a
      · refine (fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂).mul_mem ?_ ?_
        · exact fzfus_dict_q8Hom_mem hs.quat₂
            (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) b
        · exact fzfus_dict_q8Hom_mem hs.quat₃
            (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) c
    · rw [fzR6, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · refine MonoidHom.mem_range.mpr ⟨(QuaternionGroup.a 1, 1, 1), ?_⟩
        exact (hπ1 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a_one hs.quat₁)
      · refine MonoidHom.mem_range.mpr ⟨(QuaternionGroup.xa 0, 1, 1), ?_⟩
        exact (hπ1 (QuaternionGroup.xa 0)).trans (fzl_q8Hom_xa_zero hs.quat₁)
      · refine MonoidHom.mem_range.mpr ⟨(1, QuaternionGroup.a 1, 1), ?_⟩
        exact (hπ2 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a_one hs.quat₂)
      · refine MonoidHom.mem_range.mpr ⟨(1, QuaternionGroup.xa 0, 1), ?_⟩
        exact (hπ2 (QuaternionGroup.xa 0)).trans (fzl_q8Hom_xa_zero hs.quat₂)
      · refine MonoidHom.mem_range.mpr ⟨(1, 1, QuaternionGroup.a 1), ?_⟩
        exact (hπ3 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a_one hs.quat₃)
      · refine MonoidHom.mem_range.mpr ⟨(1, 1, QuaternionGroup.xa 0), ?_⟩
        exact (hπ3 (QuaternionGroup.xa 0)).trans (fzl_q8Hom_xa_zero hs.quat₃)
  exact ⟨π, htM, hx1M, hx2M, hπlam, hrange, hiff, hrangeR⟩

section

variable {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G} {π : Model →* G}

theorem FzfDict.eq_one_iff (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) (m : Model) :
    π m = 1 ↔ KEq m 1 := by
  rw [← hd.eq_iff, map_one]

theorem FzfDict.isInvM_iff (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) (m : Model) :
    IsInvM m ↔ (π m * π m = 1 ∧ π m ≠ 1) := by
  unfold IsInvM
  rw [← hd.eq_one_iff, ← hd.eq_one_iff, map_mul]

theorem FzfDict.mem_T₂_iff (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) {g : G} :
    g ∈ T₂ ↔ ∃ m : Model, π m = g := by
  rw [← hd.range_eq]
  exact MonoidHom.mem_range

theorem FzfDict.mem_fzR6_iff (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) {g : G} :
    g ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ↔ ∃ n : N3, π ⟨n, 1⟩ = g := by
  rw [← hd.rangeR_eq]
  exact MonoidHom.mem_range

theorem FzfDict.cl_eq (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) (hC : ClassFact) {m : Model}
    (hm : IsInvM m) : ConjClasses.mk (π m) = ConjClasses.mk (π (rep (clsOf m))) := by
  obtain ⟨g, hg⟩ := hC m hm
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨π g, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hd.eq_iff]
  exact hg

theorem FzfDict.distinct5_iff (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) {u a b : Model} :
    D5M u a b ↔ Distinct5 (π u) (π a) (π b) := by
  unfold D5M Distinct5
  simp only [pow_two, ← map_mul, ← hd.eq_iff, map_one, ne_eq]

end

end CFSG.OddStandard.SmallF3.FritzII
