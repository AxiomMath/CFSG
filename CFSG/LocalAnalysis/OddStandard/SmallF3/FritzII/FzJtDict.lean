module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusLet
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzQuat

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

theorem fzJt_dict {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}
    (hs : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (ht : t ^ 2 = 1) (h1 : t * x₁ = x₁ * t)
    (h2 : t * x₂ = x₂ * t) :
    ∃ π : Model →* G, FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π ∧
      ∀ q : Q8, π (⟨(1, 1, q), 1⟩ : Model) = q8Hom hs.quat₃ q := by
  obtain ⟨π, hπ1, hπ2, hπ3, hπlam, hrange, hiff⟩ := fzl_model_hom hs
  have hq8 : ∀ {p q : G} (hpq : IsQ8Pair p q) {K : Subgroup G}, p ∈ K → q ∈ K →
      ∀ r : Q8, q8Hom hpq r ∈ K := by
    intro p q hpq K hp hq r
    cases r with
    | a i => change p ^ i.val ∈ K; exact K.pow_mem hp _
    | xa i => change q * p ^ i.val ∈ K; exact K.mul_mem hq (K.pow_mem hp _)
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
      · exact hq8 hs.quat₁
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) a
      · refine (fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂).mul_mem ?_ ?_
        · exact hq8 hs.quat₂
            (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) b
        · exact hq8 hs.quat₃
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
  exact ⟨π, ⟨htM, hx1M, hx2M, hπlam, hrange, hiff, hrangeR⟩, hπ3⟩

theorem fzJt_mem_fzR3_iff {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}
    {π : Model →* G} (hs : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (hπ3 : ∀ q : Q8, π (⟨(1, 1, q), 1⟩ : Model) = q8Hom hs.quat₃ q) {a : G} :
    a ∈ fzR3 t x₁ x₂ a₃₂ ↔ ∃ q : Q8, π (mkE 1 1 q) = a := by
  rw [fzR3, ← fz_q8_range hs.quat₃]
  simp only [MonoidHom.mem_range, mkE, hπ3]

theorem fzJt_z3_mul_self {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}
    {π : Model →* G} (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) :
    (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
  have h := ((hd.isInvM_iff z3M).mp label_facts.2.2.1).1
  rwa [hd.z3M_eq] at h

theorem fzJt_mkE_sq (q : Q8) (h : KEq (mkE 1 1 q * mkE 1 1 q) z3M) :
    q * q = QuaternionGroup.a 2 := by
  revert q
  decide +kernel

theorem fzJt_R3_sq {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G} {π : Model →* G}
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) {q : Q8}
    (h : π (mkE 1 1 q) ^ 2 = (x₁ * x₂) ^ 2) : q * q = QuaternionGroup.a 2 := by
  refine fzJt_mkE_sq q ((hd.eq_iff _ _).mp ?_)
  rw [map_mul, hd.z3M_eq, ← pow_two]
  exact h

theorem fzJt_mkE_inv (q : Q8) : (mkE 1 1 q)⁻¹ = mkE 1 1 q⁻¹ := by
  revert q
  decide +kernel

theorem fzJt_q_cases (q : Q8) (h : q * q = QuaternionGroup.a 2) :
    (q = QuaternionGroup.a 1 ∨ q = QuaternionGroup.xa 0 ∨ q = QuaternionGroup.xa 3) ∨
    (q⁻¹ = QuaternionGroup.a 1 ∨ q⁻¹ = QuaternionGroup.xa 0 ∨ q⁻¹ = QuaternionGroup.xa 3) := by
  revert q
  decide

end CFSG.OddStandard.SmallF3.FritzII
