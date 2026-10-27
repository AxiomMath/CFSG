module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxCentreA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

section E16

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem t_mem_of_card_eight (h : Ctx0 t L S x₁ x₂ lam rho) {E : Subgroup G}
    (hEQ : E ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hcard : Nat.card E = 8) : t ∈ E := by
  by_contra htE
  have hHt : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have haH : a ∈ invCent t := by
      have hQH : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ invCent t :=
        sup_le (twoCore_le_invCent t) ((pt_wreath_le_L h).trans (L_le_invCent h.hyp))
      exact hQH (hEQ ha)
    exact (Commute.zpow_right (mem_invCent_iff.mp haH : Commute a t) k).eq
  have hinf : E ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxt⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hxt with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxE) htE
  have hcard16 : Nat.card ↥(E ⊔ zpowers t) = 16 := by
    rw [card_sup_of_commute hHt hinf, hcard, Nat.card_zpowers, h.hyp.ord_t]
  have hE16e : CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers t) := by
    refine ⟨isMulCommutative_sup_of_commute hHt hEe.1 inferInstance, ?_⟩
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hHt).mp hx
    have hab : Commute a b := hHt a ha b hb
    rw [hab.mul_pow, hEe.2 a ha, one_mul]
    rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hb with h1 | h1
    · rw [h1]
      exact one_pow 2
    · rw [h1, pow_two]
      exact t_mul_self h.hyp
  have hle : E ⊔ zpowers t ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
    sup_le hEQ (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left h.hyp.mem_twoCore))
  have := pt_m2 h _ hle hE16e
  omega

theorem ctx_E16_cases (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam) :
    ∀ E : Subgroup G, E ≤ S → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
      E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2} ∨
      E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, (x₁ * x₂) ^ 2, lam} ∨
      E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, (x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam} := by
  intro E hES hEe hEcard
  have hQS : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := sup_le (twoCore_le_S h) (wreathGrp_le_S h)
  have hE'e : CFSG.Open.IsElemAbelian 2 (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam)) :=
    pt_elem_of_le hEe inf_le_left
  have hle8 : Nat.card ↥(E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam)) ≤ 8 :=
    pt_m2 h _ inf_le_right hE'e
  have hcount := card_le_card_inf_mul_relIndex (H := S)
    (L := twoCore t ⊔ wreathGrp x₁ x₂ lam) (Y := E) hQS hES
  rw [hi.index_PT, hEcard] at hcount
  have hE'card : Nat.card ↥(E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam)) = 8 := by omega
  have htE : t ∈ E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) :=
    t_mem_of_card_eight h inf_le_right hE'e hE'card
  have hsq : ∀ n ∈ E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam), n * n = 1 := fun n hn => by
    rw [← pow_two]
    exact hEe.2 n hn.1
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right (t_mul_self h.hyp)
  have hDe : CFSG.Open.IsElemAbelian 2
      (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam) := hE'e.mono inf_le_left
  have hD4 : Nat.card ↥(E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam) ≤ 4 :=
    card_le_four_of_elemAbelian_wreathGrp h.wreath inf_le_right hDe
  have hidx : (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam).relIndex
      (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam)) ≤ 2 := by
    refine relIndex_le_two_of_forall inf_le_left t htE (fun n hn => ?_)
    rcases pt_invol h n hn.2 (hsq n hn) with hT | hT
    · exact Or.inl ⟨hn, hT⟩
    · right
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ htE) hn, ?_⟩
      rw [ht1]
      exact hT
  have hmul := Subgroup.relIndex_mul_card
    (H := E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam)
    (K := E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam))
  rw [inf_eq_left.mpr (inf_le_left : E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓
    wreathGrp x₁ x₂ lam ≤ E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam)), hE'card] at hmul
  have hDcard : Nat.card ↥(E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam) = 4 := by
    by_contra hne
    have hlt : Nat.card ↥(E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam) ≤ 3 := by
      omega
    have : (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam).relIndex
        (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam)) *
        Nat.card ↥(E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam) ≤ 2 * 3 :=
      Nat.mul_le_mul hidx hlt
    omega
  have hE'eq : E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) =
      zpowers t ⊔ (E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam) := by
    apply le_antisymm
    · intro e he
      rcases pt_invol h e he.2 (hsq e he) with hT | hT
      · exact Subgroup.mem_sup_right ⟨he, hT⟩
      · have hte : t * e ∈ E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓ wreathGrp x₁ x₂ lam :=
          ⟨Subgroup.mul_mem _ htE he, hT⟩
        have he' : e = t⁻¹ * (t * e) := by group
        rw [he']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _
          (Subgroup.mem_zpowers t))) (Subgroup.mem_sup_right hte)
    · exact sup_le (Subgroup.zpowers_le.mpr htE) inf_le_left
  rcases wreath_elem_four_cases h.wreath inf_le_right hDe hDcard with hc | hc | hc
  · left
    rw [hE'eq, hc, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
  · right
    left
    rw [hE'eq, hc, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
  · right
    right
    rw [hE'eq, hc, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]

end E16

end S4A

theorem ctxCentre_holds : CtxCentreStmt :=
  fun h _ hi ht =>
    { normal_W := S4A.ctx_normal_W h ht
      center_ge := S4A.ctx_center_ge h ht
      center_le := S4A.ctx_center_le h hi ht
      center_omega := S4A.ctx_center_omega h hi ht
      m2_PT := S4A.pt_m2 h
      m2_PT_attained := S4A.pt_ctxE_elem h
      E16_cases := S4A.ctx_E16_cases h hi }

end CFSG.OddStandard.SmallF3.HarrisU33
