module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem pt_wreath_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : wreathGrp x₁ x₂ lam ≤ L := by
  rw [← h.inf_eq]
  exact inf_le_right

theorem pt_base_le_wreath (x₁ x₂ lam : G) : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
  refine (Subgroup.closure_le (K := wreathGrp x₁ x₂ lam)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact Subgroup.subset_closure (by simp)
  · rw [hg]
    exact Subgroup.subset_closure (by simp)

theorem pt_base_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L :=
  (pt_base_le_wreath x₁ x₂ lam).trans (pt_wreath_le_L h)

theorem pt_four_le_base (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  refine (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact Subgroup.pow_mem _ hx₁ 2
  · rw [hg]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hx₁ hx₂) 2

theorem pt_four_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : fourGrp x₁ x₂ ≤ L :=
  (pt_four_le_base x₁ x₂).trans (pt_base_le_L h)

theorem pt_comm_wreath (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ a ∈ twoCore t, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a :=
  fun a ha b hb => twoCore_commute h.hyp a ha b (pt_wreath_le_L h hb)

theorem pt_comm_base (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
  fun a ha b hb => twoCore_commute h.hyp a ha b (pt_base_le_L h hb)

theorem pt_inf_wreath (h : Ctx0 t L S x₁ x₂ lam rho) :
    twoCore t ⊓ wreathGrp x₁ x₂ lam = ⊥ := by
  have : twoCore t ⊓ wreathGrp x₁ x₂ lam ≤ twoCore t ⊓ L :=
    inf_le_inf_left _ (pt_wreath_le_L h)
  rw [h.hyp.twoCore_inf] at this
  exact le_bot_iff.mp this

theorem pt_inf_base (h : Ctx0 t L S x₁ x₂ lam rho) : twoCore t ⊓ baseGrp x₁ x₂ = ⊥ := by
  have : twoCore t ⊓ baseGrp x₁ x₂ ≤ twoCore t ⊓ L := inf_le_inf_left _ (pt_base_le_L h)
  rw [h.hyp.twoCore_inf] at this
  exact le_bot_iff.mp this

theorem pt_card (h : Ctx0 t L S x₁ x₂ lam rho) :
    Nat.card ↥(twoCore t ⊔ wreathGrp x₁ x₂ lam) = 2 ^ 5 * Nat.card ↥(twoCore t) := by
  rw [card_sup_of_commute (pt_comm_wreath h) (pt_inf_wreath h), h.wreath.card_wreathGrp]
  ring

theorem pt_card_W (h : Ctx0 t L S x₁ x₂ lam rho) :
    Nat.card ↥(ctxW t x₁ x₂) = 2 ^ 4 * Nat.card ↥(twoCore t) := by
  rw [ctxW, card_sup_of_commute (pt_comm_base h) (pt_inf_base h), (h.wreath.baseGrp_eq).2.2]
  ring

theorem pt_W_le (t : G) (x₁ x₂ lam : G) : ctxW t x₁ x₂ ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
  sup_le_sup_left (pt_base_le_wreath x₁ x₂ lam) _

theorem pt_relIndex_W (h : Ctx0 t L S x₁ x₂ lam rho) :
    (ctxW t x₁ x₂).relIndex (twoCore t ⊔ wreathGrp x₁ x₂ lam) = 2 := by
  have hle := pt_W_le t x₁ x₂ lam
  have hmul := Subgroup.relIndex_mul_card (H := ctxW t x₁ x₂)
    (K := twoCore t ⊔ wreathGrp x₁ x₂ lam)
  rw [inf_eq_left.mpr hle, pt_card h, pt_card_W h] at hmul
  have hpos : 0 < 2 ^ 4 * Nat.card ↥(twoCore t) := by
    have : 0 < Nat.card ↥(twoCore t) := Nat.card_pos
    positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hmul]
  ring

theorem pt_normalIn_W (h : Ctx0 t L S x₁ x₂ lam rho) :
    NormalIn (ctxW t x₁ x₂) (twoCore t ⊔ wreathGrp x₁ x₂ lam) := by
  have hle := pt_W_le t x₁ x₂ lam
  have hnorm : ((ctxW t x₁ x₂).subgroupOf (twoCore t ⊔ wreathGrp x₁ x₂ lam)).Normal :=
    Subgroup.normal_of_index_eq_two (pt_relIndex_W h)
  refine ⟨hle, fun g hg k hk => ?_⟩
  exact (Subgroup.normal_subgroupOf_iff hle).mp hnorm k g hk hg

theorem pt_eq_one_or_of_mem_zpowers {g x : G} (hg : orderOf g = 2) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : g ^ k = g ^ (k % 2) := by
    have := zpow_mod_orderOf g k
    rw [hg] at this
    simpa using this.symm
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    rw [hk, h0]
    simp
  · right
    rw [hk, h0]
    simp

theorem pt_ctxE_eq_sup (t x₁ x₂ : G) : ctxE t x₁ x₂ = zpowers t ⊔ fourGrp x₁ x₂ := by
  rw [ctxE, fourGrp, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]

theorem pt_ctxE_elem (h : Ctx0 t L S x₁ x₂ lam rho) :
    CFSG.Open.IsElemAbelian 2 (ctxE t x₁ x₂) ∧ Nat.card ↥(ctxE t x₁ x₂) = 8 := by
  obtain ⟨-, hFe, hFcard⟩ := h.wreath.fourGrp_eq_omega
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : Commute t b := (mem_invCent_iff.mp (L_le_invCent h.hyp (pt_four_le_L h hb))).symm
    exact (hc.zpow_left k).eq
  have hinf : zpowers t ⊓ fourGrp x₁ x₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxf⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hxt with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ pt_four_le_L h hxf) (t_not_mem_L h.hyp)
  rw [pt_ctxE_eq_sup]
  refine ⟨⟨isMulCommutative_sup_of_commute hcomm inferInstance hFe.1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
    have hab : Commute a b := hcomm a ha b hb
    rw [hab.mul_pow]
    have ha2 : a ^ 2 = 1 := by
      rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t ha with h1 | h1
      · rw [h1]
        simp
      · rw [h1, pow_two]
        exact t_mul_self h.hyp
    rw [ha2, hFe.2 b hb, one_mul]
  · rw [card_sup_of_commute hcomm hinf, Nat.card_zpowers, h.hyp.ord_t, hFcard]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
