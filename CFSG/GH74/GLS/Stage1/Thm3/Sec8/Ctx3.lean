module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem four_comm (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
  have := hs.U_four.1
  intro a ha b hb
  exact setLike_mul_comm ha hb

theorem four_sq (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : ∀ a ∈ U, a * a = 1 := by
  have := hs.U_four.1
  intro a ha
  have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
  simpa [pow_two] using h1

theorem U_elems (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ y ∈ U, y = 1 ∨ y = z ∨ y = u ∨ y = u * z :=
  Basic.four_elems hs.z_sq hs.U_four.2 hs.z_mem hs.u_mem hs.z_ne hs.u_ne

theorem W₁_le_Q₁ (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : W₁ ≤ Qof S K₁ := hs.W₁_max.1

theorem W₂_le_Q₂ (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : W₂ ≤ Qof S K₂ := hs.W₂_max.1

theorem U_le_S1 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : U ≤ S1 S K₁ :=
  hs.U_le.trans (sup_le ((hs.W₁_le_Q₁).trans (hs.Q₁_le_S1)) ((hs.W₂_le_Q₂).trans (hs.Q₂_le_S1 hII)))

theorem U_le_S (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : U ≤ S :=
  (hs.U_le_S1 hII).trans S1_le_S

theorem W₁_normal_Q₁ (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ x ∈ Qof S K₁, ∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁ :=
  fun _ hx _ hw => hs.W₁_norm _ (hs.Q₁_le_S1 hx) _ hw

theorem W₂_normal_Q₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ x ∈ Qof S K₂, ∀ w ∈ W₂, x * w * x⁻¹ ∈ W₂ :=
  fun _ hx _ hw => hs.W₂_norm _ (hs.Q₂_le_S1 hII hx) _ hw

theorem card_W₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    2 * Nat.card ↥W₁ = Nat.card ↥(Qof S K₁) :=
  (hs.gq_Q₁ hII).card_of_normal_maxCyclic hs.W₁_max.1 hs.W₁_max.2.1 hs.W₁_max.2.2
    hs.W₁_normal_Q₁

theorem card_W₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    2 * Nat.card ↥W₂ = Nat.card ↥(Qof S K₂) :=
  (hs.gq_Q₂ hII).card_of_normal_maxCyclic hs.W₂_max.1 hs.W₂_max.2.1 hs.W₂_max.2.2
    (hs.W₂_normal_Q₂ hII)

theorem relIndex_W₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    W₂.relIndex (Qof S K₂) = 2 := by
  have h1 := Basic.card_mul_relIndex_of_le hs.W₂_max.1
  have h2 := hs.card_W₂ hII
  have hpos : 0 < Nat.card ↥W₂ := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by omega)

theorem relIndex_W₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    W₁.relIndex (Qof S K₁) = 2 := by
  have h1 := Basic.card_mul_relIndex_of_le hs.W₁_max.1
  have h2 := hs.card_W₁ hII
  have hpos : 0 < Nat.card ↥W₁ := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by omega)

theorem card_V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    2 * Nat.card ↥(Vof S K₁ W₂) = Nat.card ↥(Pof S K₁) :=
  Basic.two_mul_card_inf (hs.P₁_le_Q₂ hII) hs.W₂_max.2.1 (hs.relIndex_W₂ hII)
    (hs.gq_P hII hq (Or.inl rfl)).not_isCyclic

theorem card_V₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    2 * Nat.card ↥(Vof S K₂ W₁) = Nat.card ↥(Pof S K₂) :=
  Basic.two_mul_card_inf (hs.P₂_le_Q₁ hII) hs.W₁_max.2.1 (hs.relIndex_W₁ hII)
    (hs.gq_P hII hq (Or.inr rfl)).not_isCyclic

theorem four_le_V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    4 ≤ Nat.card ↥(Vof S K₁ W₂) := by
  have := (hs.gq_P hII hq (Or.inl rfl)).eight_le_card
  have := hs.card_V₁ hII hq
  omega

theorem four_le_V₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    4 ≤ Nat.card ↥(Vof S K₂ W₁) := by
  have := (hs.gq_P hII hq (Or.inr rfl)).eight_le_card
  have := hs.card_V₂ hII hq
  omega

theorem V₁_pgroup (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    IsPGroup 2 ↥(Vof S K₁ W₂) :=
  (hs.S_pgroup hII).to_le ((inf_le_right : Vof S K₁ W₂ ≤ Pof S K₁).trans inf_le_left)

theorem V₂_pgroup (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    IsPGroup 2 ↥(Vof S K₂ W₁) :=
  (hs.S_pgroup hII).to_le ((inf_le_right : Vof S K₂ W₁ ≤ Pof S K₂).trans inf_le_left)

theorem V₁_normal (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ x ∈ S1 S K₁, ∀ y ∈ Vof S K₁ W₂, x * y * x⁻¹ ∈ Vof S K₁ W₂ :=
  fun x hx y hy => ⟨hs.W₂_norm x hx y hy.1, hs.S1_normalizes_P hII (Or.inl rfl) x hx y hy.2⟩

theorem V₂_normal (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ x ∈ S1 S K₁, ∀ y ∈ Vof S K₂ W₁, x * y * x⁻¹ ∈ Vof S K₂ W₁ :=
  fun x hx y hy => ⟨hs.W₁_norm x hx y hy.1, hs.S1_normalizes_P hII (Or.inr rfl) x hx y hy.2⟩

theorem W_comm_U (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    (∀ c ∈ W₂, ∀ y ∈ U, c * y = y * c) ∧ (∀ c ∈ W₁, ∀ y ∈ U, c * y = y * c) := by
  have hz2 := hs.z_sq
  have hQ12 := hs.Q_inf_Q hII
  have hu2 : u * u = 1 := hs.four_sq u hs.u_mem
  obtain ⟨hc2, hc1⟩ := Basic.commute_of_involution_mem_sup (z := z) (u := u) (W₁ := W₁) (W₂ := W₂)
    (V₁ := Vof S K₁ W₂) (V₂ := Vof S K₂ W₁) hz2 hs.W₁_max.2.1 hs.W₂_max.2.1
    inf_le_left inf_le_left (hs.V₁_pgroup hII) (hs.V₂_pgroup hII) (hs.four_le_V₁ hII hq)
    (hs.four_le_V₂ hII hq)
    (fun a ha b hb => (hs.Q_comm_P hII (Or.inl rfl) b (hs.W₁_le_Q₁ hb) a ha.2).symm)
    (fun a ha b hb => (hs.Q_comm_P hII (Or.inr rfl) b (hs.W₂_le_Q₂ hb) a ha.2).symm)
    (fun b hb a ha => hs.W₁_norm b ((hs.Q₂_le_S1 hII) (hs.W₂_le_Q₂ hb)) a ha)
    (fun a ha b hb => hs.W₂_norm a ((hs.Q₁_le_S1) (hs.W₁_le_Q₁ ha)) b hb)
    (fun x hx1 hx2 => by
      have hx : x ∈ Qof S K₁ ⊓ Qof S K₂ := ⟨hs.W₁_le_Q₁ hx1, hs.W₂_le_Q₂ hx2⟩
      rw [hQ12] at hx
      exact (M.mem_zpowers_of_sq hz2).1 hx)
    (hs.U_le hs.u_mem) hu2
  have hzc : ∀ c ∈ S, c * z = z * c := by
    intro c hc
    have := hs.S_le_C hII hc
    exact ((Subgroup.mem_centralizer_iff.1 this) z (Set.mem_singleton z)).symm
  refine ⟨fun c hc y hy => ?_, fun c hc y hy => ?_⟩
  · have hcS : c ∈ S := (hs.W₂_le_Q₂ hc).1
    rcases hs.U_elems y hy with rfl | rfl | rfl | rfl
    · simp
    · exact hzc c hcS
    · exact hc2 c hc
    · calc c * (u * z) = (c * u) * z := by group
        _ = (u * c) * z := by rw [hc2 c hc]
        _ = u * (c * z) := by group
        _ = u * (z * c) := by rw [hzc c hcS]
        _ = u * z * c := by group
  · have hcS : c ∈ S := (hs.W₁_le_Q₁ hc).1
    rcases hs.U_elems y hy with rfl | rfl | rfl | rfl
    · simp
    · exact hzc c hcS
    · exact hc1 c hc
    · calc c * (u * z) = (c * u) * z := by group
        _ = (u * c) * z := by rw [hc1 c hc]
        _ = u * (c * z) := by group
        _ = u * (z * c) := by rw [hzc c hcS]
        _ = u * z * c := by group

theorem W₂_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    W₂ ≤ Wsub S U := fun c hc =>
  ⟨(hs.W₂_le_Q₂ hc).1, Subgroup.mem_centralizer_iff.2 fun y hy => ((hs.W_comm_U hII hq).1 c hc y hy).symm⟩

theorem W₁_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    W₁ ≤ Wsub S U := fun c hc =>
  ⟨(hs.W₁_le_Q₁ hc).1, Subgroup.mem_centralizer_iff.2 fun y hy => ((hs.W_comm_U hII hq).2 c hc y hy).symm⟩

theorem V₁_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Vof S K₁ W₂ ≤ Wsub S U := inf_le_left.trans (hs.W₂_le_W hII hq)

theorem V₂_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Vof S K₂ W₁ ≤ Wsub S U := inf_le_left.trans (hs.W₁_le_W hII hq)

theorem W_le_S : Wsub S U ≤ S := inf_le_left

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
