module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Reflect

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

set_option linter.unusedSectionVars false

section Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem S11_pow3_u (hb : PAB G L t E W z) (a : PA10 L t E z) {g : G} (hg : g ∈ zpowers a.u)
    (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hg
  have h2 : g * g = 1 := by
    rw [← hn, ← zpow_add, ← two_mul, zpow_mul]
    have : a.u ^ (2 : ℤ) = 1 := by rw [zpow_two, S11_u_sq hb a]
    rw [this, one_zpow]
  calc g = g ^ 3 := by rw [pow_succ, pow_two, h2, one_mul]
    _ = 1 := h3

theorem S11_O_le_T (hb : PAB G L t E W z) (a : PA10 L t E z) {x : G} {hx : x ∈ a.L₁}
    {X : Subgroup G} (hX : S11XData a hx X) (hx3 : orderOf x = 3)
    (hxy : a.y = x * (t * x * t⁻¹)) : S11_O a ≤ X ⊔ conjSub t X := by
  have hO9 := S11_card_O hb hX hx3 hxy
  have hB : Nat.card ↥(Cen a.y ⊓ Cen a.u) = 2592 := by rw [S11_card_B hb a, hO9]
  obtain ⟨hT81, hTle⟩ := S11_T_facts hb hX hxy
  have hOB : S11_O a ≤ Cen a.y ⊓ Cen a.u := fun o ho =>
    ⟨S11_O_mem_Cen a ho, mem_Cen.2 (S11_u_comm_O hb a o ho).symm⟩
  have hnorm : ((S11_O a).subgroupOf (Cen a.y ⊓ Cen a.u)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact S11_O_conj a g.2.1 hn
  have hN : Nat.card ((S11_O a).subgroupOf (Cen a.y ⊓ Cen a.u)) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOB).toEquiv, hO9]
  have hT : Nat.card ((X ⊔ conjSub t X).subgroupOf (Cen a.y ⊓ Cen a.u)) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv, hT81]
  have := s11_le_of_card _ _ hB hN hT
  intro o ho
  have h1 : (⟨o, hOB ho⟩ : ↥(Cen a.y ⊓ Cen a.u)) ∈ (S11_O a).subgroupOf (Cen a.y ⊓ Cen a.u) := ho
  exact this h1

end Final

theorem s11 : StepS11 := by
  intro G _ _ L t E W z hb a
  have ht := hb.t_mul_t
  obtain ⟨x, hx, hx3, hxy⟩ := S11_exists_x hb a
  obtain ⟨X, hX⟩ := S11_exists_XData hb a hx hx3
  have hO9 := S11_card_O hb hX hx3 hxy
  have hB : Nat.card ↥(Cen a.y ⊓ Cen a.u) = 2592 := by rw [S11_card_B hb a, hO9]
  obtain ⟨g, hgy, hgu, hgx, hgXt, hgX, hgsq, hgnt⟩ := S11_reflection hb a hx hx3 hxy hX hB
  have hOle := S11_O_le_T hb a hX hx3 hxy
  have hxX : x ∈ X := hX.mem_x hx3
  have hOT : ∀ o ∈ S11_O a, ∃ c ∈ X, ∃ b ∈ conjSub t X, o = c * b := fun o ho =>
    s11_exists_mul_of_mem_sup (hX.comm hb) (hOle ho)
  have hOinv : ∀ o ∈ S11_O a, t * o * t⁻¹ * o ∈ zpowers (x * (t * x * t⁻¹)) := by
    intro o ho
    have := a.O_inv o ho
    rwa [hxy] at this
  have hplane := s11_plane (X := X) (Xt := conjSub t X) (O := S11_O a) ht hx3 hxX hX.card
    (fun c hc => ⟨c, hc, rfl⟩) (hX.comm hb) (hX.inf hb) hOinv
    (fun o ho => S11_O_conj a hgy ho) hOT
    (fun b ⟨c, hc, hcb⟩ => ⟨c, hc, hcb.symm⟩) hgx hgXt hgX hgsq hgnt
  have hxt : t * x * t⁻¹ ∈ conjSub t a.L₁ := ⟨x, hx, rfl⟩
  have hxt3 : orderOf (t * x * t⁻¹) = 3 := by
    have h1 : (t * x * t⁻¹) ^ 3 = 1 := by
      rw [conj_pow]
      have := pow_orderOf_eq_one x
      rw [hx3] at this
      rw [this]; group
    have h2 : t * x * t⁻¹ ≠ 1 := by
      intro h
      have : x = 1 := by
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at hx3
      omega
    exact orderOf_eq_prime h1 h2
  have hcm : Cm (zpowers x) (zpowers (t * x * t⁻¹)) :=
    cm_zpowers_zpowers (S11_comm_L₁t hb a x hx _ hxt)
  have hbot : zpowers x ⊓ zpowers (t * x * t⁻¹) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hw1 : w ∈ a.L₁ := (zpowers_le.2 hx) hw.1
    have hw2 : w ∈ conjSub t a.L₁ := (zpowers_le.2 hxt) hw.2
    have hw3 : w ^ 3 = 1 := by
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hw.1
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      have := pow_orderOf_eq_one x
      rw [hx3] at this
      simp [this]
    exact S11_pow3_u hb a (S11_inter_le hb a hw1 hw2) hw3
  have hA9 : Nat.card ↥(zpowers x ⊔ zpowers (t * x * t⁻¹)) = 9 := by
    rw [card_sup_of_cm hcm hbot, Nat.card_zpowers, Nat.card_zpowers, hx3, hxt3]
  have hOA : S11_O a = zpowers x ⊔ zpowers (t * x * t⁻¹) :=
    Subgroup.eq_of_le_of_card_ge (fun o ho => hplane o ho) (by rw [hO9, hA9])
  have hxO : x ∈ Open.fusionOddCoreOf (Cen a.y) := by
    have h1 : x ∈ zpowers x ⊔ zpowers (t * x * t⁻¹) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have h2 : x ∈ S11_O a := by rw [hOA]; exact h1
    exact h2
  have hCy : Nat.card ↥(Cen a.y) = 259200 := by
    rw [S11_card_Cy a, hO9]
  exact ⟨{ toPA10 := a
           x := x
           x_mem := hx
           x_ord := hx3
           x_y := hxy
           x_O := hxO
           O_eq := hOA
           card_Cy := hCy
           X := X
           X_le := hX.le
           X_card := hX.card
           X_three := hX.three }⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
