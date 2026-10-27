module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem Fnorm_acts_on_E {α : G} (hα : AlphaSpec S z t α) {f : G} (hf : f ∈ Fsub h hα)
    (hfE : ∀ e ∈ E, f * e * f⁻¹ ∈ E) {x : G} (hx : x ∈ E) :
    f * x * f⁻¹ = x ∨ f * x * f⁻¹ = t * x := by
  have hE2 : ∀ e ∈ E2 E t, f * e * f⁻¹ = e ∨ f * e * f⁻¹ = t * e := by
    intro e he
    obtain ⟨a, ha, hae⟩ := hf.2 e he
    have haE : a ∈ E := by
      have : a = (f * e * f⁻¹) * e⁻¹ := by rw [hae]; group
      rw [this]
      exact mul_mem (hfE e he.1) (inv_mem he.1)
    rcases (h.mem_Zg hα).1 ha with h1 | h1 | h1 | h1
    · left; rw [hae, h1, one_mul]
    · right; rw [hae, h1]
    · exfalso
      rw [h1] at haE
      rcases h.S_inf_E hα.mem haE with h2 | h2
      · exact hα.ne_one h2
      · exact hα.ne_t h2
    · exfalso
      have : α ∈ E := by
        have : α = (a) * t := by rw [h1, mul_assoc, h.t_sq, mul_one]
        rw [this]; exact mul_mem haE h.t_mem_E
      rcases h.S_inf_E hα.mem this with h2 | h2
      · exact hα.ne_one h2
      · exact hα.ne_t h2
  let D : Subgroup G :=
    { carrier := {x | x ∈ E ∧ (f * x * f⁻¹ = x ∨ f * x * f⁻¹ = t * x)}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hcomm : ∀ c ∈ E, t * c = c * t := fun c hc => (h.t_comm_E c hc).symm
        have e1 : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
        rw [e1]
        rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rw [h1, h2]
        · left; rfl
        · right
          calc a * (t * b) = (a * t) * b := by group
            _ = (t * a) * b := by rw [(hcomm a ha).symm]
            _ = t * (a * b) := by group
        · right; group
        · left
          calc t * a * (t * b) = t * (a * t) * b := by group
            _ = t * (t * a) * b := by rw [(hcomm a ha).symm]
            _ = (t * t) * a * b := by group
            _ = a * b := by rw [h.t_sq, one_mul]
      one_mem' := ⟨one_mem _, Or.inl (by group)⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have hcomm : ∀ c ∈ E, t * c = c * t := fun c hc => (h.t_comm_E c hc).symm
        have e1 : f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
        rw [e1]
        rcases ha' with h1 | h1 <;> rw [h1]
        · left; rfl
        · right
          calc (t * a)⁻¹ = a⁻¹ * t⁻¹ := by group
            _ = a⁻¹ * t := by rw [inv_eq_of_mul_eq_one_right h.t_sq]
            _ = t * a⁻¹ := ((hcomm a⁻¹ (inv_mem ha)).symm) }
  have hgen : h.oe.econfig.gen ▸ (rfl : E = E) = (rfl : E = E) := rfl
  have hEle : E ≤ D := by
    have := h.oe.econfig.gen
    rw [this]
    rw [closure_le]
    intro e he
    obtain ⟨heE, he2, he1⟩ := he
    by_cases het : e = t
    · refine ⟨heE, Or.inl ?_⟩
      rw [het]; exact h.conj_t_of_M (hf.1)
    · exact ⟨heE, hE2 e ⟨heE, he2, he1, het⟩⟩
  exact (hEle hx).2

theorem B_card : Nat.card ↥B = 60 := by
  obtain ⟨eB⟩ := h.ob.B_iso
  rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem order_five_not_F {α : G} (hα : AlphaSpec S z t α) {y : G} (hyB : y ∈ B)
    (hy5 : orderOf y = 5) : y ∉ Fsub h hα := by
  intro hyF
  have hyW := h.B_le_W hyB
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 hyW.2
  have hcomm : ∀ x ∈ E, y * x = x * y := by
    intro x hx
    have h1 := h.Fnorm_acts_on_E hα hyF (fun e he => h.W_norm_E hyW he) hx
    have hy2 : (y * y) * x = x * (y * y) := by
      rcases h1 with h1 | h1
      · have h1' : y * x = x * y := by
          calc y * x = (y * x * y⁻¹) * y := by group
            _ = x * y := by rw [h1]
        calc (y * y) * x = y * (y * x) := by group
          _ = y * (x * y) := by rw [h1']
          _ = (y * x) * y := by group
          _ = (x * y) * y := by rw [h1']
          _ = x * (y * y) := by group
      · have h2 : y * x = t * x * y := by
          calc y * x = (y * x * y⁻¹) * y := by group
            _ = t * x * y := by rw [h1]
        calc (y * y) * x = y * (y * x) := by group
          _ = y * (t * x * y) := by rw [h2]
          _ = (y * t) * x * y := by group
          _ = (t * y) * x * y := by rw [hyt]
          _ = t * (y * x) * y := by group
          _ = t * (t * x * y) * y := by rw [h2]
          _ = (t * t) * x * (y * y) := by group
          _ = x * (y * y) := by rw [h.t_sq, one_mul]
    have hc2 : Commute (y * y) x := hy2
    have hy5' : y ^ 5 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy5] at this
    have hy6 : (y * y) ^ 3 = y := by
      calc (y * y) ^ 3 = y ^ 6 := by rw [← pow_two, ← pow_mul]
        _ = y ^ 5 * y := pow_succ y 5
        _ = y := by rw [hy5', one_mul]
    have := (hc2.pow_left 3).eq
    rwa [hy6] at this
  rcases h.wf.cent y (h.ob.B_le hyB) (fun e he => hcomm e he) with h1 | h1
  · rw [h1, orderOf_one] at hy5; omega
  · rw [h1, h.oe.cfg.t_order'] at hy5; omega

theorem B_inf_F {α : G} (hα : AlphaSpec S z t α) {b : G} (hbB : b ∈ B)
    (hbF : b ∈ Fsub h hα) : b = 1 := by
  obtain ⟨eB⟩ := h.ob.B_iso
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥B := MulEquiv.isSimpleGroup eB
  have hnorm : ((Fsub h hα ⊓ B).subgroupOf B).Normal := by
    refine ⟨fun k hk b' => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    exact ⟨h.Fsub_normal hα (h.W_mem_M (h.B_le_W b'.2)) hk.1, (b' * ⟨_, hk.2⟩ * b'⁻¹).2⟩
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Fsub h hα ⊓ B).subgroupOf B) with h1 | h1
  · have : (⟨b, hbB⟩ : ↥B) ∈ (Fsub h hα ⊓ B).subgroupOf B := mem_subgroupOf.2 ⟨hbF, hbB⟩
    rw [h1, mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have hBF : ∀ y ∈ B, y ∈ Fsub h hα := fun y hy => by
      have : (⟨y, hy⟩ : ↥B) ∈ (Fsub h hα ⊓ B).subgroupOf B := by rw [h1]; exact mem_top _
      exact (mem_subgroupOf.1 this).1
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [h.B_card]; norm_num :
      5 ∣ Nat.card ↥B)
    exact h.order_five_not_F hα y.2 (by rw [← Subgroup.orderOf_coe] at hy; exact hy)
      (hBF y y.2)

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
