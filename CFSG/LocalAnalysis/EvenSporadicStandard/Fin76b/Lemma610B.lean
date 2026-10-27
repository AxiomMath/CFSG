module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

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
  have hgen : h.conf.econfig.gen ▸ (rfl : E = E) = (rfl : E = E) := rfl
  have hEle : E ≤ D := by
    have := h.conf.econfig.gen
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
  obtain ⟨eB⟩ := h.conf.B_iso
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
  rcases h.wf.cent y (h.conf.B_le hyB) (fun e he => hcomm e he) with h1 | h1
  · rw [h1, orderOf_one] at hy5; omega
  · rw [h1, h.conf.cfg.t_order] at hy5; omega

theorem B_inf_F {α : G} (hα : AlphaSpec S z t α) {b : G} (hbB : b ∈ B)
    (hbF : b ∈ Fsub h hα) : b = 1 := by
  obtain ⟨eB⟩ := h.conf.B_iso
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

end Hyp69

theorem card_modEq_fixed {α : Type*} [Finite α] (σ : Equiv.Perm α) (h5 : σ ^ 5 = 1) :
    Nat.card α ≡ Nat.card (Function.fixedPoints σ) [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := Fintype.ofFinite α
  let f : Function.End α := ⇑σ
  have hpow : ∀ k : ℕ, f ^ k = (⇑(σ ^ k) : Function.End α) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) (by
    rw [pow_one, hpow, h5]; rfl)
  have e : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  have e2 : Nat.card (Function.fixedPoints σ) = Fintype.card ↑(Function.fixedPoints f) := by
    rw [Nat.card_eq_fintype_card]
  rw [e, e2]
  exact h

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem fix_E {y : G} (hyB : y ∈ B) (hy5 : orderOf y = 5) {e : G} (he : e ∈ E)
    (hfix : y * e * y⁻¹ = e) : e = 1 ∨ e = t := by
  classical
  have hyW := h.B_le_W hyB
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 hyW.2
  have hy5' : y ^ 5 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy5] at this
  let σ : Equiv.Perm ↥E :=
    { toFun := fun x => ⟨y * x * y⁻¹, h.W_norm_E hyW x.2⟩
      invFun := fun x => ⟨y⁻¹ * x * y, by simpa using h.W_norm_E (inv_mem hyW) x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  have hσk : ∀ (k : ℕ) (x : ↥E), (((σ ^ k) x : ↥E) : G) = y ^ k * x * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show y ^ k * (y * (x : G) * y⁻¹) * (y ^ k)⁻¹ = y ^ (k + 1) * x * (y ^ (k + 1))⁻¹
      rw [pow_succ]; group
  have hσ5 : σ ^ 5 = 1 := by
    ext x
    rw [hσk, hy5']
    simp
  have hmod := card_modEq_fixed σ hσ5
  have hE32 : Nat.card ↥E = 32 := h.wf.card_E
  set C : Subgroup G := E ⊓ centralizer ({y} : Set G) with hC
  have hfixset : Function.fixedPoints σ = ((C.subgroupOf E : Subgroup ↥E) : Set ↥E) := by
    ext x
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, SetLike.mem_coe, mem_subgroupOf, hC,
      mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      have h2 : y * (x : G) * y⁻¹ = x := this
      calc (x : G) * y = (y * x * y⁻¹) * y := by rw [h2]
        _ = y * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      show y * (x : G) * y⁻¹ = x
      calc y * (x : G) * y⁻¹ = (x * y) * y⁻¹ := by rw [hx]
        _ = x := by group
  rw [hfixset] at hmod
  have hcd : Nat.card ↥(C.subgroupOf E) ∣ 32 := by
    rw [← hE32]; exact Subgroup.card_subgroup_dvd_card _
  have hmod' : 32 ≡ Nat.card ↥(C.subgroupOf E) [MOD 5] := by
    have := hmod
    rwa [hE32] at this
  have hc : Nat.card ↥(C.subgroupOf E) = 2 ∨ Nat.card ↥(C.subgroupOf E) = 32 := by
    obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 5 by simpa using hcd)
    rw [hk2] at hmod' ⊢
    clear hcd hmod hfixset hk2
    interval_cases k
    · exfalso; revert hmod'; decide
    · left; norm_num
    · exfalso; revert hmod'; decide
    · exfalso; revert hmod'; decide
    · exfalso; revert hmod'; decide
    · right; norm_num
  have he_cent : e * y = y * e := by
    calc e * y = (y * e * y⁻¹) * y := by rw [hfix]
      _ = y * e := by group
  rcases hc with hc2 | hc32
  · obtain ⟨a, b, hab, hall⟩ := Nat.card_eq_two_iff.1 hc2
    have h1 : (⟨1, one_mem E⟩ : ↥E) ∈ C.subgroupOf E :=
      mem_subgroupOf.2 ⟨one_mem _, one_mem _⟩
    have ht : (⟨t, h.t_mem_E⟩ : ↥E) ∈ C.subgroupOf E :=
      mem_subgroupOf.2 ⟨h.t_mem_E, mem_centralizer_singleton_iff.2 hyt.symm⟩
    have he' : (⟨e, he⟩ : ↥E) ∈ C.subgroupOf E :=
      mem_subgroupOf.2 ⟨he, mem_centralizer_singleton_iff.2 he_cent⟩
    have hx : ∀ x : ↥(C.subgroupOf E), x = a ∨ x = b := fun x => by
      have : x ∈ ({a, b} : Set ↥(C.subgroupOf E)) := by rw [hall]; exact Set.mem_univ x
      simpa using this
    have h12 : (⟨⟨1, one_mem E⟩, h1⟩ : ↥(C.subgroupOf E)) ≠ ⟨⟨t, h.t_mem_E⟩, ht⟩ := by
      intro hh
      apply h.t_ne
      have := congrArg (fun p : ↥(C.subgroupOf E) => ((p : ↥E) : G)) hh
      exact this.symm
    have key : ∀ p1 p2 p3 : ↥(C.subgroupOf E), p1 ≠ p2 → (p1 = a ∨ p1 = b) → (p2 = a ∨ p2 = b) →
        (p3 = a ∨ p3 = b) → p3 = p1 ∨ p3 = p2 := by
      intro p1 p2 p3 hne h1 h2 h3
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
        simp_all
    rcases key _ _ ⟨⟨e, he⟩, he'⟩ h12 (hx _) (hx _) (hx _) with hh | hh
    · left
      exact congrArg (fun p : ↥(C.subgroupOf E) => ((p : ↥E) : G)) hh
    · right
      exact congrArg (fun p : ↥(C.subgroupOf E) => ((p : ↥E) : G)) hh
  · exfalso
    have htop : C.subgroupOf E = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hc32, hE32]
    have hcomm : ∀ x ∈ E, y * x = x * y := by
      intro x hx
      have : (⟨x, hx⟩ : ↥E) ∈ C.subgroupOf E := by rw [htop]; exact mem_top _
      have h2 := (mem_centralizer_singleton_iff.1 (mem_subgroupOf.1 this).2)
      exact h2.symm
    rcases h.wf.cent y (h.conf.B_le hyB) (fun e he => hcomm e he) with h1 | h1
    · rw [h1, orderOf_one] at hy5; omega
    · rw [h1, h.conf.cfg.t_order] at hy5; omega

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
