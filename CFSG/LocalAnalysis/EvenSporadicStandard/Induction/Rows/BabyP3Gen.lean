module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralLift

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Induction.Hyp

theorem eq_one_or_eq_of_mem_zpowers_mul_self {Y : Type*} [Group Y] {c x : Y} (hc : c * c = 1)
    (hx : x ∈ zpowers c) : x = 1 ∨ x = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hc, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hc, one_zpow, one_mul]

section Gen

variable {N : Type*} [Group N] [Finite N]

theorem exists_elemAbelian_centralizer {z : N} (hz : ∀ n : N, n * z = z * n) (hz2 : z * z = 1)
    (hsq : ∀ n : N, n * n = 1 ∨ n * n = z)
    (hcomm : ∀ n m : N, n * m * n⁻¹ * m⁻¹ = 1 ∨ n * m * n⁻¹ * m⁻¹ = z)
    (hcard : 2 ^ 22 ≤ Nat.card N) (g : N) :
    ∃ A : Subgroup N, A ≤ centralizer ({g} : Set N) ∧ (∀ a ∈ A, a * a = 1) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ 8 ≤ Nat.card A := by
  have hZcen : zpowers z ≤ center N :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun n => hz n)
  have hZcard : Nat.card (zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two, hz2]))
  have hbound : ∀ A : Subgroup N, A ≤ zpowers z → (∀ a ∈ A, a * a = 1) →
      Nat.card A ≤ 2 ^ 1 := fun A hA _ =>
    (Subgroup.card_le_of_le hA).trans (by simpa using hZcard)
  have hsqZ : ∀ e : N, e * e ∈ zpowers z := fun e => by
    rcases hsq e with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers z
  have hcommZ : ∀ e f : N, e * f * e⁻¹ * f⁻¹ ∈ zpowers z := fun e f => by
    rcases hcomm e f with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers z
  have hTop : CentralLift (zpowers z) ⊤ 1 :=
    { central := hZcen
      le := le_top
      sq_mem := fun e _ => hsqZ e
      comm_mem := fun e _ f _ => hcommZ e f
      bound := hbound }
  have hC := CentralLift.card_le_mul_card_inf_centralizer hTop (D := ⊤) le_rfl
    (x := g) (Subgroup.mem_top g)
  rw [top_inf_eq, Subgroup.card_top] at hC
  have hzg : zpowers z ≤ centralizer ({g} : Set N) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]
    exact (hz g).symm
  have hE : CentralLift (zpowers z) (centralizer ({g} : Set N)) 1 :=
    { central := hZcen
      le := hzg
      sq_mem := fun e _ => hsqZ e
      comm_mem := fun e _ f _ => hcommZ e f
      bound := hbound }
  have h21 : 2 ^ 21 ≤ Nat.card (centralizer ({g} : Set N)) := by
    have h2 : 2 * 2 ^ 21 ≤ 2 * Nat.card (centralizer ({g} : Set N)) := by
      calc 2 * 2 ^ 21 = 2 ^ 22 := by norm_num
        _ ≤ Nat.card N := hcard
        _ ≤ 2 ^ 1 * Nat.card (centralizer ({g} : Set N)) := hC
        _ = 2 * Nat.card (centralizer ({g} : Set N)) := by norm_num
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hn : 2 ^ 20 * Nat.card (zpowers z) ≤ Nat.card (centralizer ({g} : Set N)) :=
    calc 2 ^ 20 * Nat.card (zpowers z) ≤ 2 ^ 20 * 2 := Nat.mul_le_mul_left _ hZcard
      _ = 2 ^ 21 := by norm_num
      _ ≤ Nat.card (centralizer ({g} : Set N)) := h21
  obtain ⟨A, hAE, hA, k, hk, hAk⟩ :=
    CentralLift.exists_elementaryAbelian_of_central_lift hE hn (t := 3)
      (by intro k hk; interval_cases k <;> norm_num)
  have := hA
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have h1 : (⟨a, ha⟩ : A) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a, ha⟩
    simpa [pow_two] using congrArg Subtype.val h1
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  refine ⟨A, hAE, hAsq, hAcomm, ?_⟩
  rw [hAk]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

end Gen

section Extend

variable {Y : Type*} [Group Y]

theorem bFix_exists_sup_central [Finite Y] {V : Subgroup Y} {c : Y} (hc : ∀ y : Y, y * c = c * y)
    (hc2 : c * c = 1) (hcV : c ∉ V) :
    ∃ A : Subgroup Y, V ≤ A ∧ c ∈ A ∧ Nat.card A = 2 * Nat.card V ∧
      ∀ a ∈ A, a ∈ V ∨ c * a ∈ V := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  let A : Subgroup Y :=
    { carrier := {y | y ∈ V ∨ c * y ∈ V}
      one_mem' := Or.inl V.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (V.mul_mem ha hb)
        · refine Or.inr ?_
          have : c * (a * b) = a * (c * b) := by rw [← mul_assoc, ← hc a, mul_assoc]
          rw [this]
          exact V.mul_mem ha hb
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact V.mul_mem ha hb
        · refine Or.inl ?_
          have : (c * a) * (c * b) = a * b := by
            calc (c * a) * (c * b) = c * (a * c) * b := by group
              _ = c * (c * a) * b := by rw [hc a]
              _ = (c * c) * a * b := by group
              _ = a * b := by rw [hc2, one_mul]
          rw [← this]
          exact V.mul_mem ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (V.inv_mem ha)
        · refine Or.inr ?_
          have : c * a⁻¹ = (c * a)⁻¹ := by rw [mul_inv_rev, hci, hc a⁻¹]
          rw [this]
          exact V.inv_mem ha }
  have hVA : V ≤ A := fun v hv => Or.inl hv
  have hcA : c ∈ A := Or.inr (by rw [hc2]; exact V.one_mem)
  refine ⟨A, hVA, hcA, ?_, fun a ha => ha⟩
  have hset : (A : Set Y) = (V : Set Y) ∪ (fun y => c * y) '' (V : Set Y) := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact Or.inl hy
      · refine Or.inr ⟨c * y, hy, ?_⟩
        show c * (c * y) = y
        rw [← mul_assoc, hc2, one_mul]
    · rintro (hy | ⟨v, hv, rfl⟩)
      · exact Or.inl hy
      · refine Or.inr ?_
        show c * (c * v) ∈ V
        rw [← mul_assoc, hc2, one_mul]
        exact hv
  have hdisj : Disjoint (V : Set Y) ((fun y => c * y) '' (V : Set Y)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨v, hv, rfl⟩
    apply hcV
    have : c = (c * v) * v⁻¹ := by group
    rw [this]
    exact V.mul_mem hy (V.inv_mem hv)
  have hVfin : (V : Set Y).Finite := Set.toFinite _
  have himg : ((fun y => c * y) '' (V : Set Y)).ncard = (V : Set Y).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective c)
  have h1 : Nat.card A = (A : Set Y).ncard := Nat.card_coe_set_eq (A : Set Y)
  have h2 : Nat.card V = (V : Set Y).ncard := Nat.card_coe_set_eq (V : Set Y)
  rw [h1, h2, hset, Set.ncard_union_eq hdisj hVfin (hVfin.image _), himg]
  omega

theorem bFix_mul_self_eq_one_of_isConj {g v : Y} (hg : g * g = 1) (hvg : v * g = g * v)
    (hc : IsConj (v * g) g) : v * v = 1 := by
  obtain ⟨w, hw⟩ := isConj_iff.1 hc
  have h1 : (v * g) * (v * g) = 1 := by
    have h2 : w * ((v * g) * (v * g)) * w⁻¹ = 1 := by
      calc w * ((v * g) * (v * g)) * w⁻¹ = (w * (v * g) * w⁻¹) * (w * (v * g) * w⁻¹) := by group
        _ = g * g := by rw [hw]
        _ = 1 := hg
    simpa using h2
  calc v * v = (v * g) * (v * g) := by
        calc v * v = v * (g * g) * v := by rw [hg, mul_one]
          _ = (v * g) * (g * v) := by group
          _ = (v * g) * (v * g) := by rw [hvg]
    _ = 1 := h1

end Extend

section Reduction

variable {Y : Type*} [Group Y]

theorem fixes_of_aut_conj (M : Subgroup Y) {c : Y} (hc2 : c * c = 1)
    (hcent : centralizer (M : Set Y) = zpowers c) (hsq : ∀ y : Y, y * y ≠ c)
    (haut : ∀ σ : MulAut M, ∃ b : Y, ∀ y : M, ((σ y : M) : Y) = b * y * b⁻¹)
    (hin : ∀ g ∈ M, g * g = 1 → ∃ A : Subgroup Y, A ≤ M ∧ (∀ x ∈ A, g * x = x * g) ∧
      (∀ x ∈ A, x * x = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ 8 ≤ Nat.card A)
    (hout : ∀ g : Y, g ∉ M → g * g = 1 → ∃ A : Subgroup Y, A ≤ M ∧ (∀ x ∈ A, g * x = x * g) ∧
      (∀ x ∈ A, x * x = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ 8 ≤ Nat.card A)
    (α : MulAut M) (hα2 : α * α = 1) :
    ∃ E : Subgroup M, (∀ x ∈ E, α x = x) ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 8 ≤ Nat.card E := by
  obtain ⟨g, hg⟩ := haut α
  have hgg : g * g = 1 := by
    have hcen : g * g ∈ centralizer (M : Set Y) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 : α (α ⟨y, hy⟩) = ⟨y, hy⟩ := by
        have := congrArg (fun σ : MulAut M => σ ⟨y, hy⟩) hα2
        simpa using this
      have h2 : g * (g * y * g⁻¹) * g⁻¹ = y := by
        have := congrArg (fun w : M => (w : Y)) h1
        simpa only [hg] using this
      calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h2]
        _ = (g * g) * y := by group
    rw [hcent] at hcen
    rcases eq_one_or_eq_of_mem_zpowers_mul_self hc2 hcen with h | h
    · exact h
    · exact absurd h (hsq g)
  obtain ⟨A, hAM, hAg, hAsq, hAcomm, hA8⟩ : ∃ A : Subgroup Y, A ≤ M ∧
      (∀ x ∈ A, g * x = x * g) ∧ (∀ x ∈ A, x * x = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      8 ≤ Nat.card A := by
    by_cases hgM : g ∈ M
    · exact hin g hgM hgg
    · exact hout g hgM hgg
  refine ⟨A.subgroupOf M, fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_, ?_⟩
  · have hxA : (x : Y) ∈ A := hx
    apply Subtype.ext
    rw [hg x, hAg _ hxA, mul_inv_cancel_right]
  · have hxA : (x : Y) ∈ A := hx
    exact Subtype.ext (hAsq _ hxA)
  · have hxA : (x : Y) ∈ A := hx
    have hyA : (y : Y) ∈ A := hy
    exact Subtype.ext (hAcomm _ hxA _ hyA)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact hA8

end Reduction

end CFSG.EvenSporadicStandard.Induction
