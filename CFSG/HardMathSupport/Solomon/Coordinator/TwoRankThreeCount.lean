module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup

section Count

variable {V : Type*} [CommGroup V] {A : Type*} [CommGroup A]

@[expose] def tr3Fixer (ρ : A →* MulAut V) (U : Subgroup V) : Subgroup A where
  carrier := {a | ∀ u ∈ U, ρ a u = u}
  mul_mem' {a b} ha hb u hu := by
    rw [map_mul, MulAut.mul_apply, hb u hu, ha u hu]
  one_mem' u _ := by rw [map_one, MulAut.one_apply]
  inv_mem' {a} ha u hu := by
    rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq, ha u hu]

@[expose] def tr3Disp (ρ : A →* MulAut V) (a : A) : V →* V where
  toFun v := ρ a v * v⁻¹
  map_one' := by rw [map_one, inv_one, mul_one]
  map_mul' v w := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem tr3_disp_apply (ρ : A →* MulAut V) (a : A) (v : V) : tr3Disp ρ a v = ρ a v * v⁻¹ :=
  rfl

theorem tr3_mem_ker_disp {ρ : A →* MulAut V} {a : A} {v : V} :
    v ∈ (tr3Disp ρ a).ker ↔ ρ a v = v := by
  rw [MonoidHom.mem_ker, tr3_disp_apply, mul_inv_eq_one]

theorem tr3_comm_apply (ρ : A →* MulAut V) (a b : A) (v : V) : ρ a (ρ b v) = ρ b (ρ a v) := by
  rw [← MulAut.mul_apply, ← map_mul, mul_comm, map_mul, MulAut.mul_apply]

theorem tr3_disp_comm (ρ : A →* MulAut V) (a b : A) (v : V) :
    tr3Disp ρ a (tr3Disp ρ b v) = tr3Disp ρ b (tr3Disp ρ a v) := by
  simp only [tr3_disp_apply, map_mul, map_inv, tr3_comm_apply ρ a b]
  simp only [mul_inv_rev, inv_inv, mul_comm, mul_assoc, mul_left_comm]

theorem tr3_pow_apply_of_fixed (α : MulAut V) (v : V) (hfix : α (α v * v⁻¹) = α v * v⁻¹)
    (k : ℕ) : (α ^ k) v = (α v * v⁻¹) ^ k * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, pow_succ, mul_assoc,
      inv_mul_cancel_right]

theorem tr3_fixed_of_disp {p : ℕ} (hp : Odd p) (α : MulAut V) (hα : α ^ p = 1) (v : V)
    (hfix : α (α v * v⁻¹) = α v * v⁻¹) (h2 : (α v * v⁻¹) ^ 2 = 1) : α v = v := by
  have h := tr3_pow_apply_of_fixed α v hfix p
  rw [hα, MulAut.one_apply] at h
  have hw : (α v * v⁻¹) ^ p = 1 := right_eq_mul.mp h
  obtain ⟨m, rfl⟩ := hp
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hw
  exact mul_inv_eq_one.1 hw

theorem tr3_card_sup_of_inf_eq_bot {H K : Subgroup V} (h : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup V) = Nat.card H * Nat.card K := by
  let f : H × K →* V :=
    H.subtype.comp (MonoidHom.fst H K) * K.subtype.comp (MonoidHom.snd H K)
  have hf : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ he
    have he' : (h₁ : V) * k₁ = h₂ * k₂ := he
    have hx : (h₂ : V)⁻¹ * h₁ = k₂ * (k₁ : V)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he', mul_inv_cancel_right]
    have hmem : (h₂ : V)⁻¹ * h₁ ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, hx ▸ K.mul_mem k₂.2 (K.inv_mem k₁.2)⟩
    rw [h, mem_bot] at hmem
    have e1 : (h₁ : V) = h₂ := by rw [inv_mul_eq_one] at hmem; exact hmem.symm
    have e2 : (k₁ : V) = k₂ := by rw [e1] at he'; exact mul_left_cancel he'
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  have hrange : f.range = H ⊔ K := by
    ext x
    rw [MonoidHom.mem_range, mem_sup]
    constructor
    · rintro ⟨⟨y, z⟩, rfl⟩
      exact ⟨y, y.2, z, z.2, rfl⟩
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  rw [← hrange, ← Nat.card_prod]
  exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm

theorem tr3_norm_fixed (ρ : A →* MulAut V) {δ : A} {p : ℕ} (hp : 0 < p) (hδ : δ ^ p = 1)
    (u : V) :
    ρ δ (∏ k ∈ Finset.range p, ρ (δ ^ k) u) = ∏ k ∈ Finset.range p, ρ (δ ^ k) u := by
  rw [map_prod]
  have e : ∀ k, ρ δ (ρ (δ ^ k) u) = ρ (δ ^ (k + 1)) u := fun k => by
    rw [pow_succ', map_mul, MulAut.mul_apply]
  simp_rw [e]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun k => ρ (δ ^ k) u), hδ, pow_zero]

theorem tr3_norm_eq_one (ρ : A →* MulAut V) {U : Subgroup V}
    (hU : ∀ (a : A), ∀ u ∈ U, ρ a u ∈ U) {δ : A} {p : ℕ} (hp : 0 < p) (hδ : δ ^ p = 1)
    (hfree : ∀ u ∈ U, ρ δ u = u → u = 1) {u : V} (hu : u ∈ U) :
    ∏ k ∈ Finset.range p, ρ (δ ^ k) u = 1 :=
  hfree _ (Subgroup.prod_mem U fun _ _ => hU _ u hu) (tr3_norm_fixed ρ hp hδ u)

theorem tr3_double_norm (ρ : A →* MulAut V) (a c : A) (u : V) (p : ℕ) :
    ∏ j ∈ Finset.range p, ∏ k ∈ Finset.range p, ρ ((c * a ^ j) ^ k) u =
      ∏ k ∈ Finset.range p, ρ (c ^ k) (∏ j ∈ Finset.range p, ρ ((a ^ k) ^ j) u) := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j k, map_mul, MulAut.mul_apply]

section Main

theorem tr3_pow_not_mem {p : ℕ} (hp : p.Prime) {K : Subgroup A} {a : A} (ha : a ∉ K)
    (hap : a ^ p = 1) {k : ℕ} (hk1 : 0 < k) (hkp : k < p) : a ^ k ∉ K := by
  intro hk
  have hcop : Nat.Coprime k p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hk1 hkp))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  apply ha
  have e : a = (a ^ k) ^ m := by rw [← pow_mul, pow_eq_pow_mod _ hap, hm, pow_one]
  rw [e]
  exact K.pow_mem hk m

variable [Finite V] [Finite A]

omit [Finite V] in
theorem tr3_index_le_of_free {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hV : ∀ v : V, v ^ 2 = 1)
    (hA : ∀ a : A, a ^ p = 1) (ρ : A →* MulAut V) {U : Subgroup V}
    (hU : ∀ (a : A), ∀ u ∈ U, ρ a u ∈ U)
    (hB : ∀ a : A, (∀ u ∈ U, ρ a u = u) ∨ (∀ u ∈ U, ρ a u = u → u = 1)) :
    (tr3Fixer ρ U).index ≤ p := by
  by_contra hlt
  push Not at hlt
  set K := tr3Fixer ρ U with hK
  have hKtop : K ≠ ⊤ := by
    intro h
    rw [h, index_top] at hlt
    exact absurd hlt (not_lt.2 hp.one_lt.le)
  obtain ⟨a, haK⟩ : ∃ a, a ∉ K := by
    by_contra h
    push Not at h
    exact hKtop (eq_top_iff.2 fun x _ => h x)
  have hLtop : zpowers a ⊔ K ≠ ⊤ := by
    intro h
    have h1 : K.relIndex (zpowers a ⊔ K) = K.relIndex (zpowers a) := relIndex_sup_right _ _
    rw [h, relIndex_top_right] at h1
    have h2 : K.relIndex (zpowers a) ≤ p := by
      refine (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _)).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one hp.pos (hA a)
    omega
  obtain ⟨c, hcL⟩ : ∃ c, c ∉ zpowers a ⊔ K := by
    by_contra h
    push Not at h
    exact hLtop (eq_top_iff.2 fun x _ => h x)
  have hfa : ∀ k, 0 < k → k < p → ∀ u ∈ U, ρ (a ^ k) u = u → u = 1 := fun k hk1 hkp =>
    (hB (a ^ k)).resolve_left (tr3_pow_not_mem hp haK (hA a) hk1 hkp)
  have hfc : ∀ j : ℕ, ∀ u ∈ U, ρ (c * a ^ j) u = u → u = 1 := by
    intro j
    refine (hB _).resolve_left fun h => hcL ?_
    have e : c = c * a ^ j * (a ^ j)⁻¹ := by rw [mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mem_sup_right h) (inv_mem (mem_sup_left (pow_mem (mem_zpowers a) j)))
  have hUbot : ∀ u ∈ U, u = 1 := by
    intro u hu
    have h1 : ∏ j ∈ Finset.range p, ∏ k ∈ Finset.range p, ρ ((c * a ^ j) ^ k) u = 1 :=
      Finset.prod_eq_one fun j _ => tr3_norm_eq_one ρ hU hp.pos (hA _) (hfc j) hu
    rw [tr3_double_norm, Finset.prod_eq_single 0] at h1
    · simp only [pow_zero, one_pow, map_one, MulAut.one_apply, Finset.prod_const,
        Finset.card_range] at h1
      obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
      rw [hm, pow_succ, pow_mul, hV, one_pow, one_mul] at h1
      exact h1
    · intro k hk hk0
      have hδ : (a ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hA, one_pow]
      rw [tr3_norm_eq_one ρ hU hp.pos hδ
        (hfa k (Nat.pos_of_ne_zero hk0) (Finset.mem_range.1 hk)) hu, map_one]
    · intro h0
      exact absurd (Finset.mem_range.2 hp.pos) h0
  apply hKtop
  rw [eq_top_iff]
  intro x _ u hu
  rw [hUbot u hu, map_one]

theorem tr3_claim {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hV : ∀ v : V, v ^ 2 = 1)
    (hA : ∀ a : A, a ^ p = 1) (ρ : A →* MulAut V) (orth : V → V → Prop)
    (horth_symm : ∀ v w, orth v w → orth w v)
    (horth_mul : ∀ v w₁ w₂, orth v w₁ → orth v w₂ → orth v (w₁ * w₂))
    (horth_self : ∀ v, orth v v)
    (horth_fix : ∀ (a : A) (v u : V), ρ a v = v → orth v (ρ a u * u⁻¹)) :
    ∀ U : Subgroup V, (∀ (a : A), ∀ u ∈ U, ρ a u ∈ U) →
      ∃ W : Subgroup V, W ≤ U ∧ (∀ v ∈ W, ∀ w ∈ W, orth v w) ∧
        ∀ k : ℕ, p ^ k ≤ (tr3Fixer ρ U).index → 2 ^ k ≤ Nat.card W := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hApg : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  have : Fact p.Prime := ⟨hp⟩
  have horth_one : ∀ v, orth v 1 := fun v => by
    simpa using horth_fix 1 v v (by rw [map_one, MulAut.one_apply])
  intro U
  induction hn : Nat.card U using Nat.strong_induction_on generalizing U with
  | _ n ih =>
  intro hU
  by_cases hcase : ∃ a : A, (∃ u ∈ U, ρ a u ≠ u) ∧ (∃ u ∈ U, u ≠ 1 ∧ ρ a u = u)
  · obtain ⟨a, ⟨u₀, hu₀U, hu₀⟩, ⟨u₁, hu₁U, hu₁1, hu₁⟩⟩ := hcase
    set U₁ := U ⊓ (tr3Disp ρ a).ker with hU₁
    set U₂ := U.map (tr3Disp ρ a) with hU₂
    have hU₁inv : ∀ (b : A), ∀ v ∈ U₁, ρ b v ∈ U₁ := by
      intro b v hv
      rw [mem_inf, tr3_mem_ker_disp] at hv ⊢
      exact ⟨hU b v hv.1, by rw [tr3_comm_apply, hv.2]⟩
    have hU₂inv : ∀ (b : A), ∀ w ∈ U₂, ρ b w ∈ U₂ := by
      rintro b _ ⟨v, hv, rfl⟩
      refine ⟨ρ b v, hU b v hv, ?_⟩
      simp only [tr3_disp_apply, map_mul, map_inv, tr3_comm_apply ρ a b]
    have hdisj : U₁ ⊓ U₂ = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [mem_inf] at hw
      obtain ⟨hw, v, -, rfl⟩ := hw
      rw [mem_bot]
      rw [hU₁, mem_inf, tr3_mem_ker_disp] at hw
      replace hw := hw.2
      have hv := tr3_fixed_of_disp hodd (ρ a) (by rw [← map_pow, hA, map_one]) v hw (hV _)
      rw [tr3_disp_apply, hv, mul_inv_cancel]
    have hU₁le : U₁ ≤ U := inf_le_left
    have hU₂le : U₂ ≤ U := by
      rintro _ ⟨v, hv, rfl⟩
      exact U.mul_mem (hU a v hv) (U.inv_mem hv)
    have hu₁mem : u₁ ∈ U₁ := mem_inf.2 ⟨hu₁U, tr3_mem_ker_disp.2 hu₁⟩
    have hlt₁ : Nat.card U₁ < n := by
      rw [← hn]
      refine card_lt_of_lt (lt_of_le_of_ne hU₁le fun h => hu₀ ?_)
      have : u₀ ∈ U₁ := h ▸ hu₀U
      exact tr3_mem_ker_disp.1 (mem_inf.1 this).2
    have hlt₂ : Nat.card U₂ < n := by
      rw [← hn]
      refine card_lt_of_lt (lt_of_le_of_ne hU₂le fun h => hu₁1 ?_)
      have : u₁ ∈ U₁ ⊓ U₂ := ⟨hu₁mem, h ▸ hu₁U⟩
      rw [hdisj] at this
      exact this
    obtain ⟨W₁, hW₁U, hW₁o, hW₁k⟩ := ih _ hlt₁ U₁ rfl hU₁inv
    obtain ⟨W₂, hW₂U, hW₂o, hW₂k⟩ := ih _ hlt₂ U₂ rfl hU₂inv
    refine ⟨W₁ ⊔ W₂, sup_le (hW₁U.trans hU₁le) (hW₂U.trans hU₂le), ?_, ?_⟩
    · have cross : ∀ x ∈ U₁, ∀ y ∈ U₂, orth x y := by
        rintro x hx _ ⟨v, -, rfl⟩
        exact horth_fix a x v (tr3_mem_ker_disp.1 (mem_inf.1 hx).2)
      have hmul_left : ∀ x₁ x₂ y, orth x₁ y → orth x₂ y → orth (x₁ * x₂) y :=
        fun x₁ x₂ y h₁ h₂ =>
          horth_symm _ _ (horth_mul _ _ _ (horth_symm _ _ h₁) (horth_symm _ _ h₂))
      intro x hx y hy
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup.1 hx
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup.1 hy
      exact hmul_left _ _ _
        (horth_mul _ _ _ (hW₁o _ hx₁ _ hy₁) (cross _ (hW₁U hx₁) _ (hW₂U hy₂)))
        (horth_mul _ _ _ (horth_symm _ _ (cross _ (hW₁U hy₁) _ (hW₂U hx₂))) (hW₂o _ hx₂ _ hy₂))
    · intro k hk
      have hfix : tr3Fixer ρ U₁ ⊓ tr3Fixer ρ U₂ ≤ tr3Fixer ρ U := by
        rintro b ⟨hb₁, hb₂⟩ v hv
        have hy : tr3Disp ρ b v ∈ U₁ := by
          refine mem_inf.2 ⟨U.mul_mem (hU b v hv) (U.inv_mem hv), ?_⟩
          rw [MonoidHom.mem_ker, tr3_disp_comm]
          have h1 : ρ b (tr3Disp ρ a v) = tr3Disp ρ a v := hb₂ _ ⟨v, hv, rfl⟩
          rw [tr3_disp_apply, h1, mul_inv_cancel]
        exact tr3_fixed_of_disp hodd (ρ b) (by rw [← map_pow, hA, map_one]) v (hb₁ _ hy) (hV _)
      obtain ⟨k₁, hk₁⟩ := hApg.index (tr3Fixer ρ U₁)
      obtain ⟨k₂, hk₂⟩ := hApg.index (tr3Fixer ρ U₂)
      have hle : p ^ k ≤ p ^ (k₁ + k₂) := by
        calc p ^ k ≤ (tr3Fixer ρ U).index := hk
          _ ≤ (tr3Fixer ρ U₁ ⊓ tr3Fixer ρ U₂).index := index_antitone hfix
          _ ≤ (tr3Fixer ρ U₁).index * (tr3Fixer ρ U₂).index := index_inf_le
          _ = p ^ (k₁ + k₂) := by rw [hk₁, hk₂, pow_add]
      have hkk : k ≤ k₁ + k₂ := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
      have hdisjW : W₁ ⊓ W₂ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : x ∈ U₁ ⊓ U₂ := ⟨hW₁U hx.1, hW₂U hx.2⟩
        rwa [hdisj] at this
      rw [tr3_card_sup_of_inf_eq_bot hdisjW]
      calc 2 ^ k ≤ 2 ^ (k₁ + k₂) := Nat.pow_le_pow_right (by norm_num) hkk
        _ = 2 ^ k₁ * 2 ^ k₂ := pow_add _ _ _
        _ ≤ Nat.card W₁ * Nat.card W₂ := Nat.mul_le_mul (hW₁k k₁ hk₁.ge) (hW₂k k₂ hk₂.ge)
  · push Not at hcase
    have hB : ∀ a : A, (∀ u ∈ U, ρ a u = u) ∨ (∀ u ∈ U, ρ a u = u → u = 1) := by
      intro a
      by_cases h : ∀ u ∈ U, ρ a u = u
      · exact Or.inl h
      · push Not at h
        refine Or.inr fun u hu hfix => ?_
        by_contra hu1
        exact hcase a h u hu hu1 hfix
    have hidx := tr3_index_le_of_free hp hp2 hV hA ρ hU hB
    rcases Subgroup.bot_or_exists_ne_one U with hUbot | ⟨u, hu, hu1⟩
    · refine ⟨⊥, bot_le, ?_, ?_⟩
      · intro v hv w hw
        rw [mem_bot] at hv hw
        rw [hv, hw]
        exact horth_self 1
      · intro k hk
        have htop : tr3Fixer ρ U = ⊤ := by
          rw [eq_top_iff]
          intro a _ u hu
          rw [hUbot, mem_bot] at hu
          rw [hu, map_one]
        rw [htop, index_top] at hk
        have hk0 : k = 0 := by
          by_contra h
          have := Nat.one_lt_pow h hp.one_lt
          omega
        rw [hk0, pow_zero, card_bot]
    · let O : V → Subgroup V := fun v =>
        { carrier := {x | orth v x}
          mul_mem' := fun {x y} hx hy => horth_mul v x y hx hy
          one_mem' := horth_one v
          inv_mem' := fun {x} hx => by
            have : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by rw [← sq, hV])
            change orth v x⁻¹
            rw [this]
            exact hx }
      have hO : ∀ v x, x ∈ O v ↔ orth v x := fun _ _ => Iff.rfl
      refine ⟨zpowers (u : V), (zpowers_le).2 hu, ?_, ?_⟩
      · have h1 : zpowers (u : V) ≤ O u := (zpowers_le).2 ((hO _ _).2 (horth_self _))
        intro x hx y hy
        have h2 : zpowers (u : V) ≤ O x :=
          (zpowers_le).2 ((hO _ _).2 (horth_symm _ _ ((hO _ _).1 (h1 hx))))
        exact (hO _ _).1 (h2 hy)
      · intro k hk
        have hk1 : k ≤ 1 := by
          have : p ^ k ≤ p ^ 1 := by rw [pow_one]; exact hk.trans hidx
          exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [Nat.card_zpowers, orderOf_eq_prime (hV u) hu1]
        calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
          _ = 2 := pow_one 2

theorem tr3_exists_isotropic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hV : ∀ v : V, v ^ 2 = 1)
    (hA : ∀ a : A, a ^ p = 1) (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (orth : V → V → Prop) (horth_symm : ∀ v w, orth v w → orth w v)
    (horth_mul : ∀ v w₁ w₂, orth v w₁ → orth v w₂ → orth v (w₁ * w₂))
    (horth_self : ∀ v, orth v v)
    (horth_fix : ∀ (a : A) (v u : V), ρ a v = v → orth v (ρ a u * u⁻¹))
    {k : ℕ} (hk : p ^ k ≤ Nat.card A) :
    ∃ W : Subgroup V, (∀ v ∈ W, ∀ w ∈ W, orth v w) ∧ 2 ^ k ≤ Nat.card W := by
  obtain ⟨W, -, hWo, hWk⟩ := tr3_claim hp hp2 hV hA ρ orth horth_symm horth_mul horth_self
    horth_fix ⊤ fun _ _ _ => mem_top _
  refine ⟨W, hWo, hWk k ?_⟩
  have hbot : tr3Fixer ρ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [mem_bot]
    apply hρ
    ext v
    rw [map_one, MulAut.one_apply]
    exact ha v (mem_top v)
  rw [hbot, index_bot]
  exact hk

end Main

end Count

end CFSG.HardMathSupport.Solomon.Coordinator

end
