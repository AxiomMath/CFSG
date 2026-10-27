module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49D

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup
open scoped Pointwise commutatorElement

section Mv

abbrev mv (A : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v

theorem mv_mul (A B : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    mv (A * B) v = mv A (mv B v) := by
  rw [mv, mv, mv, Units.val_mul, Matrix.mulVec_mulVec]

theorem mv_one (v : Fin 3 → ZMod 2) : mv 1 v = v := by
  rw [mv, Units.val_one, Matrix.one_mulVec]

theorem mv_zero (A : GL (Fin 3) (ZMod 2)) : mv A 0 = 0 := Matrix.mulVec_zero _

theorem mv_inv_mv (A : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) : mv A⁻¹ (mv A v) = v := by
  rw [← mv_mul, inv_mul_cancel, mv_one]

theorem mv_mv_inv (A : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) : mv A (mv A⁻¹ v) = v := by
  rw [← mv_mul, mul_inv_cancel, mv_one]

theorem mv_injective (A : GL (Fin 3) (ZMod 2)) : Function.Injective (mv A) := fun v w h => by
  rw [← mv_inv_mv A v, h, mv_inv_mv]

theorem eq_zero_of_mv_eq_zero {A : GL (Fin 3) (ZMod 2)} {v : Fin 3 → ZMod 2} (h : mv A v = 0) :
    v = 0 := mv_injective A (h.trans (mv_zero A).symm)

theorem eq_of_mv_eq {A B : GL (Fin 3) (ZMod 2)} (h : ∀ v, mv A v = mv B v) : A = B := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h v

theorem add_self_v (v : Fin 3 → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

abbrev ev0 : Fin 3 → ZMod 2 := ![1, 0, 0]
abbrev ev1 : Fin 3 → ZMod 2 := ![0, 1, 0]
abbrev ev2 : Fin 3 → ZMod 2 := ![0, 0, 1]

theorem mv_t01_ev1 : mv t01 ev1 + ev1 = ev0 := by decide
theorem mv_t12_ev2 : mv t12 ev2 + ev2 = ev1 := by decide
theorem mv_t21_ev1 : mv t21 ev1 + ev1 = ev2 := by decide

theorem v3_cases : ∀ v : Fin 3 → ZMod 2, v = 0 ∨ v = ev0 ∨ v = ev1 ∨ v = ev0 + ev1 ∨ v = ev2 ∨
    v = ev0 + ev2 ∨ v = ev1 + ev2 ∨ v = ev0 + ev1 + ev2 := by
  decide

theorem eq_zero_of_mv_fix : ∀ v : Fin 3 → ZMod 2, mv t01 v = v → mv t12 v = v → mv t10 v = v →
    v = 0 := by
  decide

theorem eq_one_of_mv_fix {A : GL (Fin 3) (ZMod 2)} (h : ∀ v, mv A v = v) : A = 1 :=
  eq_of_mv_eq fun v => by rw [h, mv_one]

end Mv

section Data

variable {X : Type} [Group X]

structure HatData (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) (zh : X) : Prop where
  add : ∀ a b a' b', ι (a + a') (b + b') = ι a b * ι a' b'
  inj : ∀ a b, ι a b = 1 → a = 0 ∧ b = 0
  swap : ∀ a b, zh * ι a b * zh⁻¹ = ι b a
  zh_sq : zh * zh = 1
  shape : ∀ x : X, ∃ A B : GL (Fin 3) (ZMod 2),
    (∀ a b, x * ι a b * x⁻¹ = ι (mv A a) (mv B b)) ∨
      (∀ a b, x * ι a b * x⁻¹ = ι (mv B b) (mv A a))
  ker : ∀ x : X, (∀ a b, x * ι a b * x⁻¹ = ι a b) → ∃ a b, x = ι a b
  card : Nat.card X = 64 * 56448

variable {ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X} {zh : X}

@[expose] def swapι (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) :
    (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X := fun a b => ι b a

theorem HatData.swapped (h : HatData ι zh) : HatData (swapι ι) zh where
  add a b a' b' := h.add b a b' a'
  inj a b hab := (h.inj b a hab).symm
  swap a b := h.swap b a
  zh_sq := h.zh_sq
  shape x := by
    obtain ⟨A, B, hx | hx⟩ := h.shape x
    · exact ⟨B, A, Or.inl fun a b => hx b a⟩
    · exact ⟨B, A, Or.inr fun a b => hx b a⟩
  ker x hx := by
    obtain ⟨a, b, rfl⟩ := h.ker x fun a b => hx b a
    exact ⟨b, a, rfl⟩
  card := h.card

section Basic

variable (h : HatData ι zh)
include h

theorem HatData.zero : ι 0 0 = 1 := by
  have h1 := h.add 0 0 0 0
  simp only [add_zero] at h1
  exact (mul_eq_left.1 h1.symm)

theorem HatData.sq (a b : Fin 3 → ZMod 2) : ι a b * ι a b = 1 := by
  rw [← h.add, add_self_v, add_self_v, h.zero]

theorem HatData.inv (a b : Fin 3 → ZMod 2) : (ι a b)⁻¹ = ι a b :=
  inv_eq_of_mul_eq_one_right (h.sq a b)

theorem HatData.comm (a b a' b' : Fin 3 → ZMod 2) : ι a b * ι a' b' = ι a' b' * ι a b := by
  rw [← h.add, ← h.add, add_comm a, add_comm b]

theorem HatData.eq_iff {a b a' b' : Fin 3 → ZMod 2} : ι a b = ι a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro hab
    have h1 : ι (a + a') (b + b') = 1 := by rw [h.add, hab, h.sq]
    obtain ⟨h2, h3⟩ := h.inj _ _ h1
    refine ⟨?_, ?_⟩
    · have := congrArg (· + a') h2
      simpa [add_assoc, add_self_v] using this
    · have := congrArg (· + b') h3
      simpa [add_assoc, add_self_v] using this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem HatData.zh_inv : zh⁻¹ = zh := inv_eq_of_mul_eq_one_right h.zh_sq

theorem HatData.swap' (a b : Fin 3 → ZMod 2) : zh⁻¹ * ι a b * zh = ι b a := by
  have := h.swap a b
  rw [h.zh_inv] at this ⊢
  exact this

end Basic

@[expose] def Tc (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X :=
  closure {x | ∃ a b, x = ι a b}

@[expose] def T1 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X :=
  closure {x | ∃ a, x = ι a 0}

@[expose] def T2 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X :=
  closure {x | ∃ b, x = ι 0 b}

section TSub

variable (h : HatData ι zh)
include h

theorem HatData.mem_Tc {x : X} : x ∈ Tc ι ↔ ∃ a b, x = ι a b := by
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, 0, h.zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨a + a', b + b', (h.add a b a' b').symm⟩
    | inv x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨a, b, h.inv a b⟩
  · intro hx
    exact subset_closure hx

theorem HatData.mem_T1 {x : X} : x ∈ T1 ι ↔ ∃ a, x = ι a 0 := by
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, h.zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hy
      exact ⟨a + a', by rw [← h.add, add_zero]⟩
    | inv x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, h.inv a 0⟩
  · intro hx
    exact subset_closure hx

theorem HatData.mem_T2 {x : X} : x ∈ T2 ι ↔ ∃ b, x = ι 0 b := by
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, h.zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨b, rfl⟩ := hx
      obtain ⟨b', rfl⟩ := hy
      exact ⟨b + b', by rw [← h.add, add_zero]⟩
    | inv x _ hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨b, h.inv 0 b⟩
  · intro hx
    exact subset_closure hx

theorem HatData.iota_mem_Tc (a b : Fin 3 → ZMod 2) : ι a b ∈ Tc ι :=
  subset_closure ⟨a, b, rfl⟩

theorem HatData.iota_mem_T1 (a : Fin 3 → ZMod 2) : ι a 0 ∈ T1 ι := subset_closure ⟨a, rfl⟩

theorem HatData.T1_le_Tc : T1 ι ≤ Tc ι :=
  closure_le _ |>.2 fun _ ⟨a, ha⟩ => ha ▸ h.iota_mem_Tc a 0

theorem HatData.T1_inf_T2 : T1 ι ⊓ T2 ι = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := (h.mem_T1).1 (mem_inf.1 hx).1
  obtain ⟨b, hb⟩ := (h.mem_T2).1 (mem_inf.1 hx).2
  obtain ⟨rfl, -⟩ := (h.eq_iff).1 hb
  rw [mem_bot, h.zero]

theorem HatData.card_Tc : Nat.card (Tc ι) = 64 := by
  let f : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) → Tc ι := fun p => ⟨ι p.1 p.2, h.iota_mem_Tc _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      obtain ⟨h1, h2⟩ := (h.eq_iff).1 (congrArg Subtype.val hab)
      exact Prod.ext h1 h2
    · rintro ⟨x, hx⟩
      obtain ⟨a, b, rfl⟩ := (h.mem_Tc).1 hx
      exact ⟨(a, b), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp

theorem HatData.card_T1 : Nat.card (T1 ι) = 8 := by
  let f : (Fin 3 → ZMod 2) → T1 ι := fun a => ⟨ι a 0, h.iota_mem_T1 a⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' hab
      exact ((h.eq_iff).1 (congrArg Subtype.val hab)).1
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (h.mem_T1).1 hx
      exact ⟨a, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp

theorem HatData.T1_le_of_basis {Y : Subgroup X} (h0 : ι ev0 0 ∈ Y) (h1 : ι ev1 0 ∈ Y)
    (h2 : ι ev2 0 ∈ Y) : T1 ι ≤ Y := by
  refine closure_le _ |>.2 ?_
  rintro _ ⟨a, rfl⟩
  have hm : ∀ u v : Fin 3 → ZMod 2, ι u 0 ∈ Y → ι v 0 ∈ Y → ι (u + v) 0 ∈ Y := fun u v hu hv => by
    rw [show (0 : Fin 3 → ZMod 2) = 0 + 0 from (add_zero 0).symm, h.add]
    exact mul_mem hu hv
  rcases v3_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.zero]; exact one_mem Y
  · exact h0
  · exact h1
  · exact hm _ _ h0 h1
  · exact h2
  · exact hm _ _ h0 h2
  · exact hm _ _ h1 h2
  · exact hm _ _ (hm _ _ h0 h1) h2

end TSub

@[expose] def P1 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X where
  carrier := {x | ∃ A : GL (Fin 3) (ZMod 2), ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) b}
  one_mem' := ⟨1, fun a b => by rw [one_mul, inv_one, mul_one, mv_one]⟩
  mul_mem' := by
    rintro x y ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, fun a b => ?_⟩
    rw [show x * y * ι a b * (x * y)⁻¹ = x * (y * ι a b * y⁻¹) * x⁻¹ by group, hB, hA, mv_mul]
  inv_mem' := by
    rintro x ⟨A, hA⟩
    refine ⟨A⁻¹, fun a b => ?_⟩
    have h1 := hA (mv A⁻¹ a) b
    rw [mv_mv_inv] at h1
    rw [← h1]
    group

@[expose] def P2 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X := P1 (swapι ι)

@[expose] def X0 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X where
  carrier := {x | ∃ A B : GL (Fin 3) (ZMod 2), ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) (mv B b)}
  one_mem' := ⟨1, 1, fun a b => by rw [one_mul, inv_one, mul_one, mv_one, mv_one]⟩
  mul_mem' := by
    rintro x y ⟨A, B, hA⟩ ⟨A', B', hB⟩
    refine ⟨A * A', B * B', fun a b => ?_⟩
    rw [show x * y * ι a b * (x * y)⁻¹ = x * (y * ι a b * y⁻¹) * x⁻¹ by group, hB, hA, mv_mul,
      mv_mul]
  inv_mem' := by
    rintro x ⟨A, B, hA⟩
    refine ⟨A⁻¹, B⁻¹, fun a b => ?_⟩
    have h1 := hA (mv A⁻¹ a) (mv B⁻¹ b)
    rw [mv_mv_inv, mv_mv_inv] at h1
    rw [← h1]
    group

theorem X0_swap : X0 (swapι ι) = X0 ι := by
  ext x
  constructor
  · rintro ⟨A, B, hx⟩
    exact ⟨B, A, fun a b => hx b a⟩
  · rintro ⟨A, B, hx⟩
    exact ⟨B, A, fun a b => hx b a⟩

theorem P1_le_X0 : P1 ι ≤ X0 ι := by
  rintro x ⟨A, hA⟩
  exact ⟨A, 1, fun a b => by rw [hA, mv_one]⟩

theorem P2_le_X0 : P2 ι ≤ X0 ι := by
  rw [← X0_swap]
  exact P1_le_X0

@[expose] def K1 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X := ⁅P1 ι, P1 ι⁆

@[expose] def K2 (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) : Subgroup X := ⁅P2 ι, P2 ι⁆

theorem K1_le_P1 : K1 ι ≤ P1 ι := commutator_le_self _

theorem K2_le_P2 : K2 ι ≤ P2 ι := commutator_le_self _

section P

variable (h : HatData ι zh)
include h

theorem HatData.Tc_le_P1 : Tc ι ≤ P1 ι := by
  intro x hx
  obtain ⟨a', b', rfl⟩ := (h.mem_Tc).1 hx
  refine ⟨1, fun a b => ?_⟩
  rw [mv_one, h.comm a' b' a b, mul_inv_cancel_right]

theorem HatData.T1_le_P1 : T1 ι ≤ P1 ι := (h.T1_le_Tc).trans h.Tc_le_P1

theorem HatData.P1_unique {x : X} {A A' : GL (Fin 3) (ZMod 2)}
    (hA : ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) b) (hA' : ∀ a b, x * ι a b * x⁻¹ = ι (mv A' a) b) :
    A = A' :=
  eq_of_mv_eq fun a => ((h.eq_iff).1 ((hA a 0).symm.trans (hA' a 0))).1

theorem HatData.X0_unique {x : X} {A B A' B' : GL (Fin 3) (ZMod 2)}
    (hA : ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) (mv B b))
    (hA' : ∀ a b, x * ι a b * x⁻¹ = ι (mv A' a) (mv B' b)) : A = A' ∧ B = B' :=
  ⟨eq_of_mv_eq fun a => by
      have := ((h.eq_iff).1 ((hA a 0).symm.trans (hA' a 0))).1
      exact this,
    eq_of_mv_eq fun b => ((h.eq_iff).1 ((hA 0 b).symm.trans (hA' 0 b))).2⟩

theorem HatData.not_swap_of_mem_X0 {x : X} (hx : x ∈ X0 ι) {A B : GL (Fin 3) (ZMod 2)}
    (hs : ∀ a b, x * ι a b * x⁻¹ = ι (mv B b) (mv A a)) : False := by
  obtain ⟨A', B', hx⟩ := hx
  have h1 := (hx ev0 0).symm.trans (hs ev0 0)
  rw [mv_zero, mv_zero] at h1
  have h2 := ((h.eq_iff).1 h1).1
  exact absurd (eq_zero_of_mv_eq_zero h2) (by decide)

theorem HatData.mul_zh_mem_X0 {x : X} (hx : x ∉ X0 ι) : x * zh ∈ X0 ι := by
  obtain ⟨A, B, hA | hA⟩ := h.shape x
  · exact absurd ⟨A, B, hA⟩ hx
  · refine ⟨B, A, fun a b => ?_⟩
    rw [show x * zh * ι a b * (x * zh)⁻¹ = x * (zh * ι a b * zh⁻¹) * x⁻¹ by group, h.swap, hA]

theorem HatData.zh_not_mem_X0 : zh ∉ X0 ι := fun hz =>
  h.not_swap_of_mem_X0 hz (A := 1) (B := 1) fun a b => by rw [h.swap, mv_one, mv_one]

theorem HatData.index_X0 : (X0 ι).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨zh, fun b => ?_⟩
  by_cases hb : b ∈ X0 ι
  · refine Or.inr ⟨hb, fun hbz => h.zh_not_mem_X0 ?_⟩
    have := mul_mem (inv_mem hb) hbz
    rwa [inv_mul_cancel_left] at this
  · exact Or.inl ⟨h.mul_zh_mem_X0 hb, hb⟩

theorem HatData.mem_X0_or (x : X) : x ∈ X0 ι ∨ zh * x ∈ X0 ι := by
  by_cases hx : x ∈ X0 ι
  · exact Or.inl hx
  · refine Or.inr ?_
    have h1 := h.mul_zh_mem_X0 (x := x⁻¹) (fun h' => hx (by simpa using inv_mem h'))
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv, h.zh_inv] at h2

theorem HatData.card_X0 [Finite X] : Nat.card (X0 ι) = 64 * 28224 := by
  have h1 := Subgroup.card_mul_index (X0 ι)
  rw [h.index_X0, h.card] at h1
  omega

end P

section Act

variable (ι)

@[expose] def Acts1 (x : X) (A : GL (Fin 3) (ZMod 2)) : Prop :=
  ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) b

variable {ι}

theorem mem_P1_iff {x : X} : x ∈ P1 ι ↔ ∃ A, Acts1 ι x A := Iff.rfl

theorem mem_X0_iff {x : X} :
    x ∈ X0 ι ↔ ∃ A B : GL (Fin 3) (ZMod 2), ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) (mv B b) :=
  Iff.rfl

theorem Acts1.mul {x y : X} {A B : GL (Fin 3) (ZMod 2)} (hx : Acts1 ι x A) (hy : Acts1 ι y B) :
    Acts1 ι (x * y) (A * B) := fun a b => by
  rw [show x * y * ι a b * (x * y)⁻¹ = x * (y * ι a b * y⁻¹) * x⁻¹ by group, hy, hx, mv_mul]

theorem Acts1.inv {x : X} {A : GL (Fin 3) (ZMod 2)} (hx : Acts1 ι x A) : Acts1 ι x⁻¹ A⁻¹ :=
  fun a b => by
    have h1 := hx (mv A⁻¹ a) b
    rw [mv_mv_inv] at h1
    rw [← h1]
    group

theorem Acts1.one : Acts1 ι 1 1 := fun a b => by rw [one_mul, inv_one, mul_one, mv_one]

theorem Acts1.commutator {x y : X} {A B : GL (Fin 3) (ZMod 2)} (hx : Acts1 ι x A)
    (hy : Acts1 ι y B) : Acts1 ι ⁅x, y⁆ ⁅A, B⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact ((hx.mul hy).mul hx.inv).mul hy.inv

end Act

section Rho

variable (h : HatData ι zh)
include h

theorem HatData.Acts1_unique {x : X} {A A' : GL (Fin 3) (ZMod 2)} (hA : Acts1 ι x A)
    (hA' : Acts1 ι x A') : A = A' := h.P1_unique hA hA'

noncomputable def HatData.rho0 : X0 ι →* GL (Fin 3) (ZMod 2) × GL (Fin 3) (ZMod 2) where
  toFun x := ((mem_X0_iff.1 x.2).choose, (mem_X0_iff.1 x.2).choose_spec.choose)
  map_one' := by
    have hs := (mem_X0_iff.1 (1 : X0 ι).2).choose_spec.choose_spec
    obtain ⟨h1, h2⟩ := h.X0_unique hs (A' := 1) (B' := 1) fun a b => by
      rw [OneMemClass.coe_one, one_mul, inv_one, mul_one, mv_one, mv_one]
    exact Prod.ext h1 h2
  map_mul' x y := by
    have hx := (mem_X0_iff.1 x.2).choose_spec.choose_spec
    have hy := (mem_X0_iff.1 y.2).choose_spec.choose_spec
    have hxy := (mem_X0_iff.1 (x * y).2).choose_spec.choose_spec
    obtain ⟨h1, h2⟩ := h.X0_unique hxy
      (A' := (mem_X0_iff.1 x.2).choose * (mem_X0_iff.1 y.2).choose)
      (B' := (mem_X0_iff.1 x.2).choose_spec.choose * (mem_X0_iff.1 y.2).choose_spec.choose)
      fun a b => by
        rw [Subgroup.coe_mul, show (x : X) * y * ι a b * ((x : X) * y)⁻¹ =
          x * (y * ι a b * (y : X)⁻¹) * (x : X)⁻¹ by group, hy, hx, mv_mul, mv_mul]
    exact Prod.ext h1 h2

theorem HatData.rho0_spec (x : X0 ι) (a b : Fin 3 → ZMod 2) :
    (x : X) * ι a b * (x : X)⁻¹ = ι (mv (h.rho0 x).1 a) (mv (h.rho0 x).2 b) :=
  (mem_X0_iff.1 x.2).choose_spec.choose_spec a b

theorem HatData.exists_act [Finite X] (A B : GL (Fin 3) (ZMod 2)) :
    ∃ x : X, ∀ a b, x * ι a b * x⁻¹ = ι (mv A a) (mv B b) := by
  have hker : Nat.card h.rho0.ker ≤ 64 := by
    let f : h.rho0.ker → Tc ι := fun k => ⟨((k : X0 ι) : X), by
      obtain ⟨a, b, hab⟩ := h.ker _ fun a b => by
        rw [h.rho0_spec, MonoidHom.mem_ker.1 k.2, Prod.fst_one, Prod.snd_one, mv_one, mv_one]
      exact hab ▸ h.iota_mem_Tc a b⟩
    have hf : Function.Injective f := fun k k' hkk => by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hkk
      exact this
    rw [← h.card_Tc]
    exact Nat.card_le_card_of_injective f hf
  have hmul := Subgroup.card_ker_mul_card_range h.rho0
  rw [h.card_X0] at hmul
  have hrange : 28224 ≤ Nat.card h.rho0.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card h.rho0.ker * Nat.card h.rho0.range < 64 * 28224 :=
      calc Nat.card h.rho0.ker * Nat.card h.rho0.range ≤ 64 * Nat.card h.rho0.range :=
            Nat.mul_le_mul_right _ hker
        _ < 64 * 28224 := by omega
    omega
  have htop : h.rho0.range = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_prod, CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3]
    exact hrange
  obtain ⟨x, hx⟩ : (A, B) ∈ h.rho0.range := htop ▸ mem_top _
  refine ⟨x, fun a b => ?_⟩
  rw [h.rho0_spec, hx]

theorem HatData.exists_P1 [Finite X] (A : GL (Fin 3) (ZMod 2)) :
    ∃ x ∈ P1 ι, Acts1 ι x A := by
  obtain ⟨x, hx⟩ := h.exists_act A 1
  exact ⟨x, ⟨A, fun a b => by rw [hx, mv_one]⟩, fun a b => by rw [hx, mv_one]⟩

theorem HatData.exists_P2 [Finite X] (B : GL (Fin 3) (ZMod 2)) :
    ∃ x ∈ P2 ι, ∀ a b, x * ι a b * x⁻¹ = ι a (mv B b) := by
  obtain ⟨x, hx⟩ := h.exists_act 1 B
  have hx2 : x ∈ P2 ι := mem_P1_iff.2 ⟨B, fun a b => by
    show x * ι b a * x⁻¹ = ι b (mv B a)
    rw [hx, mv_one]⟩
  exact ⟨x, hx2, fun a b => by rw [hx, mv_one]⟩

theorem HatData.exists_comm_of_realize {Y : Subgroup X}
    (hY : ∀ A : GL (Fin 3) (ZMod 2), ∃ y ∈ Y, Acts1 ι y A) (A : GL (Fin 3) (ZMod 2)) :
    ∃ k ∈ ⁅Y, Y⁆, Acts1 ι k A := by
  let S : Subgroup (GL (Fin 3) (ZMod 2)) :=
    { carrier := {A | ∃ k ∈ ⁅Y, Y⁆, Acts1 ι k A}
      one_mem' := ⟨1, one_mem _, Acts1.one⟩
      mul_mem' := by
        rintro A B ⟨k, hk, hkA⟩ ⟨l, hl, hlB⟩
        exact ⟨k * l, mul_mem hk hl, hkA.mul hlB⟩
      inv_mem' := by
        rintro A ⟨k, hk, hkA⟩
        exact ⟨k⁻¹, inv_mem hk, hkA.inv⟩ }
  have hS : ⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro A _ B _
    obtain ⟨x, hx, hxA⟩ := hY A
    obtain ⟨y, hy, hyB⟩ := hY B
    exact ⟨⁅x, y⁆, commutator_mem_commutator hx hy, hxA.commutator hyB⟩
  rw [commutator_GL3] at hS
  exact hS (mem_top A)

theorem HatData.T1_le_comm_of_realize {Y : Subgroup X} (hT : T1 ι ≤ Y)
    (hY : ∀ A : GL (Fin 3) (ZMod 2), ∃ y ∈ Y, Acts1 ι y A) : T1 ι ≤ ⁅Y, Y⁆ := by
  have key : ∀ (A : GL (Fin 3) (ZMod 2)) (u : Fin 3 → ZMod 2), ι (mv A u + u) 0 ∈ ⁅Y, Y⁆ := by
    intro A u
    obtain ⟨y, hy, hyA⟩ := hY A
    have h1 := commutator_mem_commutator hy (hT (h.iota_mem_T1 u))
    rw [commutatorElement_def, hyA, h.inv, ← h.add, add_zero] at h1
    exact h1
  refine h.T1_le_of_basis ?_ ?_ ?_
  · have := key t01 ev1
    rwa [mv_t01_ev1] at this
  · have := key t12 ev2
    rwa [mv_t12_ev2] at this
  · have := key t21 ev1
    rwa [mv_t21_ev1] at this

theorem HatData.exists_K1 [Finite X] (A : GL (Fin 3) (ZMod 2)) : ∃ k ∈ K1 ι, Acts1 ι k A :=
  h.exists_comm_of_realize (fun A => h.exists_P1 A) A

theorem HatData.T1_le_K1 [Finite X] : T1 ι ≤ K1 ι :=
  h.T1_le_comm_of_realize h.T1_le_P1 fun A => h.exists_P1 A

@[expose] noncomputable def sco (ι : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → X) (x : X) :
    Fin 3 → ZMod 2 :=
  open Classical in if hx : ∃ a b, x = ι a b then hx.choose_spec.choose else 0

omit h in
theorem HatData.sco_iota (h : HatData ι zh) (a b : Fin 3 → ZMod 2) : sco ι (ι a b) = b := by
  have hx : ∃ a' b', ι a b = ι a' b' := ⟨a, b, rfl⟩
  rw [sco, dif_pos hx]
  exact ((h.eq_iff).1 hx.choose_spec.choose_spec).2.symm

theorem HatData.comm_mem_Tc {c x : X} (hc : c ∈ P2 ι) (hx : x ∈ P1 ι) :
    c * x * c⁻¹ * x⁻¹ ∈ Tc ι := by
  obtain ⟨B, hB⟩ := hc
  obtain ⟨A, hA⟩ := hx
  have hB' : ∀ a b, c * ι a b * c⁻¹ = ι a (mv B b) := fun a b => hB b a
  have hBi : ∀ a b, c⁻¹ * ι a b * c = ι a (mv B⁻¹ b) := fun a b => by
    have h1 := hB' a (mv B⁻¹ b)
    rw [mv_mv_inv] at h1
    rw [← h1]
    group
  have hAi : ∀ a b, x⁻¹ * ι a b * x = ι (mv A⁻¹ a) b := fun a b => by
    have h1 := hA (mv A⁻¹ a) b
    rw [mv_mv_inv] at h1
    rw [← h1]
    group
  obtain ⟨a, b, hab⟩ := h.ker (c * x * c⁻¹ * x⁻¹) fun a b => by
    rw [show c * x * c⁻¹ * x⁻¹ * ι a b * (c * x * c⁻¹ * x⁻¹)⁻¹ =
      c * (x * (c⁻¹ * (x⁻¹ * ι a b * x) * c) * x⁻¹) * c⁻¹ by group, hAi, hBi, hA, hB',
      mv_mv_inv, mv_mv_inv]
  exact hab ▸ h.iota_mem_Tc a b

noncomputable def HatData.gco {c : X} (hc : c ∈ P2 ι) :
    P1 ι →* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (sco ι (c * x * c⁻¹ * (x : X)⁻¹))
  map_one' := by
    rw [OneMemClass.coe_one, mul_one, mul_inv_cancel, inv_one, mul_one, ← h.zero, h.sco_iota]
    rfl
  map_mul' x y := by
    obtain ⟨a₁, b₁, h1⟩ := (h.mem_Tc).1 (h.comm_mem_Tc hc x.2)
    obtain ⟨a₂, b₂, h2⟩ := (h.mem_Tc).1 (h.comm_mem_Tc hc y.2)
    obtain ⟨A, hA⟩ := x.2
    have e : c * ((x : X) * y) * c⁻¹ * ((x : X) * y)⁻¹ =
        (c * x * c⁻¹ * (x : X)⁻¹) * (x * (c * y * c⁻¹ * (y : X)⁻¹) * (x : X)⁻¹) := by group
    rw [Subgroup.coe_mul, e, h1, h2, hA, ← h.add, h.sco_iota, h.sco_iota, h.sco_iota]
    rfl

theorem HatData.comm_mem_T1 {c x : X} (hc : c ∈ P2 ι) (hx : x ∈ K1 ι) :
    c * x * c⁻¹ * x⁻¹ ∈ T1 ι := by
  have hle : K1 ι ≤ (h.gco hc).ker.map (P1 ι).subtype := by
    rw [K1, Subgroup.commutator_le]
    intro p hp q hq
    refine ⟨(⁅(⟨p, hp⟩ : P1 ι), (⟨q, hq⟩ : P1 ι)⁆ : P1 ι), ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, mul_comm]
  obtain ⟨y, hy, rfl⟩ := hle hx
  have hy' : sco ι (c * y * c⁻¹ * (y : X)⁻¹) = 0 := by
    have := MonoidHom.mem_ker.1 hy
    exact this
  obtain ⟨a, b, hab⟩ := (h.mem_Tc).1 (h.comm_mem_Tc hc y.2)
  rw [hab, h.sco_iota] at hy'
  rw [Subgroup.coe_subtype, hab, hy']
  exact h.iota_mem_T1 a

theorem HatData.comm_mem_T2 {c x : X} (hc : c ∈ P1 ι) (hx : x ∈ K2 ι) :
    c * x * c⁻¹ * x⁻¹ ∈ T2 ι :=
  h.swapped.comm_mem_T1 hc hx

theorem HatData.K1_comm_K2 {x y : X} (hx : x ∈ K1 ι) (hy : y ∈ K2 ι) : x * y = y * x := by
  have h1 := h.comm_mem_T1 (K2_le_P2 hy) hx
  have h2 := h.comm_mem_T2 (K1_le_P1 hx) hy
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ T1 ι := by
    have := inv_mem h1
    rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at this
  have h4 : x * y * x⁻¹ * y⁻¹ ∈ T1 ι ⊓ T2 ι := mem_inf.2 ⟨h3, h2⟩
  rw [h.T1_inf_T2, mem_bot] at h4
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h4, one_mul]

theorem HatData.mem_T1_of_mem_K1 [Finite X] {a b : Fin 3 → ZMod 2} (hk : ι a b ∈ K1 ι) :
    ι a b ∈ T1 ι := by
  have hfix : ∀ B : GL (Fin 3) (ZMod 2), mv B b = b := by
    intro B
    obtain ⟨c, hc, hcB⟩ := h.exists_P2 B
    have h1 := h.comm_mem_T1 hc hk
    rw [hcB, h.inv, ← h.add, add_self_v] at h1
    obtain ⟨a', ha'⟩ := (h.mem_T1).1 h1
    have h2 := ((h.eq_iff).1 ha').2
    have := congrArg (· + b) h2
    simpa [add_assoc, add_self_v] using this
  rw [eq_zero_of_mv_fix b (hfix t01) (hfix t12) (hfix t10)]
  exact h.iota_mem_T1 a

theorem HatData.K1_inf_Tc [Finite X] : K1 ι ⊓ Tc ι = T1 ι := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.T1_le_K1 h.T1_le_Tc)
  obtain ⟨a, b, rfl⟩ := (h.mem_Tc).1 (mem_inf.1 hx).2
  exact h.mem_T1_of_mem_K1 (mem_inf.1 hx).1

theorem HatData.mem_Tc_of_acts_one {x : X} (hx : Acts1 ι x 1) : x ∈ Tc ι := by
  obtain ⟨a, b, rfl⟩ := h.ker x fun a b => by rw [hx, mv_one]
  exact h.iota_mem_Tc a b

theorem HatData.K1_inf_K2 [Finite X] : K1 ι ⊓ K2 ι = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨A, hA⟩ := K1_le_P1 hx1
  obtain ⟨B, hB⟩ := K2_le_P2 hx2
  have hA1 : A = 1 := eq_of_mv_eq fun a => by
    have h1 := (hA a 0).symm.trans (show x * ι a 0 * x⁻¹ = ι a (mv B 0) from hB 0 a)
    rw [mv_one]
    exact ((h.eq_iff).1 h1).1
  subst hA1
  have hT := h.mem_Tc_of_acts_one hA
  have h1 : x ∈ T1 ι := h.K1_inf_Tc ▸ mem_inf.2 ⟨hx1, hT⟩
  have hTs : x ∈ Tc (swapι ι) := by
    obtain ⟨a, b, rfl⟩ := (h.mem_Tc).1 hT
    exact h.swapped.iota_mem_Tc b a
  have h2 : x ∈ T2 ι := by
    show x ∈ T1 (swapι ι)
    rw [← h.swapped.K1_inf_Tc]
    exact mem_inf.2 ⟨hx2, hTs⟩
  have h3 : x ∈ T1 ι ⊓ T2 ι := mem_inf.2 ⟨h1, h2⟩
  rwa [h.T1_inf_T2] at h3

noncomputable def HatData.rho1 : P1 ι →* GL (Fin 3) (ZMod 2) where
  toFun x := (mem_P1_iff.1 x.2).choose
  map_one' := h.Acts1_unique (mem_P1_iff.1 (1 : P1 ι).2).choose_spec Acts1.one
  map_mul' x y := h.Acts1_unique (mem_P1_iff.1 (x * y).2).choose_spec
    ((mem_P1_iff.1 x.2).choose_spec.mul (mem_P1_iff.1 y.2).choose_spec)

theorem HatData.rho1_spec (x : P1 ι) : Acts1 ι x (h.rho1 x) :=
  (mem_P1_iff.1 x.2).choose_spec

theorem HatData.rho1_eq {x : P1 ι} {A : GL (Fin 3) (ZMod 2)} (hA : Acts1 ι x A) :
    h.rho1 x = A := h.Acts1_unique (h.rho1_spec x) hA

theorem HatData.card_K1 [Finite X] : Nat.card (K1 ι) = 1344 := by
  let ρK : K1 ι →* GL (Fin 3) (ZMod 2) := h.rho1.comp (Subgroup.inclusion K1_le_P1)
  have hsurj : ρK.range = ⊤ := by
    rw [eq_top_iff]
    intro A _
    obtain ⟨k, hk, hkA⟩ := h.exists_K1 A
    exact ⟨⟨k, hk⟩, h.rho1_eq hkA⟩
  have hker : ρK.ker = (T1 ι).subgroupOf (K1 ι) := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hk
      have h1 : Acts1 ι (k : X) 1 := by
        have := h.rho1_spec (Subgroup.inclusion K1_le_P1 k)
        rw [show h.rho1 (Subgroup.inclusion K1_le_P1 k) = 1 from hk] at this
        exact this
      exact h.K1_inf_Tc ▸ mem_inf.2 ⟨k.2, h.mem_Tc_of_acts_one h1⟩
    · intro hk
      obtain ⟨a, ha⟩ := (h.mem_T1).1 hk
      apply h.rho1_eq
      intro a' b'
      rw [Subgroup.coe_inclusion, ha, mv_one, h.comm a 0 a' b', mul_inv_cancel_right]
  have h1 := Subgroup.card_ker_mul_card_range ρK
  rw [hker, hsurj, Subgroup.card_top,
    CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3,
    Nat.card_congr (subgroupOfEquivOfLe h.T1_le_K1).toEquiv, h.card_T1] at h1
  omega

theorem HatData.mem_T1_of_comm [Finite X] {k : X} (hk : k ∈ K1 ι)
    (hc : ∀ a, k * ι a 0 = ι a 0 * k) : k ∈ T1 ι := by
  obtain ⟨A, hA⟩ := K1_le_P1 hk
  have hA1 : A = 1 := eq_one_of_mv_fix fun a => by
    have h1 := hA a 0
    rw [hc, mul_inv_cancel_right] at h1
    exact ((h.eq_iff).1 h1).1.symm
  subst hA1
  exact h.K1_inf_Tc ▸ mem_inf.2 ⟨hk, h.mem_Tc_of_acts_one hA⟩

theorem HatData.center_K1 [Finite X] : center (K1 ι) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨x, hx⟩ hxc
  rw [mem_center_iff] at hxc
  have hc : ∀ y ∈ K1 ι, y * x = x * y := fun y hy => congrArg Subtype.val (hxc ⟨y, hy⟩)
  have hxT : x ∈ T1 ι := h.mem_T1_of_comm hx fun a => (hc _ (h.T1_le_K1 (h.iota_mem_T1 a))).symm
  obtain ⟨a₀, rfl⟩ := (h.mem_T1).1 hxT
  have hfix : ∀ B : GL (Fin 3) (ZMod 2), mv B a₀ = a₀ := by
    intro B
    obtain ⟨k, hk, hkB⟩ := h.exists_K1 B
    have h1 := hkB a₀ 0
    rw [hc k hk, mul_inv_cancel_right] at h1
    exact ((h.eq_iff).1 h1).1.symm
  rw [mem_bot]
  apply Subtype.ext
  show ι a₀ 0 = 1
  rw [eq_zero_of_mv_fix a₀ (hfix t01) (hfix t12) (hfix t10), h.zero]

theorem HatData.commutator_K1 [Finite X] : ⁅K1 ι, K1 ι⁆ = K1 ι := by
  refine le_antisymm (commutator_le_self _) (fun x hx => ?_)
  have hreal : ∀ A : GL (Fin 3) (ZMod 2), ∃ y ∈ K1 ι, Acts1 ι y A := fun A => h.exists_K1 A
  have hT : T1 ι ≤ ⁅K1 ι, K1 ι⁆ := h.T1_le_comm_of_realize h.T1_le_K1 hreal
  obtain ⟨A, hA⟩ := K1_le_P1 hx
  obtain ⟨k, hk, hkA⟩ := h.exists_comm_of_realize hreal A
  have h1 : x * k⁻¹ ∈ T1 ι := by
    refine h.K1_inf_Tc ▸ mem_inf.2 ⟨mul_mem hx (inv_mem (commutator_le_self _ hk)),
      h.mem_Tc_of_acts_one ?_⟩
    have := Acts1.mul (ι := ι) hA hkA.inv
    rwa [mul_inv_cancel] at this
  have : x = x * k⁻¹ * k := by group
  rw [this]
  exact mul_mem (hT h1) hk

theorem HatData.conj_P1 {x : X} (hx : x ∈ P1 ι) : zh * x * zh⁻¹ ∈ P2 ι := by
  obtain ⟨A, hA⟩ := hx
  refine ⟨A, fun a b => ?_⟩
  show zh * x * zh⁻¹ * ι b a * (zh * x * zh⁻¹)⁻¹ = ι b (mv A a)
  rw [show zh * x * zh⁻¹ * ι b a * (zh * x * zh⁻¹)⁻¹ = zh * (x * (zh⁻¹ * ι b a * zh) * x⁻¹) *
    zh⁻¹ by group, h.swap', hA, h.swap]

theorem HatData.conj_K1 {x : X} (hx : x ∈ K1 ι) : zh * x * zh⁻¹ ∈ K2 ι := by
  have hle : (K1 ι).map (MulAut.conj zh).toMonoidHom ≤ K2 ι := by
    rw [K1, map_commutator]
    refine commutator_mono ?_ ?_ <;>
    · rintro _ ⟨y, hy, rfl⟩
      exact h.conj_P1 hy
  exact hle ⟨x, hx, rfl⟩

theorem HatData.conj_K2 {x : X} (hx : x ∈ K2 ι) : zh * x * zh⁻¹ ∈ K1 ι :=
  h.swapped.conj_K1 hx

theorem HatData.K2_le_normalizer [Finite X] : K2 ι ≤ normalizer (K1 ι : Set X) :=
  ModIso.le_normalizer_of_conj' fun y hy x hx => by
    rw [← h.K1_comm_K2 hx hy, mul_inv_cancel_right]
    exact hx

theorem HatData.X0_eq_sup [Finite X] : X0 ι = K1 ι ⊔ K2 ι := by
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (K1_le_P1.trans P1_le_X0)
    (K2_le_P2.trans P2_le_X0)) ?_).symm
  rw [card_sup_of_inf_eq_bot h.K2_le_normalizer h.K1_inf_K2, h.card_X0, h.card_K1,
    show Nat.card (K2 ι) = 1344 from h.swapped.card_K1]

theorem HatData.exists_mul_of_mem_X0 [Finite X] {x : X} (hx : x ∈ X0 ι) :
    ∃ k₁ ∈ K1 ι, ∃ k₂ ∈ K2 ι, x = k₁ * k₂ := by
  rw [h.X0_eq_sup] at hx
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left (K1 ι) (K2 ι) h.K2_le_normalizer
  have hx' : x ∈ (K1 ι : Set X) * (K2 ι : Set X) := by
    rw [← hm]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem HatData.eq_of_mul_eq [Finite X] {a a' b b' : X} (ha : a ∈ K1 ι) (ha' : a' ∈ K1 ι)
    (hb : b ∈ K2 ι) (hb' : b' ∈ K2 ι) (h1 : a * b = a' * b') : a = a' ∧ b = b' := by
  have h2 : a'⁻¹ * a ∈ K1 ι ⊓ K2 ι := by
    refine mem_inf.2 ⟨mul_mem (inv_mem ha') ha, ?_⟩
    have : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    rw [this]
    exact mul_mem hb' (inv_mem hb)
  rw [h.K1_inf_K2, mem_bot] at h2
  have ha'' : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  subst ha''
  exact ⟨rfl, mul_left_cancel h1⟩

@[expose] noncomputable def HatData.delta [Finite X] : K1 ι →* X where
  toFun k := k * (zh * k * zh⁻¹)
  map_one' := by rw [OneMemClass.coe_one, mul_one, mul_inv_cancel, one_mul]
  map_mul' a b := by
    have hc := h.K1_comm_K2 b.2 (h.conj_K1 a.2)
    show ((a : X) * b) * (zh * ((a : X) * b) * zh⁻¹) =
      ((a : X) * (zh * a * zh⁻¹)) * ((b : X) * (zh * b * zh⁻¹))
    calc ((a : X) * b) * (zh * ((a : X) * b) * zh⁻¹)
        = a * ((b : X) * (zh * a * zh⁻¹)) * (zh * b * zh⁻¹) := by group
      _ = a * ((zh * a * zh⁻¹) * (b : X)) * (zh * b * zh⁻¹) := by rw [hc]
      _ = ((a : X) * (zh * a * zh⁻¹)) * ((b : X) * (zh * b * zh⁻¹)) := by group

theorem HatData.delta_apply [Finite X] (k : K1 ι) :
    h.delta k = (k : X) * (zh * k * zh⁻¹) := rfl

theorem HatData.delta_injective [Finite X] : Function.Injective h.delta := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rw [h.delta_apply] at hk
  have h1 : (k : X) = (zh * k * zh⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hk
  have h2 : (k : X) ∈ K1 ι ⊓ K2 ι := mem_inf.2 ⟨k.2, h1 ▸ inv_mem (h.conj_K1 k.2)⟩
  rw [h.K1_inf_K2, mem_bot] at h2
  exact Subtype.ext h2

theorem HatData.mem_diag_iff [Finite X] {B : Subgroup X} (hBX : B ≤ X0 ι)
    (hBz : ∀ b ∈ B, zh * b * zh⁻¹ = b) (hBc : Nat.card B = 1344) (g : X) :
    g ∈ B ↔ ∃ k ∈ K1 ι, g = k * (zh * k * zh⁻¹) := by
  have hle : B ≤ h.delta.range := by
    intro g hg
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h.exists_mul_of_mem_X0 (hBX hg)
    have hz := hBz _ hg
    have e : zh * (k₁ * k₂) * zh⁻¹ = (zh * k₂ * zh⁻¹) * (zh * k₁ * zh⁻¹) := by
      rw [show zh * (k₁ * k₂) * zh⁻¹ = (zh * k₁ * zh⁻¹) * (zh * k₂ * zh⁻¹) by group]
      exact (h.K1_comm_K2 (h.conj_K2 hk₂) (h.conj_K1 hk₁)).symm
    rw [e] at hz
    obtain ⟨-, h2⟩ := h.eq_of_mul_eq (h.conj_K2 hk₂) hk₁ (h.conj_K1 hk₁) hk₂ hz
    refine ⟨⟨k₁, hk₁⟩, ?_⟩
    rw [h.delta_apply]
    show k₁ * (zh * k₁ * zh⁻¹) = k₁ * k₂
    rw [h2]
  have hcard : Nat.card h.delta.range = 1344 := by
    rw [← h.card_K1]
    exact (Nat.card_congr (MonoidHom.ofInjective h.delta_injective).toEquiv).symm
  have heq : B = h.delta.range := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hBc])
  rw [heq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem HatData.exists_decomp [Finite X] (x : X) :
    ∃ k₁ ∈ K1 ι, ∃ k₂ ∈ K2 ι, x = k₁ * k₂ ∨ x = zh⁻¹ * (k₁ * k₂) := by
  rcases h.mem_X0_or x with hx | hx
  · obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h.exists_mul_of_mem_X0 hx
    exact ⟨k₁, hk₁, k₂, hk₂, Or.inl rfl⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := h.exists_mul_of_mem_X0 hx
    refine ⟨k₁, hk₁, k₂, hk₂, Or.inr ?_⟩
    rw [← hk]
    group

end Rho

end Data

end CFSG.OddStandard.AltStdSmall4.W49
