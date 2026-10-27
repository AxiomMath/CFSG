module

public import Mathlib.Algebra.Field.MinimalAxioms
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Fin

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

@[ext] structure F4c where
  a : ZMod 2
  b : ZMod 2

namespace F4c

instance : DecidableEq F4c := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b) (by cases x; cases y; simp)

instance : Fintype F4c :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2)
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun x => (x.a, x.b)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

instance : Zero F4c := ⟨⟨0, 0⟩⟩
instance : One F4c := ⟨⟨1, 0⟩⟩
instance : Add F4c := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg F4c := ⟨fun x => x⟩
instance : Mul F4c := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩
instance : Inv F4c := ⟨fun x => x * x⟩

instance instField : Field F4c :=
  Field.ofMinimalAxioms F4c (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end F4c

@[ext] structure F16c where
  a0 : ZMod 2
  a1 : ZMod 2
  a2 : ZMod 2
  a3 : ZMod 2

namespace F16c

instance : DecidableEq F16c := fun x y =>
  decidable_of_iff (x.a0 = y.a0 ∧ x.a1 = y.a1 ∧ x.a2 = y.a2 ∧ x.a3 = y.a3) (by
    cases x; cases y; simp)

instance : Fintype F16c :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
      invFun := fun x => (x.a0, x.a1, x.a2, x.a3)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

instance : Zero F16c := ⟨⟨0, 0, 0, 0⟩⟩
instance : One F16c := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add F16c := ⟨fun x y => ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3⟩⟩
instance : Neg F16c := ⟨fun x => x⟩
instance : Mul F16c := ⟨fun x y =>
  let c0 := x.a0 * y.a0
  let c1 := x.a0 * y.a1 + x.a1 * y.a0
  let c2 := x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0
  let c3 := x.a0 * y.a3 + x.a1 * y.a2 + x.a2 * y.a1 + x.a3 * y.a0
  let c4 := x.a1 * y.a3 + x.a2 * y.a2 + x.a3 * y.a1
  let c5 := x.a2 * y.a3 + x.a3 * y.a2
  let c6 := x.a3 * y.a3
  ⟨c0 + c4, c1 + c4 + c5, c2 + c5 + c6, c3 + c6⟩⟩
instance : Inv F16c := ⟨fun x =>
  let x2 := x * x
  let x4 := x2 * x2
  let x8 := x4 * x4
  x8 * x4 * x2⟩

instance instField : Field F16c :=
  Field.ofMinimalAxioms F16c (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def barc (x : F16c) : F16c := x ^ 4

theorem barc_add : ∀ x y : F16c, barc (x + y) = barc x + barc y := by decide +kernel

theorem barc_mul (x y : F16c) : barc (x * y) = barc x * barc y := by
  simp [barc, mul_pow]

theorem barc_barc : ∀ x : F16c, barc (barc x) = x := by decide +kernel

theorem two_eq_zero : (2 : F16c) = 0 := by decide +kernel

end F16c

open F16c

noncomputable def e4 : F4 ≃+* F4c :=
  let _ : Fintype F4 := Fintype.ofFinite F4
  FiniteField.ringEquivOfCardEq (K := F4) (K' := F4c) (by
    have h1 : Fintype.card F4 = 4 := by
      rw [← Nat.card_eq_fintype_card]
      have := GaloisField.card 2 2 (by norm_num)
      simpa using this
    rw [h1]
    decide)

noncomputable def e16 : F16 ≃+* F16c :=
  let _ : Fintype F16 := Fintype.ofFinite F16
  FiniteField.ringEquivOfCardEq (K := F16) (K' := F16c) (by
    have h1 : Fintype.card F16 = 16 := by
      rw [← Nat.card_eq_fintype_card]
      have := GaloisField.card 2 4 (by norm_num)
      simpa using this
    rw [h1]
    decide)

theorem e16_bar (x : F16) : e16 (bar x) = barc (e16 x) := by
  rw [bar_apply, map_pow]; rfl

def ut3Congr {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    UT3 R ≃* UT3 R' where
  toFun u := ⟨e u.a, e u.b, e u.c⟩
  invFun u := ⟨e.symm u.a, e.symm u.b, e.symm u.c⟩
  left_inv u := by ext <;> simp
  right_inv u := by ext <;> simp
  map_mul' u v := by ext <;> simp [UT3.mul_def, map_add, map_mul]

instance : DecidableEq (UT3 F4c) := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.c = y.c) (by cases x; cases y; simp)

instance : Fintype (UT3 F4c) :=
  Fintype.ofEquiv (F4c × F4c × F4c)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      invFun := fun x => (x.a, x.b, x.c)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

@[ext] structure UHc where
  a : F16c
  b : F16c

namespace UHc

instance : Mul UHc := ⟨fun x y => ⟨x.a + y.a, x.b + y.b + x.a * barc y.a⟩⟩
instance : One UHc := ⟨⟨0, 0⟩⟩
instance : Inv UHc := ⟨fun x => ⟨-x.a, -x.b + x.a * barc x.a⟩⟩

theorem mul_def (x y : UHc) : x * y = ⟨x.a + y.a, x.b + y.b + x.a * barc y.a⟩ := rfl
theorem one_def : (1 : UHc) = ⟨0, 0⟩ := rfl
theorem inv_def (x : UHc) : x⁻¹ = ⟨-x.a, -x.b + x.a * barc x.a⟩ := rfl

instance : Group UHc where
  mul_assoc x y z := by
    refine UHc.ext ?_ ?_
    · simp only [mul_def]; ring
    · simp only [mul_def, barc_add]; ring
  one_mul x := by
    refine UHc.ext ?_ ?_
    · simp only [mul_def, one_def]; ring
    · simp only [mul_def, one_def]; ring
  mul_one x := by
    refine UHc.ext ?_ ?_
    · simp only [mul_def, one_def]; ring
    · simp only [mul_def, one_def]; simp [barc]
  inv_mul_cancel x := by
    refine UHc.ext ?_ ?_
    · simp only [mul_def, one_def, inv_def]; ring
    · simp only [mul_def, one_def, inv_def]; ring

instance : DecidableEq UHc := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b) (by cases x; cases y; simp)

instance : Fintype UHc :=
  Fintype.ofEquiv (F16c × F16c)
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun x => (x.a, x.b)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

end UHc

def sylSU3c : Subgroup UHc where
  carrier := {x | x.b + barc x.b + x.a * barc x.a = 0}
  mul_mem' := by
    intro x y hx hy
    change x.b + barc x.b + x.a * barc x.a = 0 at hx
    change y.b + barc y.b + y.a * barc y.a = 0 at hy
    change (x * y).b + barc (x * y).b + (x * y).a * barc (x * y).a = 0
    simp only [UHc.mul_def, barc_add, barc_mul, barc_barc]
    linear_combination hx + hy + (x.a * barc y.a + barc x.a * y.a) * two_eq_zero
  one_mem' := by
    change (1 : UHc).b + barc (1 : UHc).b + (1 : UHc).a * barc (1 : UHc).a = 0
    show (0 : F16c) + barc 0 + 0 * barc 0 = 0
    decide +kernel
  inv_mem' := by
    intro x hx
    change x.b + barc x.b + x.a * barc x.a = 0 at hx
    change (x⁻¹).b + barc (x⁻¹).b + (x⁻¹).a * barc (x⁻¹).a = 0
    have hneg : ∀ y : F16c, barc (-y) = -barc y := by decide +kernel
    simp only [UHc.inv_def, barc_add, hneg, barc_mul, barc_barc]
    linear_combination (-1 : F16c) * hx + (2 * x.a * barc x.a) * two_eq_zero

instance : DecidablePred (· ∈ sylSU3c) := fun x =>
  inferInstanceAs (Decidable (x.b + barc x.b + x.a * barc x.a = 0))

theorem mem_sylSU3c (x : UHc) : x ∈ sylSU3c ↔ x.b + barc x.b + x.a * barc x.a = 0 :=
  ⟨fun h => h, fun h => h⟩

noncomputable def uhCongr : UH ≃* UHc where
  toFun u := ⟨e16 u.a, e16 u.b⟩
  invFun u := ⟨e16.symm u.a, e16.symm u.b⟩
  left_inv u := by ext <;> simp
  right_inv u := by refine UHc.ext ?_ ?_ <;> simp
  map_mul' u v := by
    refine UHc.ext ?_ ?_ <;> simp [UH.mul_def, UHc.mul_def, map_add, map_mul, e16_bar]

theorem sylSU3_map : sylSU3.map uhCongr.toMonoidHom = sylSU3c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y.b + bar y.b + y.a * bar y.a = 0 := (mem_sylSU3 y).mp hy
    have := congrArg e16 hy'
    simpa [mem_sylSU3c, uhCongr, map_add, map_mul, e16_bar] using this
  · intro hx
    refine ⟨uhCongr.symm x, (mem_sylSU3 _).mpr ?_, by simp⟩
    have hx' : x.b + barc x.b + x.a * barc x.a = 0 := hx
    apply e16.injective
    simpa [uhCongr, map_add, map_mul, e16_bar] using hx'

noncomputable def sylCongr : SylSU3_4 ≃* ↥sylSU3c :=
  (MulEquiv.subgroupMap uhCongr sylSU3).trans (MulEquiv.subgroupCongr sylSU3_map)

noncomputable def sylLCongr : SylSL3_4 ≃* UT3 F4c := ut3Congr e4

theorem card_UT3c : Nat.card (UT3 F4c) = 64 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_sylSU3c : Nat.card ↥sylSU3c = 64 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem inv_count_L : Fintype.card {t : UT3 F4c // t * t = 1 ∧ t ≠ 1} = 27 := by
  decide +kernel

theorem inv_count_S : Fintype.card {t : ↥sylSU3c // t * t = 1 ∧ t ≠ 1} = 3 := by
  decide +kernel

@[expose] def embOf {M : Type} [Group M] (e₁ e₂ : M) (v : Vec) : M :=
  e₁ ^ v.1.val * e₂ ^ v.2.val

@[expose] def mkData {M : Type} [Group M] (e₁ e₂ p q : M) (α β γ : Vec)
    (hemb : (∀ v w, embOf e₁ e₂ (v + w) = embOf e₁ e₂ v * embOf e₁ e₂ w) ∧
      Function.Injective (embOf e₁ e₂))
    (hrel : (∀ v, p * embOf e₁ e₂ v = embOf e₁ e₂ (PP v) * p) ∧
      (∀ v, q * embOf e₁ e₂ v = embOf e₁ e₂ (QQ v) * q) ∧
      p * p = embOf e₁ e₂ α ∧ q * q = embOf e₁ e₂ β ∧ q * p = p * q * embOf e₁ e₂ γ) :
    ExtData PP QQ M where
  emb := embOf e₁ e₂
  emb_add := hemb.1
  emb_inj := hemb.2
  p := p
  q := q
  α := α
  β := β
  γ := γ
  hp := hrel.1
  hq := hrel.2.1
  hpp := hrel.2.2.1
  hqq := hrel.2.2.2.1
  hqp := hrel.2.2.2.2

@[expose] def EmbOK {M : Type} [Group M] (e₁ e₂ : M) : Prop :=
  (∀ v w, embOf e₁ e₂ (v + w) = embOf e₁ e₂ v * embOf e₁ e₂ w) ∧ Function.Injective (embOf e₁ e₂)

@[expose] def RelOK {M : Type} [Group M] (e₁ e₂ p q : M) (π : Vec × Vec × Vec) : Prop :=
  (∀ v, p * embOf e₁ e₂ v = embOf e₁ e₂ (PP v) * p) ∧
    (∀ v, q * embOf e₁ e₂ v = embOf e₁ e₂ (QQ v) * q) ∧
    p * p = embOf e₁ e₂ π.1 ∧ q * q = embOf e₁ e₂ π.2.1 ∧
    q * p = p * q * embOf e₁ e₂ π.2.2

instance {M : Type} [Group M] [DecidableEq M] (e₁ e₂ : M) : Decidable (EmbOK e₁ e₂) := by
  unfold EmbOK
  haveI : Decidable (Function.Injective (embOf e₁ e₂)) :=
    Fintype.decidableInjectiveFintype (embOf e₁ e₂)
  infer_instance

instance {M : Type} [Group M] [DecidableEq M] (e₁ e₂ p q : M) (π : Vec × Vec × Vec) :
    Decidable (RelOK e₁ e₂ p q π) := by
  unfold RelOK; infer_instance

def eL1 : UT3 F4c := ⟨⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩⟩

def eL2 : UT3 F4c := ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩⟩

def tabL : List ((Vec × Vec × Vec) × UT3 F4c × UT3 F4c) :=
  [(((0, 0), (0, 0), (0, 0)), ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩),
   (((0, 0), (0, 0), (2, 0)), ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩),
   (((0, 0), (0, 2), (0, 2)), ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩),
   (((0, 0), (0, 2), (2, 2)), ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩),
   (((2, 2), (0, 0), (0, 2)), ⟨⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩),
   (((2, 2), (0, 0), (2, 2)), ⟨⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩, ⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩),
   (((2, 2), (0, 2), (0, 0)), ⟨⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩, ⟨⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩),
   (((2, 2), (0, 2), (2, 0)), ⟨⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩, ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩)]

def eS1 : UHc := ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩

def eS2 : UHc := ⟨⟨0, 1, 1, 0⟩, ⟨1, 1, 1, 1⟩⟩

def tabS : List ((Vec × Vec × Vec) × UHc × UHc) :=
  [(((0, 2), (2, 0), (0, 0)), ⟨⟨1, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 0⟩⟩),
   (((0, 2), (2, 0), (2, 0)), ⟨⟨1, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 0⟩⟩),
   (((0, 2), (2, 2), (0, 2)), ⟨⟨1, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨1, 1, 0, 1⟩, ⟨0, 1, 0, 1⟩⟩),
   (((0, 2), (2, 2), (2, 2)), ⟨⟨1, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨1, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩⟩),
   (((2, 0), (2, 0), (0, 2)), ⟨⟨0, 0, 0, 1⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 0⟩⟩),
   (((2, 0), (2, 0), (2, 2)), ⟨⟨0, 0, 0, 1⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 0⟩⟩),
   (((2, 0), (2, 2), (0, 0)), ⟨⟨0, 0, 0, 1⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨1, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩⟩),
   (((2, 0), (2, 2), (2, 0)), ⟨⟨0, 0, 0, 1⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨1, 1, 0, 1⟩, ⟨0, 1, 0, 1⟩⟩)]

theorem embOK_L : EmbOK eL1 eL2 := by decide +kernel

theorem embOK_S : EmbOK eS1 eS2 := by decide +kernel

theorem relOK_LB : (tabL.all fun t => decide (RelOK eL1 eL2 t.2.1 t.2.2 t.1)) = true := by
  decide +kernel

theorem relOK_SB : (tabS.all fun t => decide (RelOK eS1 eS2 t.2.1 t.2.2 t.1)) = true := by
  decide +kernel

theorem relOK_L : ∀ t ∈ tabL, RelOK eL1 eL2 t.2.1 t.2.2 t.1 := by
  intro t ht
  have h := relOK_LB
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h t ht)

theorem relOK_S : ∀ t ∈ tabS, RelOK eS1 eS2 t.2.1 t.2.2 t.1 := by
  intro t ht
  have h := relOK_SB
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h t ht)

theorem S16_cover_B : (S16.all fun π => tabL.any (fun t => decide (t.1 = π)) ||
    tabS.any (fun t => decide (t.1 = π))) = true := by
  decide +kernel

theorem S16_cover (π : Vec × Vec × Vec) (hπ : π ∈ S16) :
    (∃ t ∈ tabL, t.1 = π) ∨ ∃ t ∈ tabS, t.1 = π := by
  have h := S16_cover_B
  rw [List.all_eq_true] at h
  have h1 := h π hπ
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at h1
  rcases h1 with ⟨t, ht, h2⟩ | ⟨t, ht, h2⟩
  · exact Or.inl ⟨t, ht, of_decide_eq_true h2⟩
  · exact Or.inr ⟨t, ht, of_decide_eq_true h2⟩

@[expose] noncomputable def dataL (t : (Vec × Vec × Vec) × UT3 F4c × UT3 F4c) (ht : t ∈ tabL) :
    ExtData PP QQ (UT3 F4c) :=
  mkData eL1 eL2 t.2.1 t.2.2 t.1.1 t.1.2.1 t.1.2.2 (by simpa [EmbOK] using embOK_L)
    (by simpa [RelOK] using relOK_L t ht)

@[expose] def ExtData.restrict {G : Type} [Group G] (D : ExtData PP QQ G) (H : Subgroup G)
    (hemb : ∀ v, D.emb v ∈ H) (hp : D.p ∈ H) (hq : D.q ∈ H) : ExtData PP QQ ↥H where
  emb v := ⟨D.emb v, hemb v⟩
  emb_add v w := Subtype.ext (D.emb_add v w)
  emb_inj _ _ h := D.emb_inj (congrArg Subtype.val h)
  p := ⟨D.p, hp⟩
  q := ⟨D.q, hq⟩
  α := D.α
  β := D.β
  γ := D.γ
  hp v := Subtype.ext (D.hp v)
  hq v := Subtype.ext (D.hq v)
  hpp := Subtype.ext D.hpp
  hqq := Subtype.ext D.hqq
  hqp := Subtype.ext D.hqp

theorem embmemS_B : (allVec.all fun v => decide (embOf eS1 eS2 v ∈ sylSU3c)) = true := by
  decide +kernel

theorem pqmemS_B : (tabS.all fun t => decide (t.2.1 ∈ sylSU3c) && decide (t.2.2 ∈ sylSU3c)) =
    true := by
  decide +kernel

theorem embmemS (v : Vec) : embOf eS1 eS2 v ∈ sylSU3c := by
  have h := embmemS_B
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h v (mem_allVec v))

theorem pmemS (t : (Vec × Vec × Vec) × UHc × UHc) (ht : t ∈ tabS) : t.2.1 ∈ sylSU3c := by
  have h := pqmemS_B
  rw [List.all_eq_true] at h
  have h1 := h t ht
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true h1.1

theorem qmemS (t : (Vec × Vec × Vec) × UHc × UHc) (ht : t ∈ tabS) : t.2.2 ∈ sylSU3c := by
  have h := pqmemS_B
  rw [List.all_eq_true] at h
  have h1 := h t ht
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true h1.2

@[expose] noncomputable def dataS (t : (Vec × Vec × Vec) × UHc × UHc) (ht : t ∈ tabS) :
    ExtData PP QQ ↥sylSU3c :=
  (mkData eS1 eS2 t.2.1 t.2.2 t.1.1 t.1.2.1 t.1.2.2 (by simpa [EmbOK] using embOK_S)
    (by simpa [RelOK] using relOK_S t ht)).restrict sylSU3c embmemS (pmemS t ht) (qmemS t ht)

theorem dataL_params (t : (Vec × Vec × Vec) × UT3 F4c × UT3 F4c) (ht : t ∈ tabL) :
    ((dataL t ht).α, (dataL t ht).β, (dataL t ht).γ) = t.1 := rfl

theorem dataS_params (t : (Vec × Vec × Vec) × UHc × UHc) (ht : t ∈ tabS) :
    ((dataS t ht).α, (dataS t ht).β, (dataS t ht).γ) = t.1 := rfl

end L23

end CFSG.GH74.GLS.Bg.TwoGroups
