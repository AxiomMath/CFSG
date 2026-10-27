module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferCocycle
public import Mathlib.Algebra.Group.MinimalAxioms

public section

namespace CFSG.ComponentClassification.M12Cover

@[expose] def packNat (l : List ℕ) : ℕ := l.foldl (fun acc c => acc * 10 ^ 90 + c) 0

@[expose] def packEntry (T w k : ℕ) : ℕ := (T >>> (w * k)) % 2 ^ w

theorem packEntry_lt (T w k : ℕ) : packEntry T w k < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

theorem all_range {n : ℕ} {q : ℕ → Bool} (h : (List.range n).all q = true) {i : ℕ}
    (hi : i < n) : q i = true :=
  List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem zmod2_add_self (v : ZMod 2) : v + v = 0 := by
  fin_cases v <;> rfl

theorem zmod2_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

open CFSG.ComponentClassification.CentralCover in
theorem cocycle_of_closure {Q : Type*} [Group Q] {f : Q → Q → ZMod 2} {Y : Set Q}
    (hY : Subgroup.closure Y = ⊤) (hl : ∀ t, f 1 t = 0)
    (hc : ∀ y ∈ Y, ∀ t u, f y t + f (y * t) u = f t u + f y (t * u))
    (hc' : ∀ y ∈ Y, ∀ t u, f y⁻¹ t + f (y⁻¹ * t) u = f t u + f y⁻¹ (t * u)) :
    ∀ s t u, f s t + f (s * t) u = f t u + f s (t * u) := by
  have step : ∀ y x : Q, (∀ t u, f y t + f (y * t) u = f t u + f y (t * u)) →
      (∀ t u, f x t + f (x * t) u = f t u + f x (t * u)) →
      ∀ t u, f (y * x) t + f (y * x * t) u = f t u + f (y * x) (t * u) := by
    intro y x hy hx t u
    have e1 := hy x t
    have e2 := hy (x * t) u
    have e3 := hy x (t * u)
    have e4 := hx t u
    rw [← mul_assoc] at e2 e3
    rw [mul_assoc y x t, mul_assoc] at *
    grind
  intro s t u
  have hs : s ∈ Subgroup.closure Y := by rw [hY]; exact Subgroup.mem_top s
  induction hs using Subgroup.closure_induction_left generalizing t u with
  | one => simp [hl]
  | mul_left y hy x _ ih => exact step y x (hc y hy) (fun t u => ih t u) t u
  | inv_mul_cancel y hy x _ ih => exact step y⁻¹ x (hc' y hy) (fun t u => ih t u) t u

open CFSG.ComponentClassification.CentralCover in
@[expose] def cochainAut {Q : Type*} [Group Q] {f : NormCocycle Q} (α : Q ≃* Q)
    (l : Q → ZMod 2) (hl : ∀ s t, l s + l t + l (s * t) = f (α s) (α t) + f s t) :
    CocycleExtension f ≃* CocycleExtension f where
  toFun x := ⟨x.fst + l x.snd, α x.snd⟩
  invFun x := ⟨x.fst + l (α.symm x.snd), α.symm x.snd⟩
  left_inv x := by
    refine CocycleExtension.ext ?_ (α.symm_apply_apply x.snd)
    change x.fst + l x.snd + l (α.symm (α x.snd)) = x.fst
    rw [MulEquiv.symm_apply_apply, add_assoc, zmod2_add_self, add_zero]
  right_inv x := by
    refine CocycleExtension.ext ?_ (α.apply_symm_apply x.snd)
    change x.fst + l (α.symm x.snd) + l (α.symm x.snd) = x.fst
    rw [add_assoc, zmod2_add_self, add_zero]
  map_mul' x y := by
    refine CocycleExtension.ext ?_ (map_mul α x.snd y.snd)
    change x.fst + y.fst + f x.snd y.snd + l (x.snd * y.snd) =
      x.fst + l x.snd + (y.fst + l y.snd) + f (α x.snd) (α y.snd)
    have := hl x.snd y.snd
    grind

open CFSG.ComponentClassification.CentralCover in
theorem cochainAut_apply {Q : Type*} [Group Q] {f : NormCocycle Q} (α : Q ≃* Q)
    (l : Q → ZMod 2) (hl : ∀ s t, l s + l t + l (s * t) = f (α s) (α t) + f s t)
    (x : CocycleExtension f) : cochainAut α l hl x = ⟨x.fst + l x.snd, α x.snd⟩ :=
  rfl

structure TwistHyp {R : Type*} [Group R] (τ : R ≃* R) (z : R) : Prop where
  invol : ∀ x, τ (τ x) = x
  comm : ∀ x, z * x = x * z
  fix : τ z = z

@[ext] structure TwistExt {R : Type*} [Group R] (τ : R ≃* R) (z : R) where
  x : R
  e : ZMod 2

namespace TwistExt

variable {R : Type*} [Group R] {τ : R ≃* R} {z : R}

@[expose] def twist (τ : R ≃* R) (e : ZMod 2) (y : R) : R := if e = 1 then τ y else y

@[expose] def zpow2 (z : R) (c : ZMod 2) : R := if c = 1 then z else 1

instance instMul : Mul (TwistExt τ z) :=
  ⟨fun a b => ⟨a.x * twist τ a.e b.x * zpow2 z (a.e * b.e), a.e + b.e⟩⟩

instance instOne : One (TwistExt τ z) := ⟨⟨1, 0⟩⟩

instance instInv : Inv (TwistExt τ z) :=
  ⟨fun a => ⟨twist τ a.e a.x⁻¹ * (zpow2 z a.e)⁻¹, a.e⟩⟩

theorem mul_def (a b : TwistExt τ z) :
    a * b = ⟨a.x * twist τ a.e b.x * zpow2 z (a.e * b.e), a.e + b.e⟩ := rfl

theorem one_def : (1 : TwistExt τ z) = ⟨1, 0⟩ := rfl

theorem inv_def (a : TwistExt τ z) : a⁻¹ = ⟨twist τ a.e a.x⁻¹ * (zpow2 z a.e)⁻¹, a.e⟩ := rfl

theorem twist_zero (y : R) : twist τ 0 y = y := by simp [twist]

theorem twist_one (y : R) : twist τ 1 y = τ y := by simp [twist]

theorem zpow2_zero : zpow2 z 0 = 1 := by simp [zpow2]

theorem zpow2_one : zpow2 z 1 = z := by simp [zpow2]

instance instGroup [h : Fact (TwistHyp τ z)] : Group (TwistExt τ z) :=
  Group.ofLeftAxioms
    (fun a b c => by
      obtain ⟨hτ, hz, hτz⟩ := h.out
      ext
      · simp only [mul_def]
        rcases zmod2_cases a.e with ha | ha <;> rcases zmod2_cases b.e with hb | hb <;>
          rcases zmod2_cases c.e with hc | hc <;>
          simp only [ha, hb, hc, twist_zero, twist_one, zpow2_zero, zpow2_one, map_mul, hτ, hτz,
            mul_one, mul_zero, zero_add, add_zero,
            show (1 : ZMod 2) + 1 = 0 from rfl, show (1 : ZMod 2) * 1 = 1 from rfl] <;>
          simp only [mul_assoc, hz]
      · simp only [mul_def, add_assoc])
    (fun a => by
      ext
      · simp [mul_def, one_def, twist, zpow2]
      · simp [mul_def, one_def])
    (fun a => by
      obtain ⟨hτ, hz, hτz⟩ := h.out
      ext
      · simp only [mul_def, inv_def, one_def]
        rcases zmod2_cases a.e with ha | ha
        · simp [ha, twist_zero, zpow2_zero]
        · simp only [ha, twist_one, zpow2_one, show (1 : ZMod 2) * 1 = 1 from rfl, map_inv]
          rw [mul_assoc, ← hz, mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
      · simp only [mul_def, inv_def, one_def]
        exact zmod2_add_self a.e)

@[expose] def equivProd : TwistExt τ z ≃ R × ZMod 2 where
  toFun a := (a.x, a.e)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFinite [Finite R] : Finite (TwistExt τ z) := Finite.of_equiv _ equivProd.symm

theorem card [Finite R] : Nat.card (TwistExt τ z) = 2 * Nat.card R := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_zmod, mul_comm]

variable [h : Fact (TwistHyp τ z)]

@[expose] def inl : R →* TwistExt τ z where
  toFun x := ⟨x, 0⟩
  map_one' := rfl
  map_mul' _ _ := by
    ext
    · simp [mul_def, twist_zero, zpow2_zero]
    · simp [mul_def]

theorem inl_injective : Function.Injective (inl : R →* TwistExt τ z) :=
  fun _ _ h => congrArg TwistExt.x h

@[expose] def t : TwistExt τ z := ⟨1, 1⟩

theorem t_mul_t : (t : TwistExt τ z) * t = inl z := by
  ext
  · simp [mul_def, t, inl, twist_one, zpow2_one]
  · simp only [mul_def, t, inl]
    rfl

theorem t_conj (x : R) : (t : TwistExt τ z) * inl x * t⁻¹ = inl (τ x) := by
  obtain ⟨hτ, hz, hτz⟩ := h.out
  ext
  · simp [mul_def, inv_def, t, inl, twist, zpow2, hτz]
  · simp only [mul_def, inv_def, t, inl]
    rfl

end TwistExt

@[expose] noncomputable def rootCount {G : Type*} [Monoid G] (n : ℕ) (z : G) : ℕ :=
  Nat.card {x : G // x ^ n = z}

theorem rootCount_map {G H : Type*} [Monoid G] [Monoid H] (φ : G ≃* H) (n : ℕ) (z : G) :
    rootCount n (φ z) = rootCount n z := by
  refine (Nat.card_congr (φ.toEquiv.subtypeEquiv fun x => ?_)).symm
  change x ^ n = z ↔ φ x ^ n = φ z
  rw [← map_pow, φ.injective.eq_iff]

theorem map_mem_center {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {z : G}
    (hz : z ∈ Subgroup.center G) : φ z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [← map_mul, ← map_mul, hz]

theorem aut_apply_eq_of_rootCount {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G)
    (h : ∀ w ∈ Subgroup.center G, rootCount 2 w = rootCount 2 z →
      rootCount 4 w = rootCount 4 z → w = z) : φ z = z :=
  h _ (map_mem_center φ hz) (rootCount_map φ 2 z) (rootCount_map φ 4 z)

theorem aut_fixes_center {G : Type*} [Group G] {z₁ z₂ z₃ : G}
    (hc : ∀ w, w ∈ Subgroup.center G ↔ w = 1 ∨ w = z₁ ∨ w = z₂ ∨ w = z₃)
    (h₁ : z₁ ≠ 1) (h₂ : z₂ ≠ 1) (h₃ : z₃ ≠ 1)
    (h₁₂ : (rootCount 2 z₁, rootCount 4 z₁) ≠ (rootCount 2 z₂, rootCount 4 z₂))
    (h₁₃ : (rootCount 2 z₁, rootCount 4 z₁) ≠ (rootCount 2 z₃, rootCount 4 z₃))
    (h₂₃ : (rootCount 2 z₂, rootCount 4 z₂) ≠ (rootCount 2 z₃, rootCount 4 z₃))
    (φ : MulAut G) : ∀ w ∈ Subgroup.center G, φ w = w := by
  have key : ∀ w, w ≠ 1 → w ∈ Subgroup.center G →
      (∀ w' ∈ Subgroup.center G, w' ≠ 1 → w' ≠ w →
        (rootCount 2 w', rootCount 4 w') ≠ (rootCount 2 w, rootCount 4 w)) → φ w = w := by
    intro w hw hwc hd
    by_contra hne
    refine hd (φ w) (map_mem_center φ hwc) (fun h1 => hw ?_) hne
      (Prod.ext (rootCount_map φ 2 w) (rootCount_map φ 4 w))
    exact φ.injective (h1.trans (map_one φ).symm)
  intro w hw
  rcases (hc w).1 hw with rfl | rfl | rfl | rfl
  · exact map_one φ
  · refine key _ h₁ hw fun w' hw' h1 hne => ?_
    rcases (hc w').1 hw' with rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl hne
    · exact fun h => h₁₂ h.symm
    · exact fun h => h₁₃ h.symm
  · refine key _ h₂ hw fun w' hw' h1 hne => ?_
    rcases (hc w').1 hw' with rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · exact h₁₂
    · exact absurd rfl hne
    · exact fun h => h₂₃ h.symm
  · refine key _ h₃ hw fun w' hw' h1 hne => ?_
    rcases (hc w').1 hw' with rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · exact h₁₃
    · exact h₂₃
    · exact absurd rfl hne

theorem card_fin_subtype_eq_countP (N : ℕ) (q : ℕ → Bool) :
    Nat.card {x : Fin N // q x = true} = (List.range N).countP q := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if q i = true then 1 else 0) N]
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    simp [List.countP_cons]

@[expose] def IsTableModel {G : Type*} [Mul G] {N : ℕ} (mul : Fin N → Fin N → Fin N)
    (enc : Fin N ≃ G) : Prop :=
  ∀ x y, enc (mul x y) = enc x * enc y

namespace IsTableModel

variable {G : Type*} [Monoid G] {N : ℕ} {mul : Fin N → Fin N → Fin N} {enc : Fin N ≃ G}

theorem enc_sq (h : IsTableModel mul enc) (x : Fin N) : enc (mul x x) = enc x ^ 2 := by
  rw [h, sq]

theorem enc_pow_four (h : IsTableModel mul enc) (x : Fin N) :
    enc (mul (mul x x) (mul x x)) = enc x ^ 4 := by
  rw [h, enc_sq h, ← pow_add]

theorem rootCount_two (h : IsTableModel mul enc) (z : Fin N) :
    rootCount 2 (enc z) = Nat.card {x : Fin N // mul x x = z} := by
  refine (Nat.card_congr (enc.subtypeEquiv fun x => ?_)).symm
  rw [← enc_sq h, enc.injective.eq_iff]

theorem rootCount_four (h : IsTableModel mul enc) (z : Fin N) :
    rootCount 4 (enc z) = Nat.card {x : Fin N // mul (mul x x) (mul x x) = z} := by
  refine (Nat.card_congr (enc.subtypeEquiv fun x => ?_)).symm
  rw [← enc_pow_four h, enc.injective.eq_iff]

theorem mem_center_iff {G : Type*} [Group G] {mul : Fin N → Fin N → Fin N} {enc : Fin N ≃ G}
    (h : IsTableModel mul enc) (z : Fin N) :
    enc z ∈ Subgroup.center G ↔ ∀ x, mul z x = mul x z := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hz x
    apply enc.injective
    rw [h, h, hz]
  · intro hz g
    obtain ⟨x, rfl⟩ := enc.surjective g
    rw [← h, ← h, hz]

end IsTableModel

end CFSG.ComponentClassification.M12Cover
