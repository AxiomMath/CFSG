module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.NoncommCoprod

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

namespace DihedralPair

section Generators

variable {P : Type*} [Group P] {r b : P}

theorem zpow_val_eq_of_cast_eq (hr : orderOf r = 4) (a : ZMod 4) (k : ℤ)
    (h : (a : ZMod 4) = (k : ZMod 4)) : r ^ (a.val : ℤ) = r ^ k := by
  rw [zpow_eq_zpow_iff_modEq, hr, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact h

theorem conj_zpow_of_rel (hrel : b * r * b⁻¹ = r⁻¹) (k : ℤ) : b * r ^ k * b⁻¹ = r ^ (-k) := by
  have h := map_zpow (MulAut.conj b) r k
  rw [MulAut.conj_apply, MulAut.conj_apply, hrel, inv_zpow'] at h
  exact h

theorem zpow_mul_of_rel (hrel : b * r * b⁻¹ = r⁻¹) (k : ℤ) : r ^ k * b = b * r ^ (-k) := by
  have h := conj_zpow_of_rel hrel (-k)
  rw [neg_neg] at h
  calc r ^ k * b = b * r ^ (-k) * b⁻¹ * b := by rw [h]
    _ = b * r ^ (-k) := by group

@[expose] def dihedralFourHom (hr : orderOf r = 4) (hb : b⁻¹ = b) (hrel : b * r * b⁻¹ = r⁻¹) :
    DihedralGroup 4 →* P where
  toFun x := match x with
    | DihedralGroup.r i => r ^ (i.val : ℤ)
    | DihedralGroup.sr i => b * r ^ (i.val : ℤ)
  map_one' := by
    change r ^ ((0 : ZMod 4).val : ℤ) = 1
    rw [ZMod.val_zero, Nat.cast_zero, zpow_zero]
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j
    · rw [DihedralGroup.r_mul_r]
      change r ^ ((i + j).val : ℤ) = r ^ (i.val : ℤ) * r ^ (j.val : ℤ)
      rw [← zpow_add]
      exact zpow_val_eq_of_cast_eq hr _ _ (by push_cast [ZMod.natCast_zmod_val]; rfl)
    · rw [DihedralGroup.r_mul_sr]
      change b * r ^ ((j - i).val : ℤ) = r ^ (i.val : ℤ) * (b * r ^ (j.val : ℤ))
      rw [← mul_assoc, zpow_mul_of_rel hrel, mul_assoc, ← zpow_add]
      congr 1
      exact zpow_val_eq_of_cast_eq hr _ _
        (by push_cast [ZMod.natCast_zmod_val]; ring)
    · rw [DihedralGroup.sr_mul_r]
      change b * r ^ ((i + j).val : ℤ) = b * r ^ (i.val : ℤ) * r ^ (j.val : ℤ)
      rw [mul_assoc, ← zpow_add]
      congr 1
      exact zpow_val_eq_of_cast_eq hr _ _ (by push_cast [ZMod.natCast_zmod_val]; rfl)
    · rw [DihedralGroup.sr_mul_sr]
      change r ^ ((j - i).val : ℤ) = b * r ^ (i.val : ℤ) * (b * r ^ (j.val : ℤ))
      calc r ^ ((j - i).val : ℤ) = r ^ (-(i.val : ℤ)) * r ^ (j.val : ℤ) := by
            rw [← zpow_add]
            exact zpow_val_eq_of_cast_eq hr _ _
              (by push_cast [ZMod.natCast_zmod_val]; ring)
        _ = b * r ^ (i.val : ℤ) * b⁻¹ * r ^ (j.val : ℤ) := by rw [conj_zpow_of_rel hrel]
        _ = b * r ^ (i.val : ℤ) * (b * r ^ (j.val : ℤ)) := by rw [hb]; group

theorem dihedralFourHom_r (hr : orderOf r = 4) (hb : b⁻¹ = b) (hrel : b * r * b⁻¹ = r⁻¹)
    (i : ZMod 4) : dihedralFourHom hr hb hrel (DihedralGroup.r i) = r ^ (i.val : ℤ) :=
  rfl

theorem dihedralFourHom_sr (hr : orderOf r = 4) (hb : b⁻¹ = b) (hrel : b * r * b⁻¹ = r⁻¹)
    (i : ZMod 4) : dihedralFourHom hr hb hrel (DihedralGroup.sr i) = b * r ^ (i.val : ℤ) :=
  rfl

theorem dihedralFourHom_injective (hr : orderOf r = 4) (hb : b⁻¹ = b)
    (hrel : b * r * b⁻¹ = r⁻¹) (hbr : b ∉ zpowers r) :
    Function.Injective (dihedralFourHom hr hb hrel) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [dihedralFourHom_r, zpow_natCast] at h
    have hdvd : orderOf r ∣ i.val := orderOf_dvd_of_pow_eq_one h
    rw [hr] at hdvd
    have hlt : i.val < 4 := ZMod.val_lt i
    have hi : i.val = 0 := by omega
    rw [(ZMod.val_eq_zero i).mp hi]
    rfl
  · rw [dihedralFourHom_sr] at h
    exfalso
    apply hbr
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem (zpow_mem (mem_zpowers r) _)

theorem dihedralFourHom_surjective (hr : orderOf r = 4) (hb : b⁻¹ = b)
    (hrel : b * r * b⁻¹ = r⁻¹) (hgen : closure {r, b} = ⊤) :
    Function.Surjective (dihedralFourHom hr hb hrel) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
  rintro x (rfl | rfl)
  · refine ⟨DihedralGroup.r 1, ?_⟩
    rw [dihedralFourHom_r]
    have : (1 : ZMod 4).val = 1 := rfl
    rw [this, Nat.cast_one, zpow_one]
  · refine ⟨DihedralGroup.sr 0, ?_⟩
    rw [dihedralFourHom_sr, ZMod.val_zero, Nat.cast_zero, zpow_zero, mul_one]

end Generators

abbrev PairCoord := DihedralGroup 4 × DihedralGroup 4 × Fin 2

@[expose] def pairMul (μ : ℕ) : PairCoord → PairCoord → PairCoord
  | (g, h, 0), (g', h', a) => (g * g', h * h', a)
  | (g, h, 1), (g', h', 0) => (g * h', h * g', 1)
  | (g, h, 1), (g', h', 1) => (g * h' * DihedralGroup.r 2 ^ μ, h * g', 0)

@[expose] def PairEquiv (m m' : PairCoord) : Prop :=
  m'.2.2 = m.2.2 ∧ ((m'.1 = m.1 ∧ m'.2.1 = m.2.1) ∨
    (m'.1 = m.1 * DihedralGroup.r 2 ∧ m'.2.1 = m.2.1 * DihedralGroup.r 2))

instance (m m' : PairCoord) : Decidable (PairEquiv m m') := by
  unfold PairEquiv
  infer_instance

@[expose] def pairU : PairCoord := (DihedralGroup.sr 0, DihedralGroup.sr 0, 0)

@[expose] def pairZ : PairCoord := (DihedralGroup.r 2, 1, 0)

@[expose] def pairZU : PairCoord := (DihedralGroup.r 2 * DihedralGroup.sr 0, DihedralGroup.sr 0, 0)

@[expose] def PairInD (μ : ℕ) (m : PairCoord) : Prop :=
  PairEquiv (pairMul μ pairU m) (pairMul μ m pairU)

instance (μ : ℕ) (m : PairCoord) : Decidable (PairInD μ m) := by
  unfold PairInD
  infer_instance

theorem card_pairInD_zero : (Finset.univ.filter (fun m => PairInD 0 m)).card = 64 := by decide

theorem card_pairInD_one : (Finset.univ.filter (fun m => PairInD 1 m)).card = 64 := by decide

theorem card_pair_sq_z_zero :
    (Finset.univ.filter (fun m => PairInD 0 m ∧ PairEquiv (pairMul 0 m m) pairZ)).card = 8 := by
  decide

theorem card_pair_sq_z_one :
    (Finset.univ.filter (fun m => PairInD 1 m ∧ PairEquiv (pairMul 1 m m) pairZ)).card = 24 := by
  decide

theorem card_pair_sq_u_zero :
    (Finset.univ.filter (fun m => PairInD 0 m ∧ PairEquiv (pairMul 0 m m) pairU)).card = 8 := by
  decide

theorem card_pair_sq_u_one :
    (Finset.univ.filter (fun m => PairInD 1 m ∧ PairEquiv (pairMul 1 m m) pairU)).card = 8 := by
  decide

theorem card_pair_sq_zu_zero :
    (Finset.univ.filter (fun m => PairInD 0 m ∧ PairEquiv (pairMul 0 m m) pairZU)).card = 8 := by
  decide

theorem card_pair_sq_zu_one :
    (Finset.univ.filter (fun m => PairInD 1 m ∧ PairEquiv (pairMul 1 m m) pairZU)).card = 8 := by
  decide

theorem r_two_sq : (DihedralGroup.r 2 : DihedralGroup 4) ^ 2 = 1 := by decide

theorem r_two_inv : (DihedralGroup.r 2 : DihedralGroup 4)⁻¹ = DihedralGroup.r 2 := by decide

theorem r_two_comm (g : DihedralGroup 4) : g * DihedralGroup.r 2 = DihedralGroup.r 2 * g := by
  revert g
  decide

theorem r_two_ne_one : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1 := by decide

theorem mem_zpowers_eq_one_or_eq {G : Type*} [Group G] {g x : G} (hg : orderOf g = 2)
    (hx : x ∈ zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

variable {H : Type*} [Group H]

structure Model (φ₀ φ₁ : DihedralGroup 4 →* H) (z τ : H) (μ : ℕ) : Prop where
  inj₀ : Function.Injective φ₀
  inj₁ : Function.Injective φ₁
  zeta₀ : φ₀ (DihedralGroup.r 2) = z
  zeta₁ : φ₁ (DihedralGroup.r 2) = z
  central : z ∈ center H
  inter : φ₀.range ⊓ φ₁.range = zpowers z
  comm : ∀ x y, φ₁ y * φ₀ x = φ₀ x * φ₁ y
  sq : τ ^ 2 = z ^ μ
  swap₀ : ∀ x, τ * φ₀ x * τ⁻¹ = φ₁ x
  swap₁ : ∀ x, τ * φ₁ x * τ⁻¹ = φ₀ x
  not_mem : τ ∉ (φ₀.range : Set H) * (φ₁.range : Set H)
  gen : closure ((φ₀.range : Set H) ∪ φ₁.range ∪ {τ}) = ⊤

@[expose] def elem (φ₀ φ₁ : DihedralGroup 4 →* H) (τ : H) (m : PairCoord) : H :=
  φ₀ m.1 * φ₁ m.2.1 * τ ^ (m.2.2 : ℕ)

namespace Model

variable {φ₀ φ₁ : DihedralGroup 4 →* H} {z τ : H} {μ : ℕ}

theorem swap₀' (hM : Model φ₀ φ₁ z τ μ) (x : DihedralGroup 4) : τ * φ₀ x = φ₁ x * τ := by
  rw [← hM.swap₀ x]
  group

theorem swap₁' (hM : Model φ₀ φ₁ z τ μ) (x : DihedralGroup 4) : τ * φ₁ x = φ₀ x * τ := by
  rw [← hM.swap₁ x]
  group

theorem z_sq (hM : Model φ₀ φ₁ z τ μ) : z ^ 2 = 1 := by
  rw [← hM.zeta₀, ← map_pow, r_two_sq, map_one]

theorem orderOf_z (hM : Model φ₀ φ₁ z τ μ) : orderOf z = 2 := by
  apply orderOf_eq_prime hM.z_sq
  rw [← hM.zeta₀, ← map_one φ₀]
  exact fun h => r_two_ne_one (hM.inj₀ h)

theorem elem_mul (hM : Model φ₀ φ₁ z τ μ) (m m' : PairCoord) :
    elem φ₀ φ₁ τ m * elem φ₀ φ₁ τ m' = elem φ₀ φ₁ τ (pairMul μ m m') := by
  obtain ⟨g, h, a⟩ := m
  obtain ⟨g', h', a'⟩ := m'
  have hc := hM.comm
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have ha' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
  · change φ₀ g * φ₁ h * τ ^ 0 * (φ₀ g' * φ₁ h' * τ ^ 0) =
      φ₀ (g * g') * φ₁ (h * h') * τ ^ 0
    rw [pow_zero, mul_one, mul_one, mul_one, map_mul, map_mul]
    calc φ₀ g * φ₁ h * (φ₀ g' * φ₁ h') = φ₀ g * (φ₁ h * φ₀ g') * φ₁ h' := by
          simp only [mul_assoc]
      _ = φ₀ g * (φ₀ g' * φ₁ h) * φ₁ h' := by rw [hc]
      _ = φ₀ g * φ₀ g' * (φ₁ h * φ₁ h') := by simp only [mul_assoc]
  · change φ₀ g * φ₁ h * τ ^ 0 * (φ₀ g' * φ₁ h' * τ ^ 1) =
      φ₀ (g * g') * φ₁ (h * h') * τ ^ 1
    rw [pow_zero, mul_one, map_mul, map_mul]
    calc φ₀ g * φ₁ h * (φ₀ g' * φ₁ h' * τ ^ 1) =
        φ₀ g * (φ₁ h * φ₀ g') * φ₁ h' * τ ^ 1 := by simp only [mul_assoc]
      _ = φ₀ g * (φ₀ g' * φ₁ h) * φ₁ h' * τ ^ 1 := by rw [hc]
      _ = φ₀ g * φ₀ g' * (φ₁ h * φ₁ h') * τ ^ 1 := by simp only [mul_assoc]
  · change φ₀ g * φ₁ h * τ ^ 1 * (φ₀ g' * φ₁ h' * τ ^ 0) =
      φ₀ (g * h') * φ₁ (h * g') * τ ^ 1
    rw [pow_zero, pow_one, mul_one, map_mul, map_mul]
    calc φ₀ g * φ₁ h * τ * (φ₀ g' * φ₁ h') = φ₀ g * φ₁ h * (τ * φ₀ g') * φ₁ h' := by
          simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * (φ₁ g' * τ) * φ₁ h' := by rw [hM.swap₀']
      _ = φ₀ g * φ₁ h * φ₁ g' * (τ * φ₁ h') := by simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * φ₁ g' * (φ₀ h' * τ) := by rw [hM.swap₁']
      _ = φ₀ g * (φ₁ (h * g') * φ₀ h') * τ := by simp only [map_mul, mul_assoc]
      _ = φ₀ g * (φ₀ h' * φ₁ (h * g')) * τ := by rw [hc]
      _ = φ₀ g * φ₀ h' * (φ₁ h * φ₁ g') * τ := by simp only [map_mul, mul_assoc]
  · change φ₀ g * φ₁ h * τ ^ 1 * (φ₀ g' * φ₁ h' * τ ^ 1) =
      φ₀ (g * h' * DihedralGroup.r 2 ^ μ) * φ₁ (h * g') * τ ^ 0
    rw [pow_zero, pow_one, mul_one, map_mul, map_mul, map_pow, hM.zeta₀]
    have hzc : ∀ y : H, y * z ^ μ = z ^ μ * y := fun y =>
      mem_center_iff.mp (pow_mem hM.central μ) y
    calc φ₀ g * φ₁ h * τ * (φ₀ g' * φ₁ h' * τ) =
        φ₀ g * φ₁ h * (τ * φ₀ g') * φ₁ h' * τ := by simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * (φ₁ g' * τ) * φ₁ h' * τ := by rw [hM.swap₀']
      _ = φ₀ g * φ₁ h * φ₁ g' * (τ * φ₁ h') * τ := by simp only [mul_assoc]
      _ = φ₀ g * φ₁ h * φ₁ g' * (φ₀ h' * τ) * τ := by rw [hM.swap₁']
      _ = φ₀ g * (φ₁ (h * g') * φ₀ h') * τ ^ 2 := by simp only [map_mul, mul_assoc, pow_two]
      _ = φ₀ g * (φ₀ h' * φ₁ (h * g')) * z ^ μ := by rw [hc, hM.sq]
      _ = φ₀ g * φ₀ h' * (φ₁ (h * g') * z ^ μ) := by simp only [mul_assoc]
      _ = φ₀ g * φ₀ h' * (z ^ μ * φ₁ (h * g')) := by rw [hzc]
      _ = φ₀ g * φ₀ h' * z ^ μ * φ₁ (h * g') := by simp only [mul_assoc]

theorem inv_mul_pair (hM : Model φ₀ φ₁ z τ μ) (x y x' y' : DihedralGroup 4) :
    (φ₀ x * φ₁ y)⁻¹ * (φ₀ x' * φ₁ y') = φ₀ (x⁻¹ * x') * φ₁ (y⁻¹ * y') := by
  calc (φ₀ x * φ₁ y)⁻¹ * (φ₀ x' * φ₁ y') = φ₁ y⁻¹ * φ₀ (x⁻¹ * x') * φ₁ y' := by
        simp only [mul_inv_rev, map_mul, map_inv, mul_assoc]
    _ = φ₀ (x⁻¹ * x') * φ₁ y⁻¹ * φ₁ y' := by rw [hM.comm]
    _ = φ₀ (x⁻¹ * x') * φ₁ (y⁻¹ * y') := by simp only [map_mul, mul_assoc]

theorem elem_eq_iff (hM : Model φ₀ φ₁ z τ μ) (m m' : PairCoord) :
    elem φ₀ φ₁ τ m = elem φ₀ φ₁ τ m' ↔ PairEquiv m m' := by
  obtain ⟨g, h, a⟩ := m
  obtain ⟨g', h', a'⟩ := m'
  have hmemPP : ∀ x y : DihedralGroup 4,
      φ₀ x * φ₁ y ∈ (φ₀.range : Set H) * (φ₁.range : Set H) :=
    fun x y => Set.mul_mem_mul ⟨x, rfl⟩ ⟨y, rfl⟩
  constructor
  · intro heq
    have ha : a' = a := by
      have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      have ha' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
      rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
      · rfl
      · exfalso
        apply hM.not_mem
        change φ₀ g * φ₁ h * τ ^ 0 = φ₀ g' * φ₁ h' * τ ^ 1 at heq
        rw [pow_zero, mul_one, pow_one] at heq
        have hτ : τ = φ₀ (g'⁻¹ * g) * φ₁ (h'⁻¹ * h) := by
          rw [← hM.inv_mul_pair, heq]
          group
        rw [hτ]
        exact hmemPP _ _
      · exfalso
        apply hM.not_mem
        change φ₀ g * φ₁ h * τ ^ 1 = φ₀ g' * φ₁ h' * τ ^ 0 at heq
        rw [pow_zero, mul_one, pow_one] at heq
        have hτ : τ = φ₀ (g⁻¹ * g') * φ₁ (h⁻¹ * h') := by
          rw [← hM.inv_mul_pair, ← heq]
          group
        rw [hτ]
        exact hmemPP _ _
      · rfl
    subst ha
    refine ⟨rfl, ?_⟩
    have h2 : φ₀ g * φ₁ h = φ₀ g' * φ₁ h' := mul_right_cancel heq
    have hw : φ₀ (g'⁻¹ * g) = φ₁ (h' * h⁻¹) := by
      calc φ₀ (g'⁻¹ * g) = (φ₀ g')⁻¹ * (φ₀ g * φ₁ h) * (φ₁ h)⁻¹ := by
            simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one]
        _ = (φ₀ g')⁻¹ * (φ₀ g' * φ₁ h') * (φ₁ h)⁻¹ := by rw [h2]
        _ = φ₁ (h' * h⁻¹) := by simp only [map_mul, map_inv, inv_mul_cancel_left]
    have hwmem : φ₀ (g'⁻¹ * g) ∈ zpowers z := by
      rw [← hM.inter]
      exact mem_inf.mpr ⟨⟨_, rfl⟩, hw ▸ ⟨_, rfl⟩⟩
    rcases mem_zpowers_eq_one_or_eq hM.orderOf_z hwmem with h1 | h1
    · left
      have hg : g'⁻¹ * g = 1 := hM.inj₀ (by rw [h1, map_one])
      have hh : h' * h⁻¹ = 1 := hM.inj₁ (by rw [← hw, h1, map_one])
      exact ⟨inv_mul_eq_one.mp hg, mul_inv_eq_one.mp hh⟩
    · right
      have hg : g'⁻¹ * g = DihedralGroup.r 2 := hM.inj₀ (by rw [h1, hM.zeta₀])
      have hh : h' * h⁻¹ = DihedralGroup.r 2 := hM.inj₁ (by rw [← hw, h1, hM.zeta₁])
      constructor
      · calc g' = g * (g'⁻¹ * g)⁻¹ := by group
          _ = g * DihedralGroup.r 2 := by rw [hg, r_two_inv]
      · calc h' = h' * h⁻¹ * h := by group
          _ = h * DihedralGroup.r 2 := by rw [hh, r_two_comm]
  · rintro ⟨ha, (⟨hg, hh⟩ | ⟨hg, hh⟩)⟩
    · simp only at ha hg hh
      subst ha hg hh
      rfl
    · simp only at ha hg hh
      rw [ha, hg, hh]
      change φ₀ g * φ₁ h * τ ^ (a : ℕ) =
        φ₀ (g * DihedralGroup.r 2) * φ₁ (h * DihedralGroup.r 2) * τ ^ (a : ℕ)
      rw [map_mul, map_mul, hM.zeta₀, hM.zeta₁]
      congr 1
      have hzc : ∀ y : H, y * z = z * y := fun y => mem_center_iff.mp hM.central y
      calc φ₀ g * φ₁ h = φ₀ g * φ₁ h * (z * z) := by rw [← pow_two, hM.z_sq, mul_one]
        _ = φ₀ g * (φ₁ h * z) * z := by simp only [mul_assoc]
        _ = φ₀ g * (z * φ₁ h) * z := by rw [hzc (φ₁ h)]
        _ = φ₀ g * z * (φ₁ h * z) := by simp only [mul_assoc]

theorem elem_surjective (hM : Model φ₀ φ₁ z τ μ) : Function.Surjective (elem φ₀ φ₁ τ) := by
  have hone : elem φ₀ φ₁ τ (1, 1, 0) = 1 := by
    change φ₀ 1 * φ₁ 1 * τ ^ 0 = 1
    rw [map_one, map_one, pow_zero, mul_one, mul_one]
  let K : Subgroup H :=
    { carrier := Set.range (elem φ₀ φ₁ τ)
      mul_mem' := by
        rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
        exact ⟨pairMul μ m m', (hM.elem_mul m m').symm⟩
      one_mem' := ⟨(1, 1, 0), hone⟩
      inv_mem' := by
        rintro _ ⟨⟨g, h, a⟩, rfl⟩
        have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
        rcases ha with rfl | rfl
        · refine ⟨(g⁻¹, h⁻¹, 0), eq_inv_of_mul_eq_one_right ?_⟩
          rw [hM.elem_mul]
          change elem φ₀ φ₁ τ (g * g⁻¹, h * h⁻¹, 0) = 1
          rw [mul_inv_cancel, mul_inv_cancel, hone]
        · refine ⟨(h⁻¹, g⁻¹ * DihedralGroup.r 2 ^ μ, 1), eq_inv_of_mul_eq_one_right ?_⟩
          rw [hM.elem_mul]
          change elem φ₀ φ₁ τ (g * (g⁻¹ * DihedralGroup.r 2 ^ μ) * DihedralGroup.r 2 ^ μ,
            h * h⁻¹, 0) = 1
          have hsq : g * (g⁻¹ * DihedralGroup.r 2 ^ μ) * DihedralGroup.r 2 ^ μ = 1 := by
            rw [mul_inv_cancel_left, ← pow_add, ← two_mul, pow_mul, r_two_sq, one_pow]
          rw [hsq, mul_inv_cancel, hone] }
  have hle : closure ((φ₀.range : Set H) ∪ φ₁.range ∪ {τ}) ≤ K := by
    rw [closure_le]
    rintro x ((⟨y, rfl⟩ | ⟨y, rfl⟩) | hx)
    · refine ⟨(y, 1, 0), ?_⟩
      change φ₀ y * φ₁ 1 * τ ^ 0 = φ₀ y
      rw [map_one, pow_zero, mul_one, mul_one]
    · refine ⟨(1, y, 0), ?_⟩
      change φ₀ 1 * φ₁ y * τ ^ 0 = φ₁ y
      rw [map_one, pow_zero, mul_one, one_mul]
    · refine ⟨(1, 1, 1), ?_⟩
      change φ₀ 1 * φ₁ 1 * τ ^ 1 = x
      rw [map_one, map_one, pow_one, one_mul, one_mul, Set.mem_singleton_iff.mp hx]
  rw [hM.gen] at hle
  intro x
  exact hle (mem_top x)

theorem card_fiber (hM : Model φ₀ φ₁ z τ μ) (x : H) :
    Nat.card {m : PairCoord // elem φ₀ φ₁ τ m = x} = 2 := by
  obtain ⟨m₀, rfl⟩ := hM.elem_surjective x
  obtain ⟨g₀, h₀, a₀⟩ := m₀
  have hset : {m : PairCoord | elem φ₀ φ₁ τ m = elem φ₀ φ₁ τ (g₀, h₀, a₀)} =
      {(g₀, h₀, a₀), (g₀ * DihedralGroup.r 2, h₀ * DihedralGroup.r 2, a₀)} := by
    ext ⟨g, h, a⟩
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [eq_comm, hM.elem_eq_iff]
    simp only [PairEquiv, Prod.mk.injEq]
    tauto
  have hne : ((g₀, h₀, a₀) : PairCoord) ≠
      (g₀ * DihedralGroup.r 2, h₀ * DihedralGroup.r 2, a₀) := by
    intro h
    apply r_two_ne_one
    have h1 : g₀ = g₀ * DihedralGroup.r 2 := congrArg Prod.fst h
    calc (DihedralGroup.r 2 : DihedralGroup 4) = g₀⁻¹ * (g₀ * DihedralGroup.r 2) := by group
      _ = 1 := by rw [← h1, inv_mul_cancel]
  change Nat.card ↥{m : PairCoord | elem φ₀ φ₁ τ m = elem φ₀ φ₁ τ (g₀, h₀, a₀)} = 2
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair hne]

theorem two_mul_card (hM : Model φ₀ φ₁ z τ μ) [Finite H] (Q : H → Prop) :
    2 * Nat.card {x : H // Q x} = Nat.card {m : PairCoord // Q (elem φ₀ φ₁ τ m)} := by
  classical
  have : Fintype H := Fintype.ofFinite H
  let e : {m : PairCoord // Q (elem φ₀ φ₁ τ m)} ≃
      Σ x : {x : H // Q x}, {m : PairCoord // elem φ₀ φ₁ τ m = x} :=
    { toFun := fun m => ⟨⟨elem φ₀ φ₁ τ m, m.2⟩, ⟨m.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      left_inv := fun m => rfl
      right_inv := by
        rintro ⟨⟨x, hx⟩, ⟨m, hm⟩⟩
        exact Sigma.subtype_ext (Subtype.ext hm) rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [card_fiber hM, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm, Nat.card_eq_fintype_card]

end Model

theorem klein_closure {G : Type*} [Group G] {z u : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : z * u = u * z) (hne : u ∉ zpowers z) :
    IsElementaryAbelian 2 (closure {z, u}) ∧ Nat.card (closure {z, u}) = 4 := by
  have hcomm : ∀ (x : zpowers z) (y : zpowers u),
      Commute ((zpowers z).subtype x) ((zpowers u).subtype y) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hzu i j)
  let φ := (zpowers z).subtype.noncommCoprod (zpowers u).subtype hcomm
  have hrange : φ.range = closure {z, u} := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype, Set.insert_eq,
      closure_union, zpowers_eq_closure, zpowers_eq_closure]
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨subtype_injective _, subtype_injective _, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨hxz, hxu⟩ := mem_inf.mp hx
    rcases mem_zpowers_eq_one_or_eq hu hxu with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (h ▸ hxz) hne
  have hcard : Nat.card (closure {z, u}) = 4 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, Nat.card_zpowers, hz, hu]
  have hle : closure {z, u} ≤ centralizer ((closure {z, u} : Subgroup G) : Set G) := by
    rw [centralizer_closure, closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hzu.symm
    · exact hzu
    · rfl
  have hcommK : ∀ x ∈ closure {z, u}, ∀ y ∈ closure {z, u}, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (hle hx) y hy).symm
  have hsq : ∀ x ∈ closure {z, u}, x ^ 2 = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · rw [← hz, pow_orderOf_eq_one]
      · rw [← hu, pow_orderOf_eq_one]
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hcommK a ha b hb) 2), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hcommInst : IsMulCommutative (closure {z, u}) :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hcommK _ a.2 _ b.2)
  refine ⟨@IsElementaryAbelian.mk 2 _ _ hcommInst ?_, hcard⟩
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro g
  exact Subtype.ext (by simpa using hsq g g.2)

end DihedralPair

open DihedralPair

theorem dihedral_pair_outer_centralizer_square_counts {P : Type*} [Group P] {r b : P}
    (hgen : closure {r, b} = ⊤) (hr : orderOf r = 4) (hb : orderOf b = 2)
    (hbr : b ∉ zpowers r) (hrel : b * r * b⁻¹ = r⁻¹)
    {H : Type*} [Group H] [Finite H] {z : H} (hzc : z ∈ center H)
    (φ₀ φ₁ : P →* H) (hφ₀ : Function.Injective φ₀) (hφ₁ : Function.Injective φ₁)
    (hζ₀ : φ₀ (r ^ 2) = z) (hζ₁ : φ₁ (r ^ 2) = z)
    (hint : φ₀.range ⊓ φ₁.range = zpowers z) (hcomm : ⁅φ₀.range, φ₁.range⁆ = ⊥)
    {μ : ℕ} (hμ : μ ≤ 1) {τ : H} (hτ2 : τ ^ 2 = z ^ μ)
    (hτ₀ : ∀ x : P, τ * φ₀ x * τ⁻¹ = φ₁ x) (hτ₁ : ∀ x : P, τ * φ₁ x * τ⁻¹ = φ₀ x)
    (hτP : τ ∉ (φ₀.range : Set H) * (φ₁.range : Set H))
    (hH : closure ((φ₀.range : Set H) ∪ φ₁.range ∪ {τ}) = ⊤)
    (u : H) (hu : u = φ₀ b * φ₁ b) (D : Subgroup H) (hD : D = centralizer {u}) :
    IsPGroup 2 H ∧ Nat.card H = 64 ∧
    IsElementaryAbelian 2 (closure {z, u}) ∧ Nat.card (closure {z, u}) = 4 ∧
    closure {z, u} ≤ D ∧ closure {z, u} ≤ centralizer (D : Set H) ∧
    Nat.card D = 32 ∧
    Nat.card {x : H // x ∈ D ∧ x ^ 2 = z} = 4 + 8 * μ ∧
    Nat.card {x : H // x ∈ D ∧ x ^ 2 = u} = 4 ∧
    Nat.card {x : H // x ∈ D ∧ x ^ 2 = z * u} = 4 ∧
    (μ = 1 → Nat.card {x : H // x ∈ D ∧ x ^ 2 = u} < Nat.card {x : H // x ∈ D ∧ x ^ 2 = z} ∧
      Nat.card {x : H // x ∈ D ∧ x ^ 2 = z * u} < Nat.card {x : H // x ∈ D ∧ x ^ 2 = z}) := by
  classical
  have hb' : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hb, pow_orderOf_eq_one]
  set f := dihedralFourHom hr hb' hrel with hfdef
  have hfinj := dihedralFourHom_injective hr hb' hrel hbr
  have hfsurj := dihedralFourHom_surjective hr hb' hrel hgen
  have hrange : ∀ φ : P →* H, (φ.comp f).range = φ.range := fun φ => by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hfsurj, ← MonoidHom.range_eq_map]
  have hf2 : f (DihedralGroup.r 2) = r ^ 2 := by
    rw [hfdef, dihedralFourHom_r, show (2 : ZMod 4).val = 2 from rfl, zpow_natCast]
  have hfb : f (DihedralGroup.sr 0) = b := by
    rw [hfdef, dihedralFourHom_sr, ZMod.val_zero, Nat.cast_zero, zpow_zero, mul_one]
  have hcommPP : ∀ x y : P, φ₁ y * φ₀ x = φ₀ x * φ₁ y := by
    intro x y
    have hle := commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact mem_centralizer_iff.mp (hle ⟨x, rfl⟩) (φ₁ y) ⟨y, rfl⟩
  have hM : Model (φ₀.comp f) (φ₁.comp f) z τ μ :=
    { inj₀ := hφ₀.comp hfinj
      inj₁ := hφ₁.comp hfinj
      zeta₀ := by rw [MonoidHom.comp_apply, hf2, hζ₀]
      zeta₁ := by rw [MonoidHom.comp_apply, hf2, hζ₁]
      central := hzc
      inter := by rw [hrange, hrange, hint]
      comm := fun x y => hcommPP (f x) (f y)
      sq := hτ2
      swap₀ := fun x => hτ₀ (f x)
      swap₁ := fun x => hτ₁ (f x)
      not_mem := by rw [hrange, hrange]; exact hτP
      gen := by rw [hrange, hrange]; exact hH }
  set ψ₀ := φ₀.comp f with hψ₀def
  set ψ₁ := φ₁.comp f with hψ₁def
  have hU : elem ψ₀ ψ₁ τ pairU = u := by
    rw [hu]
    change φ₀ (f (DihedralGroup.sr 0)) * φ₁ (f (DihedralGroup.sr 0)) * τ ^ 0 = _
    rw [hfb, pow_zero, mul_one]
  have hZ : elem ψ₀ ψ₁ τ pairZ = z := by
    change φ₀ (f (DihedralGroup.r 2)) * φ₁ (f 1) * τ ^ 0 = z
    rw [hf2, hζ₀, map_one, map_one, pow_zero, mul_one, mul_one]
  have hZU : elem ψ₀ ψ₁ τ pairZU = z * u := by
    change φ₀ (f (DihedralGroup.r 2 * DihedralGroup.sr 0)) * φ₁ (f (DihedralGroup.sr 0)) *
      τ ^ 0 = _
    rw [map_mul, hf2, hfb, map_mul, hζ₀, hu, pow_zero, mul_one, mul_assoc]
  have hone : elem ψ₀ ψ₁ τ (1, 1, 0) = 1 := by
    change φ₀ (f 1) * φ₁ (f 1) * τ ^ 0 = 1
    rw [map_one, map_one, map_one, pow_zero, mul_one, mul_one]
  have hmemD : ∀ m, elem ψ₀ ψ₁ τ m ∈ D ↔ PairInD μ m := by
    intro m
    rw [hD, mem_centralizer_singleton_iff, ← hU, hM.elem_mul, hM.elem_mul, eq_comm,
      hM.elem_eq_iff]
    rfl
  have hsq : ∀ m t, (elem ψ₀ ψ₁ τ m) ^ 2 = elem ψ₀ ψ₁ τ t ↔ PairEquiv (pairMul μ m m) t := by
    intro m t
    rw [pow_two, hM.elem_mul, hM.elem_eq_iff]
  have hcount : ∀ (Q : H → Prop) (p : PairCoord → Prop) [DecidablePred p],
      (∀ m, Q (elem ψ₀ ψ₁ τ m) ↔ p m) →
      2 * Nat.card {x : H // Q x} = (Finset.univ.filter p).card := by
    intro Q p _ hQ
    rw [hM.two_mul_card Q, Nat.card_congr (Equiv.subtypeEquivRight hQ),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardH : Nat.card H = 64 := by
    have h := hcount (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), Finset.filter_true,
      Finset.card_univ] at h
    have hM128 : Fintype.card PairCoord = 128 := by
      simp [Fintype.card_prod, DihedralGroup.card]
    omega
  have hcardD : 2 * Nat.card D = (Finset.univ.filter (fun m => PairInD μ m)).card :=
    hcount (· ∈ D) _ hmemD
  have hcz : 2 * Nat.card {x : H // x ∈ D ∧ x ^ 2 = z} =
      (Finset.univ.filter (fun m => PairInD μ m ∧ PairEquiv (pairMul μ m m) pairZ)).card :=
    hcount _ _ fun m => by rw [hmemD, ← hZ, hsq]
  have hcu : 2 * Nat.card {x : H // x ∈ D ∧ x ^ 2 = u} =
      (Finset.univ.filter (fun m => PairInD μ m ∧ PairEquiv (pairMul μ m m) pairU)).card :=
    hcount _ _ fun m => by rw [hmemD, ← hU, hsq]
  have hczu : 2 * Nat.card {x : H // x ∈ D ∧ x ^ 2 = z * u} =
      (Finset.univ.filter (fun m => PairInD μ m ∧ PairEquiv (pairMul μ m m) pairZU)).card :=
    hcount _ _ fun m => by rw [hmemD, ← hZU, hsq]
  have hcounts : Nat.card D = 32 ∧ Nat.card {x : H // x ∈ D ∧ x ^ 2 = z} = 4 + 8 * μ ∧
      Nat.card {x : H // x ∈ D ∧ x ^ 2 = u} = 4 ∧
      Nat.card {x : H // x ∈ D ∧ x ^ 2 = z * u} = 4 := by
    interval_cases μ
    · rw [card_pairInD_zero] at hcardD
      rw [card_pair_sq_z_zero] at hcz
      rw [card_pair_sq_u_zero] at hcu
      rw [card_pair_sq_zu_zero] at hczu
      omega
    · rw [card_pairInD_one] at hcardD
      rw [card_pair_sq_z_one] at hcz
      rw [card_pair_sq_u_one] at hcu
      rw [card_pair_sq_zu_one] at hczu
      omega
  have hzcomm : ∀ y : H, y * z = z * y := fun y => mem_center_iff.mp hzc y
  have hu1 : u ≠ 1 := by
    rw [← hU, ← hone, Ne, hM.elem_eq_iff]
    decide
  have huz : u ≠ z := by
    rw [← hU, ← hZ, Ne, hM.elem_eq_iff]
    decide
  have hu2 : u ^ 2 = 1 := by
    rw [← hU, ← hone, hsq]
    change PairEquiv (DihedralGroup.sr 0 * DihedralGroup.sr 0,
      DihedralGroup.sr 0 * DihedralGroup.sr 0, 0) (1, 1, 0)
    decide
  have horderU : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hune : u ∉ zpowers z := by
    intro h
    rcases mem_zpowers_eq_one_or_eq hM.orderOf_z h with h1 | h1
    · exact hu1 h1
    · exact huz h1
  obtain ⟨hklein, hcard4⟩ := klein_closure hM.orderOf_z horderU (hzcomm u).symm hune
  have hzD : z ∈ D := by
    rw [hD, mem_centralizer_singleton_iff]
    exact (hzcomm u).symm
  have huD : u ∈ D := by
    rw [hD, mem_centralizer_singleton_iff]
  have hleD : closure {z, u} ≤ D := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact hzD
    · exact huD
  have hleC : closure {z, u} ≤ centralizer (D : Set H) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, mem_centralizer_iff]
      intro d _
      exact hzcomm d
    · rw [SetLike.mem_coe, mem_centralizer_iff]
      intro d hd
      rw [SetLike.mem_coe, hD, mem_centralizer_singleton_iff] at hd
      exact hd
  obtain ⟨hD32, hz', hu', hzu'⟩ := hcounts
  refine ⟨IsPGroup.of_card (n := 6) (by rw [hcardH]; norm_num), hcardH, hklein, hcard4, hleD,
    hleC, hD32, hz', hu', hzu', ?_⟩
  intro h1
  rw [hz', hu', hzu', h1]
  omega

end CFSG.ComponentClassification.UnbalancedGS
