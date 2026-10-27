module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylDefs
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

namespace ShapeModel

open Subgroup

section Cyclic

variable {G : Type*} [Group G]

def cycHom (m : ℕ) (g : G) (hg : g ^ m = 1) : Multiplicative (ZMod m) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift m ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      have h0 : Additive.ofMul (g ^ m) = (0 : Additive G) := by rw [hg]; rfl
      simpa [ofMul_pow] using h0⟩)

theorem exists_intCast (m : ℕ) (z : Multiplicative (ZMod m)) :
    ∃ k : ℤ, z = Multiplicative.ofAdd (k : ZMod m) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  exact ⟨k, by rw [hk]; rfl⟩

theorem cycHom_intCast (m : ℕ) (g : G) (hg : g ^ m = 1) (k : ℤ) :
    cycHom m g hg (Multiplicative.ofAdd (k : ZMod m)) = g ^ k := by
  simp [cycHom]

theorem cycHom_ofAdd_one (m : ℕ) (g : G) (hg : g ^ m = 1) :
    cycHom m g hg (Multiplicative.ofAdd 1) = g := by
  simpa using cycHom_intCast m g hg 1

theorem cycHom_range (m : ℕ) (g : G) (hg : g ^ m = 1) :
    (cycHom m g hg).range = zpowers g := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨k, rfl⟩ := exists_intCast m z
    rw [cycHom_intCast]
    exact Subgroup.zpow_mem _ (mem_zpowers g) k
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ⟨Multiplicative.ofAdd (k : ZMod m), cycHom_intCast m g hg k⟩

theorem cycHom_injective (m : ℕ) (g : G) (hg : g ^ m = 1) (hord : orderOf g = m) :
    Function.Injective (cycHom m g hg) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨k, rfl⟩ := exists_intCast m z
  rw [cycHom_intCast] at hz
  have hdvd : (m : ℤ) ∣ k := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hz
    rwa [hord] at this
  have hk : (k : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd k m).2 hdvd
  rw [hk]
  rfl

end Cyclic

section Model

abbrev ShapeN (n : ℕ) := Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))

abbrev ShapeH := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

@[expose] def swapAut (n : ℕ) : MulAut (ShapeN n) := MulEquiv.prodComm

@[expose] def invAut (n : ℕ) : MulAut (ShapeN n) := MulEquiv.inv _

theorem swapAut_apply (n : ℕ) (x : ShapeN n) : swapAut n x = x.swap := rfl

theorem invAut_apply (n : ℕ) (x : ShapeN n) : invAut n x = x⁻¹ := rfl

theorem swapAut_sq (n : ℕ) : swapAut n ^ 2 = 1 := by
  refine MulEquiv.ext fun x => ?_
  simp [pow_two, swapAut_apply]

theorem invAut_sq (n : ℕ) : invAut n ^ 2 = 1 := by
  refine MulEquiv.ext fun x => ?_
  simp [invAut_apply, pow_two]

theorem swapAut_comm_invAut (n : ℕ) : Commute (swapAut n) (invAut n) := by
  refine MulEquiv.ext fun x => ?_
  simp [swapAut_apply, invAut_apply]

def shapeAct (n : ℕ) : ShapeH →* MulAut (ShapeN n) :=
  MonoidHom.noncommCoprod (cycHom 2 (swapAut n) (swapAut_sq n)) (cycHom 2 (invAut n) (invAut_sq n))
    (by
      intro x y
      obtain ⟨k, rfl⟩ := exists_intCast 2 x
      obtain ⟨l, rfl⟩ := exists_intCast 2 y
      rw [cycHom_intCast, cycHom_intCast]
      exact (swapAut_comm_invAut n).zpow_zpow k l)

abbrev ShapeGrp (n : ℕ) := ShapeN n ⋊[shapeAct n] ShapeH

theorem card_shapeGrp (n : ℕ) : Nat.card (ShapeGrp n) = 2 ^ (2 * n + 2) := by
  rw [SemidirectProduct.card, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  ring

end Model

section Lift

variable {X : Type*} [Group X] {n : ℕ} {a b t y : X}

structure ShapeData (n : ℕ) (a b t y : X) : Prop where
  a_pow : a ^ 2 ^ n = 1
  b_pow : b ^ 2 ^ n = 1
  ab : Commute a b
  t_sq : t ^ 2 = 1
  y_sq : y ^ 2 = 1
  ty : Commute t y
  tab : t * a * t⁻¹ = b
  tba : t * b * t⁻¹ = a
  ya : y * a * y⁻¹ = a⁻¹
  yb : y * b * y⁻¹ = b⁻¹

@[expose] def ShapeData.fN (hD : ShapeData n a b t y) : ShapeN n →* X :=
  (cycHom _ a hD.a_pow).noncommCoprod (cycHom _ b hD.b_pow) (by
    intro x z
    obtain ⟨k, rfl⟩ := exists_intCast _ x
    obtain ⟨l, rfl⟩ := exists_intCast _ z
    rw [cycHom_intCast, cycHom_intCast]
    exact hD.ab.zpow_zpow k l)

def ShapeData.fH (hD : ShapeData n a b t y) : ShapeH →* X :=
  (cycHom 2 t hD.t_sq).noncommCoprod (cycHom 2 y hD.y_sq) (by
    intro x z
    obtain ⟨k, rfl⟩ := exists_intCast _ x
    obtain ⟨l, rfl⟩ := exists_intCast _ z
    rw [cycHom_intCast, cycHom_intCast]
    exact hD.ty.zpow_zpow k l)

theorem ShapeData.fN_apply (hD : ShapeData n a b t y) (x : ShapeN n) :
    hD.fN x = cycHom _ a hD.a_pow x.1 * cycHom _ b hD.b_pow x.2 := rfl

theorem ShapeData.commute_fa_fb (hD : ShapeData n a b t y) (x z : Multiplicative (ZMod (2 ^ n))) :
    Commute (cycHom _ a hD.a_pow x) (cycHom _ b hD.b_pow z) := by
  obtain ⟨k, rfl⟩ := exists_intCast _ x
  obtain ⟨l, rfl⟩ := exists_intCast _ z
  rw [cycHom_intCast, cycHom_intCast]
  exact hD.ab.zpow_zpow k l

theorem ShapeData.conj_fa (hD : ShapeData n a b t y) (z : Multiplicative (ZMod (2 ^ n))) :
    t * cycHom _ a hD.a_pow z * t⁻¹ = cycHom _ b hD.b_pow z := by
  obtain ⟨k, rfl⟩ := exists_intCast _ z
  rw [cycHom_intCast, cycHom_intCast, ← hD.tab]
  exact conj_zpow.symm

theorem ShapeData.conj_fb (hD : ShapeData n a b t y) (z : Multiplicative (ZMod (2 ^ n))) :
    t * cycHom _ b hD.b_pow z * t⁻¹ = cycHom _ a hD.a_pow z := by
  obtain ⟨k, rfl⟩ := exists_intCast _ z
  rw [cycHom_intCast, cycHom_intCast, ← hD.tba]
  exact conj_zpow.symm

theorem ShapeData.inv_fa (hD : ShapeData n a b t y) (z : Multiplicative (ZMod (2 ^ n))) :
    y * cycHom _ a hD.a_pow z * y⁻¹ = (cycHom _ a hD.a_pow z)⁻¹ := by
  obtain ⟨k, rfl⟩ := exists_intCast _ z
  rw [cycHom_intCast]
  calc y * a ^ k * y⁻¹ = (y * a * y⁻¹) ^ k := conj_zpow.symm
    _ = (a ^ k)⁻¹ := by rw [hD.ya, inv_zpow]

theorem ShapeData.inv_fb (hD : ShapeData n a b t y) (z : Multiplicative (ZMod (2 ^ n))) :
    y * cycHom _ b hD.b_pow z * y⁻¹ = (cycHom _ b hD.b_pow z)⁻¹ := by
  obtain ⟨k, rfl⟩ := exists_intCast _ z
  rw [cycHom_intCast]
  calc y * b ^ k * y⁻¹ = (y * b * y⁻¹) ^ k := conj_zpow.symm
    _ = (b ^ k)⁻¹ := by rw [hD.yb, inv_zpow]

theorem ShapeData.fN_swap (hD : ShapeData n a b t y) (x : ShapeN n) :
    hD.fN (swapAut n x) = t * hD.fN x * t⁻¹ := by
  obtain ⟨u, v⟩ := x
  rw [swapAut_apply, Prod.swap_prod_mk, fN_apply, fN_apply]
  dsimp only
  calc cycHom _ a hD.a_pow v * cycHom _ b hD.b_pow u
      = cycHom _ b hD.b_pow u * cycHom _ a hD.a_pow v := (hD.commute_fa_fb v u).eq
    _ = (t * cycHom _ a hD.a_pow u * t⁻¹) * (t * cycHom _ b hD.b_pow v * t⁻¹) := by
      rw [hD.conj_fa, hD.conj_fb]
    _ = t * (cycHom _ a hD.a_pow u * cycHom _ b hD.b_pow v) * t⁻¹ := by
      simp [mul_assoc]

theorem ShapeData.fN_inv (hD : ShapeData n a b t y) (x : ShapeN n) :
    hD.fN (invAut n x) = y * hD.fN x * y⁻¹ := by
  obtain ⟨u, v⟩ := x
  rw [invAut_apply, Prod.inv_mk, fN_apply, fN_apply]
  dsimp only
  calc cycHom _ a hD.a_pow u⁻¹ * cycHom _ b hD.b_pow v⁻¹
      = (y * cycHom _ a hD.a_pow u * y⁻¹) * (y * cycHom _ b hD.b_pow v * y⁻¹) := by
        rw [hD.inv_fa, hD.inv_fb, map_inv, map_inv]
    _ = y * (cycHom _ a hD.a_pow u * cycHom _ b hD.b_pow v) * y⁻¹ := by
      simp [mul_assoc]

theorem ShapeData.compat (hD : ShapeData n a b t y) (g : ShapeH) :
    hD.fN.comp (shapeAct n g).toMonoidHom =
      (MulAut.conj (hD.fH g)).toMonoidHom.comp hD.fN := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨e, f⟩ := g
  have hE : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
  rcases hE e with rfl | rfl <;> rcases hE f with rfl | rfl
  · simp [shapeAct, ShapeData.fH]
  · simp [shapeAct, ShapeData.fH, cycHom_ofAdd_one, fN_inv]
  · simp [shapeAct, ShapeData.fH, cycHom_ofAdd_one, fN_swap]
  · simp [shapeAct, ShapeData.fH, cycHom_ofAdd_one, fN_swap, fN_inv, mul_assoc]

@[expose] def ShapeData.lift (hD : ShapeData n a b t y) : ShapeGrp n →* X :=
  SemidirectProduct.lift hD.fN hD.fH hD.compat

theorem ShapeData.lift_apply (hD : ShapeData n a b t y) (x : ShapeN n) (h : ShapeH) :
    hD.lift ⟨x, h⟩ = hD.fN x * hD.fH h := rfl

theorem ShapeData.fN_range (hD : ShapeData n a b t y) :
    hD.fN.range = zpowers a ⊔ zpowers b := by
  rw [ShapeData.fN, MonoidHom.noncommCoprod_range, cycHom_range, cycHom_range]

theorem ShapeData.fH_range (hD : ShapeData n a b t y) :
    hD.fH.range = zpowers t ⊔ zpowers y := by
  rw [ShapeData.fH, MonoidHom.noncommCoprod_range, cycHom_range, cycHom_range]

theorem ShapeData.fN_injective (hD : ShapeData n a b t y) (ha : orderOf a = 2 ^ n)
    (hb : orderOf b = 2 ^ n) (hdisj : Disjoint (zpowers a) (zpowers b)) :
    Function.Injective hD.fN := by
  rw [ShapeData.fN, MonoidHom.noncommCoprod_injective]
  refine ⟨cycHom_injective _ _ _ ha, cycHom_injective _ _ _ hb, ?_⟩
  rwa [cycHom_range, cycHom_range]

theorem ShapeData.fH_injective (hD : ShapeData n a b t y) (ht : orderOf t = 2)
    (hy : orderOf y = 2) (hdisj : Disjoint (zpowers t) (zpowers y)) :
    Function.Injective hD.fH := by
  rw [ShapeData.fH, MonoidHom.noncommCoprod_injective]
  refine ⟨cycHom_injective _ _ _ ht, cycHom_injective _ _ _ hy, ?_⟩
  rwa [cycHom_range, cycHom_range]

theorem ShapeData.lift_injective (hD : ShapeData n a b t y) (hN : Function.Injective hD.fN)
    (hH : Function.Injective hD.fH) (hdisj : Disjoint hD.fN.range hD.fH.range) :
    Function.Injective hD.lift := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, h⟩ hxh
  rw [lift_apply] at hxh
  have h1 : hD.fN x = (hD.fH h)⁻¹ := eq_inv_of_mul_eq_one_left hxh
  have hmem : hD.fN x ∈ hD.fN.range ⊓ hD.fH.range :=
    ⟨⟨x, rfl⟩, by rw [h1]; exact Subgroup.inv_mem _ (MonoidHom.mem_range.2 ⟨h, rfl⟩)⟩
  rw [disjoint_iff.1 hdisj] at hmem
  have h2 : hD.fN x = 1 := mem_bot.1 hmem
  rw [h2, one_mul] at hxh
  have hx : x = 1 := hN (by rw [h2, map_one])
  have hh : h = 1 := hH (by rw [hxh, map_one])
  subst hx
  subst hh
  rfl

theorem ShapeData.lift_range (hD : ShapeData n a b t y) :
    hD.lift.range = hD.fN.range ⊔ hD.fH.range := by
  apply le_antisymm
  · rintro _ ⟨⟨x, h⟩, rfl⟩
    rw [lift_apply]
    exact mul_mem (mem_sup_left ⟨x, rfl⟩) (mem_sup_right ⟨h, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨SemidirectProduct.inl x, SemidirectProduct.lift_inl _ _ _ _⟩
    · rintro _ ⟨h, rfl⟩
      exact ⟨SemidirectProduct.inr h, SemidirectProduct.lift_inr _ _ _ _⟩

end Lift

section Main

variable {X : Type*} [Group X]

theorem zpow_eq_one_or_self {t : X} (htt : t * t = 1) (i : ℤ) : t ^ i = 1 ∨ t ^ i = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htt
  have h : t ^ i = t ^ (i % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one i with h0 | h1
  · left
    rw [h, h0, zpow_zero]
  · right
    rw [h, h1, zpow_one]

theorem disjoint_zpowers_of_sq {t y : X} (htt : t * t = 1) (hyy : y * y = 1) (ht1 : t ≠ 1)
    (hty : t ≠ y) : Disjoint (zpowers t) (zpowers y) := by
  rw [disjoint_iff, eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hz1
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hz2
  rcases zpow_eq_one_or_self htt i with h1 | h1
  · exact mem_bot.2 h1
  · exfalso
    rcases zpow_eq_one_or_self hyy j with h2 | h2
    · exact ht1 (by rw [← h1, ← hj, h2])
    · exact hty (by rw [← h1, ← hj, h2])

end Main

end ShapeModel

open ShapeModel Subgroup

section Main

variable {X : Type*} [Group X] {S A : Subgroup X} {a t y : X} {n : ℕ}

theorem ShapeConds.nonempty_mulEquiv_shapeGrp (h : ShapeConds S A a t y n) :
    Nonempty (ShapeGrp n ≃* ↥S) := by
  obtain ⟨ha, hA, hab, hcomm, htt, hyy, hty, ht1, hy1, hty', hAty, hyA, hS⟩ := h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hsemi : SemiconjBy t⁻¹ a (t⁻¹ * a * t) := (mul_inv_cancel_right (t⁻¹ * a) t).symm
  have hb_ord : orderOf (t⁻¹ * a * t) = 2 ^ n := by rw [← hsemi.orderOf_eq, ha]
  have ha_mem : a ∈ A := by
    rw [hA]
    exact mem_sup_left (mem_zpowers a)
  have hb_mem : t⁻¹ * a * t ∈ A := by
    rw [hA]
    exact mem_sup_right (mem_zpowers _)
  have hD : ShapeData n a (t⁻¹ * a * t) t y :=
    { a_pow := by rw [← ha]; exact pow_orderOf_eq_one a
      b_pow := by rw [← hb_ord]; exact pow_orderOf_eq_one _
      ab := hcomm
      t_sq := by rw [pow_two]; exact htt
      y_sq := by rw [pow_two]; exact hyy
      ty := hty
      tab := by rw [hti]
      tba := by simp [mul_assoc]
      ya := by rw [hyi]; exact hyA a ha_mem
      yb := by rw [hyi]; exact hyA _ hb_mem }
  have hN : Function.Injective hD.fN :=
    hD.fN_injective ha hb_ord (disjoint_iff.2 hab)
  have hH : Function.Injective hD.fH :=
    hD.fH_injective (orderOf_eq_prime (by rw [pow_two]; exact htt) ht1)
      (orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1)
      (disjoint_zpowers_of_sq htt hyy ht1 hty')
  have hdisj : Disjoint hD.fN.range hD.fH.range := by
    rw [hD.fN_range, hD.fH_range, ← hA]
    exact disjoint_iff.2 hAty
  have hrange : hD.lift.range = S := by
    rw [hD.lift_range, hD.fN_range, hD.fH_range, ← hA, hS, sup_assoc]
  exact ⟨(MonoidHom.ofInjective (hD.lift_injective hN hH hdisj)).trans
    (MulEquiv.subgroupCongr hrange)⟩

theorem ShapeConds.card_eq (h : ShapeConds S A a t y n) : Nat.card ↥S = 2 ^ (2 * n + 2) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_shapeGrp
  rw [← Nat.card_congr e.toEquiv, card_shapeGrp]

end Main

theorem shapeConds_mulEquiv {X Y : Type*} [Group X] [Group Y] {S A : Subgroup X} {a t y : X}
    {S' A' : Subgroup Y} {a' t' y' : Y} {n : ℕ}
    (h : ShapeConds S A a t y n) (h' : ShapeConds S' A' a' t' y' n) :
    Nonempty (↥S ≃* ↥S') := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_shapeGrp
  obtain ⟨e'⟩ := h'.nonempty_mulEquiv_shapeGrp
  exact ⟨e.symm.trans e'⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
