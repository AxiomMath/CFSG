module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G] {W : Subgroup G} {t : G}

theorem mul_comm_of_forall_mul_self_eq_one (hW : ∀ w ∈ W, w * w = 1) {v w : G} (hv : v ∈ W)
    (hw : w ∈ W) : v * w = w * v := by
  have h1 : (v * w)⁻¹ = v * w := inv_eq_of_mul_eq_one_right (hW _ (W.mul_mem hv hw))
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hW v hv)
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW w hw)
  rw [← h1, mul_inv_rev, hv', hw']

theorem tcomm_mem (htW : t ∈ normalizer (W : Set G)) {w : G} (hw : w ∈ W) :
    t * w * t⁻¹ * w⁻¹ ∈ W :=
  W.mul_mem ((mem_normalizer_iff.1 htW w).1 hw) (W.inv_mem hw)

theorem tcomm_mul (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (htW : t ∈ normalizer (W : Set G))
    {v w : G} (hv : v ∈ W) (hw : w ∈ W) :
    t * (v * w) * t⁻¹ * (v * w)⁻¹ = (t * v * t⁻¹ * v⁻¹) * (t * w * t⁻¹ * w⁻¹) := by
  have h1 : v⁻¹ * (t * w * t⁻¹) = (t * w * t⁻¹) * v⁻¹ :=
    hWc _ (W.inv_mem hv) _ ((mem_normalizer_iff.1 htW w).1 hw)
  have h2 : w⁻¹ * v⁻¹ = v⁻¹ * w⁻¹ := hWc _ (W.inv_mem hw) _ (W.inv_mem hv)
  calc t * (v * w) * t⁻¹ * (v * w)⁻¹ = (t * v * t⁻¹) * (t * w * t⁻¹) * (w⁻¹ * v⁻¹) := by group
    _ = (t * v * t⁻¹) * (t * w * t⁻¹) * (v⁻¹ * w⁻¹) := by rw [h2]
    _ = (t * v * t⁻¹) * ((t * w * t⁻¹) * v⁻¹) * w⁻¹ := by group
    _ = (t * v * t⁻¹) * (v⁻¹ * (t * w * t⁻¹)) * w⁻¹ := by rw [h1]
    _ = (t * v * t⁻¹ * v⁻¹) * (t * w * t⁻¹ * w⁻¹) := by group

theorem tcomm_eq_one_iff {w : G} :
    t * w * t⁻¹ * w⁻¹ = 1 ↔ w ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc w * t = (t * w * t⁻¹ * w⁻¹)⁻¹ * (t * w) := by group
      _ = t * w := by rw [h, inv_one, one_mul]
  · intro h
    rw [← h]
    group

theorem tcomm_conj_of_commute {x : G} (hxt : x * t = t * x) (w : G) :
    t * (x * w * x⁻¹) * t⁻¹ * (x * w * x⁻¹)⁻¹ = x * (t * w * t⁻¹ * w⁻¹) * x⁻¹ := by
  have ht' : t = x * t * x⁻¹ := by rw [hxt, mul_inv_cancel_right]
  conv_lhs => rw [ht']
  group

theorem tcomm_mem_centralizer (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) {w : G} (hw : w ∈ W) :
    t * w * t⁻¹ * w⁻¹ ∈ centralizer ({t} : Set G) := by
  have hc2 : (t * w * t⁻¹ * w⁻¹)⁻¹ = t * w * t⁻¹ * w⁻¹ :=
    inv_eq_of_mul_eq_one_right (hW _ (tcomm_mem htW hw))
  have hcinv : t * w * t⁻¹ * w⁻¹ = w * t * w⁻¹ * t⁻¹ := by
    rw [← hc2]
    group
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [mem_centralizer_singleton_iff]
  calc (t * w * t⁻¹ * w⁻¹) * t = (w * t * w⁻¹ * t⁻¹) * t := by rw [hcinv]
    _ = w * t * w⁻¹ := by group
    _ = w * t⁻¹ * w⁻¹ := by rw [ht']
    _ = (t * t) * w * t⁻¹ * w⁻¹ := by rw [ht, one_mul]
    _ = t * (t * w * t⁻¹ * w⁻¹) := by group

theorem exists_tcomm_eq_of_pow_three (hW : ∀ w ∈ W, w * w = 1)
    (htW : t ∈ normalizer (W : Set G)) {x : G} (hxW : x ∈ normalizer (W : Set G))
    (hxt : x * t = t * x) (hx3 : x ^ 3 = 1) {w : G} (hw : w ∈ W)
    (hvx : t * w * t⁻¹ * w⁻¹ ∈ centralizer ({x} : Set G)) :
    ∃ w' ∈ W ⊓ centralizer ({x} : Set G), t * w' * t⁻¹ * w'⁻¹ = t * w * t⁻¹ * w⁻¹ := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hw₁ : x * w * x⁻¹ ∈ W := (mem_normalizer_iff.1 hxW w).1 hw
  have hw₂ : x * (x * w * x⁻¹) * x⁻¹ ∈ W := (mem_normalizer_iff.1 hxW _).1 hw₁
  have hx3' : x * x * x = 1 := by rw [← pow_three', hx3]
  have h3 : x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = w := by
    calc x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * w * (x * x * x)⁻¹ := by group
      _ = w := by rw [hx3', one_mul, inv_one, mul_one]
  have hc : x * (t * w * t⁻¹ * w⁻¹) * x⁻¹ = t * w * t⁻¹ * w⁻¹ := by
    rw [mem_centralizer_singleton_iff] at hvx
    rw [← hvx, mul_inv_cancel_right]
  have hc₁ : t * (x * w * x⁻¹) * t⁻¹ * (x * w * x⁻¹)⁻¹ = t * w * t⁻¹ * w⁻¹ := by
    rw [tcomm_conj_of_commute hxt, hc]
  have hc₂ : t * (x * (x * w * x⁻¹) * x⁻¹) * t⁻¹ * (x * (x * w * x⁻¹) * x⁻¹)⁻¹ =
      t * w * t⁻¹ * w⁻¹ := by
    rw [tcomm_conj_of_commute hxt, hc₁, hc]
  refine ⟨w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹),
    Subgroup.mem_inf.2 ⟨W.mul_mem (W.mul_mem hw hw₁) hw₂, ?_⟩, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    have hconj : x * (w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) * x⁻¹ =
        w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) := by
      calc x * (w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) * x⁻¹ =
          (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) * (x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹) := by
            group
        _ = (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) * w := by rw [h3]
        _ = w * ((x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) :=
            (hWc w hw _ (W.mul_mem hw₁ hw₂)).symm
        _ = w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) := by group
    calc w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) * x =
        (x * (w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) * x⁻¹) * x := by rw [hconj]
      _ = x * (w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹)) := by group
  · have hcc : (t * w * t⁻¹ * w⁻¹) * (t * w * t⁻¹ * w⁻¹) = 1 := hW _ (tcomm_mem htW hw)
    rw [tcomm_mul hWc htW (W.mul_mem hw hw₁) hw₂, tcomm_mul hWc htW hw hw₁, hc₁, hc₂, hcc,
      one_mul]

theorem tcomm_mem_centralizer_of_commute {x : G} (hxt : x * t = t * x) {w : G}
    (hwx : w ∈ centralizer ({x} : Set G)) :
    t * w * t⁻¹ * w⁻¹ ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hwx ⊢
  have hw : x * w * x⁻¹ = w := by rw [← hwx, mul_inv_cancel_right]
  have h := tcomm_conj_of_commute hxt w
  rw [hw] at h
  calc t * w * t⁻¹ * w⁻¹ * x = (x * (t * w * t⁻¹ * w⁻¹) * x⁻¹) * x := by rw [← h]
    _ = x * (t * w * t⁻¹ * w⁻¹) := by group

@[expose] def tcommHom (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (htW : t ∈ normalizer (W : Set G)) {A B : Subgroup G} (hAW : A ≤ W)
    (hAB : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ B) : A →* B where
  toFun a := ⟨t * a * t⁻¹ * (a : G)⁻¹, hAB a a.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    exact tcomm_mul hWc htW (hAW a.2) (hAW b.2)

theorem coe_tcommHom_apply (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (htW : t ∈ normalizer (W : Set G)) {A B : Subgroup G} (hAW : A ≤ W)
    (hAB : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ B) (a : A) :
    ((tcommHom hWc htW hAW hAB a : B) : G) = t * a * t⁻¹ * (a : G)⁻¹ :=
  rfl

theorem card_ker_tcommHom (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (htW : t ∈ normalizer (W : Set G)) {A B C : Subgroup G} (hAW : A ≤ W)
    (hAB : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ B) (hCA : C ≤ A)
    (hC : ∀ a ∈ A, a ∈ C ↔ a ∈ centralizer ({t} : Set G)) :
    Nat.card (tcommHom hWc htW hAW hAB).ker = Nat.card C := by
  have hker : (tcommHom hWc htW hAW hAB).ker = C.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf, hC a a.2, ← tcomm_eq_one_iff, Subtype.ext_iff,
      coe_tcommHom_apply]
    rfl
  rw [hker]
  exact Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv

theorem tcomm_surjective_of_card [Finite G] (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G))
    (hcard : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2) :
    ∀ v ∈ W ⊓ centralizer ({t} : Set G), ∃ w ∈ W, t * w * t⁻¹ * w⁻¹ = v := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hAB : ∀ a ∈ W, t * a * t⁻¹ * a⁻¹ ∈ W ⊓ centralizer ({t} : Set G) := fun a ha =>
    Subgroup.mem_inf.2 ⟨tcomm_mem htW ha, tcomm_mem_centralizer hW ht htW ha⟩
  set φ := tcommHom hWc htW le_rfl hAB with hφ
  have hker : Nat.card φ.ker = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    card_ker_tcommHom hWc htW le_rfl hAB inf_le_left fun a _ =>
      ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨‹_›, h⟩⟩
  have hW' := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hcard, sq] at hW'
  have hpos : 0 < Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) := Nat.card_pos
  have hrange : Nat.card φ.range = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    (Nat.eq_of_mul_eq_mul_right hpos hW').symm
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hrange
  intro v hv
  obtain ⟨a, ha⟩ := (MonoidHom.range_eq_top.1 htop) ⟨v, hv⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

theorem card_inf_centralizer_eq_sq [Finite G] (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G))
    (hsurj : ∀ v ∈ W ⊓ centralizer ({t} : Set G), ∃ w ∈ W, t * w * t⁻¹ * w⁻¹ = v) {x : G}
    (hxW : x ∈ normalizer (W : Set G)) (hxt : x * t = t * x) (hx3 : x ^ 3 = 1) :
    Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hAB : ∀ a ∈ W ⊓ centralizer ({x} : Set G), t * a * t⁻¹ * a⁻¹ ∈
      W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) := fun a ha =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨tcomm_mem htW (Subgroup.mem_inf.1 ha).1,
      tcomm_mem_centralizer hW ht htW (Subgroup.mem_inf.1 ha).1⟩,
      tcomm_mem_centralizer_of_commute hxt (Subgroup.mem_inf.1 ha).2⟩
  set φ := tcommHom hWc htW inf_le_left hAB with hφ
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨⟨hvW, hvt⟩, hvx⟩ := hv
    obtain ⟨w, hw, hwv⟩ := hsurj v (Subgroup.mem_inf.2 ⟨hvW, hvt⟩)
    obtain ⟨w', hw', hw'v⟩ := exists_tcomm_eq_of_pow_three hW htW hxW hxt hx3 hw (hwv ▸ hvx)
    exact ⟨⟨w', hw'⟩, Subtype.ext (hw'v.trans hwv)⟩
  have hker : Nat.card φ.ker =
      Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    refine card_ker_tcommHom hWc htW inf_le_left hAB
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) fun a ha => ?_
    obtain ⟨haW, hax⟩ := Subgroup.mem_inf.1 ha
    exact ⟨fun h => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h).1).2,
      fun h => Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨haW, h⟩, hax⟩⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurjφ).toEquiv, hker, sq]

theorem inf_centralizer_inf_eq_bot (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) {x y : G} (hxt : x * t = t * x) (hyt : y * t = t * y)
    (h : W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) ⊓
      centralizer ({y} : Set G) = ⊥) :
    W ⊓ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwWx, hwy⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨hwW, hwx⟩ := Subgroup.mem_inf.1 hwWx
  have hc : t * w * t⁻¹ * w⁻¹ ∈ W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) ⊓
      centralizer ({y} : Set G) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨tcomm_mem htW hwW,
      tcomm_mem_centralizer hW ht htW hwW⟩, tcomm_mem_centralizer_of_commute hxt hwx⟩,
      tcomm_mem_centralizer_of_commute hyt hwy⟩
  rw [h, Subgroup.mem_bot] at hc
  have hwt := tcomm_eq_one_iff.1 hc
  have hw' : w ∈ W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) ⊓
      centralizer ({y} : Set G) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hwW, hwt⟩, hwx⟩, hwy⟩
  rwa [h] at hw'

theorem exists_commutator_eq_of_inf_centralizer_eq_bot [Finite G]
    (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) {y : G} (hyW : y ∈ normalizer (W : Set G))
    (h : W ⊓ centralizer ({y} : Set G) = ⊥) {w : G} (hw : w ∈ W) :
    ∃ w' ∈ W, w' * y * w'⁻¹ * y⁻¹ = w := by
  have hmem : ∀ u ∈ W, u * y * u⁻¹ * y⁻¹ ∈ W := fun u hu => by
    have : y * u⁻¹ * y⁻¹ ∈ W := (mem_normalizer_iff.1 hyW _).1 (W.inv_mem hu)
    have h2 := W.mul_mem hu this
    rwa [show u * (y * u⁻¹ * y⁻¹) = u * y * u⁻¹ * y⁻¹ by group] at h2
  let f : W →* W :=
    { toFun := fun u => ⟨u * y * (u : G)⁻¹ * y⁻¹, hmem u u.2⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by
        ext
        simp only [Subgroup.coe_mul]
        have ha : y * (u : G)⁻¹ * y⁻¹ ∈ W := (mem_normalizer_iff.1 hyW _).1 (W.inv_mem u.2)
        have hb : y * (v : G)⁻¹ * y⁻¹ ∈ W := (mem_normalizer_iff.1 hyW _).1 (W.inv_mem v.2)
        have h1 : (y * (u : G)⁻¹ * y⁻¹) * ((v : G) * (y * (v : G)⁻¹ * y⁻¹)) =
            ((v : G) * (y * (v : G)⁻¹ * y⁻¹)) * (y * (u : G)⁻¹ * y⁻¹) :=
          hWc _ ha _ (W.mul_mem v.2 hb)
        calc (u : G) * v * y * ((u : G) * v)⁻¹ * y⁻¹ =
            (u : G) * ((v : G) * (y * (v : G)⁻¹ * y⁻¹)) * (y * (u : G)⁻¹ * y⁻¹) := by group
          _ = (u : G) * ((y * (u : G)⁻¹ * y⁻¹) * ((v : G) * (y * (v : G)⁻¹ * y⁻¹))) := by
            rw [h1]; group
          _ = (u : G) * y * (u : G)⁻¹ * y⁻¹ * ((v : G) * y * (v : G)⁻¹ * y⁻¹) := by group }
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hu1 : (u : G) * y * (u : G)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hu
    have huy : (u : G) ∈ W ⊓ centralizer ({y} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨u.2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      calc (u : G) * y = ((u : G) * y * (u : G)⁻¹ * y⁻¹) * (y * u) := by group
        _ = y * u := by rw [hu1, one_mul]
    rw [h, Subgroup.mem_bot] at huy
    exact (Subgroup.mem_bot).2 (Subtype.ext huy)
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨w, hw⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem exists_conj_eq_of_mul_self_eq_one (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (hsurj : ∀ v ∈ W ⊓ centralizer ({t} : Set G), ∃ w ∈ W, t * w * t⁻¹ * w⁻¹ = v) {w : G}
    (hw : w ∈ W) (h : w * t * (w * t) = 1) : ∃ u ∈ W, w * t = u * t * u⁻¹ := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW w hw)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hwt : w ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w * t = (w * t)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
      _ = t⁻¹ * w⁻¹ := mul_inv_rev w t
      _ = t * w := by rw [ht', hw']
  obtain ⟨u, hu, huw⟩ := hsurj w (Subgroup.mem_inf.2 ⟨hw, hwt⟩)
  refine ⟨u, hu, ?_⟩
  calc w * t = w⁻¹ * t := by rw [hw']
    _ = (t * u * t⁻¹ * u⁻¹)⁻¹ * t := by rw [huw]
    _ = u * t * u⁻¹ := by group

end CFSG.SeitzReduction.LinearPilot
