module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

section TypeFree

variable {G : Type} [Group G]

theorem sup_inf_eq_of_le_of_sup_eq {W Y X D : Subgroup G} (hWY : W ≤ Y) (hYX : Y ≤ X)
    (hDN : D ≤ normalizer (W : Set G)) (hWD : W ⊔ D = X) : W ⊔ (Y ⊓ D) = Y := by
  refine le_antisymm (sup_le hWY inf_le_left) fun y hy => ?_
  have hyX : y ∈ ((W ⊔ D : Subgroup G) : Set G) := by
    rw [hWD]
    exact hYX hy
  rw [coe_mul_of_right_le_normalizer_left W D hDN] at hyX
  obtain ⟨w, hw, d, hd, rfl⟩ := hyX
  have hdY : d ∈ Y := by
    have h1 : d = w⁻¹ * (w * d) := by group
    rw [h1]
    exact mul_mem (inv_mem (hWY hw)) hy
  exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_inf.2 ⟨hdY, hd⟩))

theorem inv_eq_self_of_forall_mul_self {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {a : G}
    (ha : a ∈ W) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (hW2 a ha)

theorem mul_comm_of_mem_of_exponent_two {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {a b : G}
    (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a :=
  calc a * b = (a * b)⁻¹ := (inv_eq_self_of_forall_mul_self hW2 (mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
      rw [inv_eq_self_of_forall_mul_self hW2 hb, inv_eq_self_of_forall_mul_self hW2 ha]

@[expose] def wTraceHom {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {t : G}
    (htN : t ∈ normalizer (W : Set G)) : W →* W where
  toFun u := ⟨t * u * t⁻¹ * u, mul_mem ((mem_normalizer_iff.1 htN u).1 u.2) u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by
    have hcomm : t * (v : G) * t⁻¹ * u = u * (t * v * t⁻¹) :=
      mul_comm_of_mem_of_exponent_two hW2 ((mem_normalizer_iff.1 htN v).1 v.2) u.2
    change t * ((u : G) * v) * t⁻¹ * (u * v) = t * u * t⁻¹ * u * (t * v * t⁻¹ * v)
    calc t * ((u : G) * v) * t⁻¹ * (u * v) = t * u * t⁻¹ * (t * v * t⁻¹ * u) * v := by group
      _ = t * u * t⁻¹ * (u * (t * v * t⁻¹)) * v := by rw [hcomm]
      _ = t * u * t⁻¹ * u * (t * v * t⁻¹ * v) := by group)

theorem coe_wTraceHom {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {t : G}
    (htN : t ∈ normalizer (W : Set G)) (u : W) :
    ((wTraceHom hW2 htN u : W) : G) = t * u * t⁻¹ * u :=
  rfl

theorem exists_conj_mul_eq_of_card_eq_sq [Finite G] {W : Subgroup G}
    (hW2 : ∀ w ∈ W, w * w = 1) {t : G} (ht2 : t * t = 1) (htN : t ∈ normalizer (W : Set G))
    (hcard : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {w : G} (hw : w ∈ W ⊓ centralizer ({t} : Set G)) : ∃ u ∈ W, t * u * t⁻¹ * u = w := by
  set f := wTraceHom hW2 htN with hf
  set V := W ⊓ centralizer ({t} : Set G) with hV
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hker : f.ker = V.subgroupOf W := by
    ext u
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    have hu := u.2
    constructor
    · intro h
      have h' : t * (u : G) * t⁻¹ * u = 1 := congrArg Subtype.val h
      refine ⟨hu, ?_⟩
      have h2 : t * (u : G) * t⁻¹ = u := by
        calc t * (u : G) * t⁻¹ = (t * u * t⁻¹ * u) * (u : G)⁻¹ := by group
          _ = u := by rw [h', one_mul, inv_eq_self_of_forall_mul_self hW2 hu]
      calc (u : G) * t = t * u * t⁻¹ * t := by rw [h2]
        _ = t * u := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      change t * (u : G) * t⁻¹ * u = 1
      calc t * (u : G) * t⁻¹ * u = u * t * t⁻¹ * u := by rw [← h]
        _ = u * u := by group
        _ = 1 := hW2 _ hu
  have hrange : f.range ≤ V.subgroupOf W := by
    rintro _ ⟨u, rfl⟩
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    refine ⟨(f u).2, ?_⟩
    rw [hf, coe_wTraceHom]
    have hcomm := mul_comm_of_mem_of_exponent_two hW2 ((mem_normalizer_iff.1 htN u).1 u.2) u.2
    calc t * (u : G) * t⁻¹ * u * t = (u * (t * u * t⁻¹)) * t := by rw [hcomm]
      _ = u * t * u := by group
      _ = t * t * u * t⁻¹ * u := by rw [ht2, htinv]; group
      _ = t * (t * u * t⁻¹ * u) := by group
  have hVW : V ≤ W := inf_le_left
  have hcardV : Nat.card (V.subgroupOf W) = Nat.card V :=
    Nat.card_congr (subgroupOfEquivOfLe hVW).toEquiv
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, hcardV] at h1
  have hpos : 0 < Nat.card V := Nat.card_pos
  have hrc : Nat.card f.range = Nat.card V := by
    rw [hcard, sq] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have heq : f.range = V.subgroupOf W :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardV, hrc])
  have hwW : (⟨w, (mem_inf.1 hw).1⟩ : W) ∈ f.range := by
    rw [heq, mem_subgroupOf]
    exact hw
  obtain ⟨u, hu⟩ := hwW
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem exists_complement_of_complement_sup_zpowers [Finite G] {W S D : Subgroup G} {t : G}
    (hW2 : ∀ w ∈ W, w * w = 1) (ht2 : t * t = 1) (hWS : W ≤ S)
    (hSN : S ≤ normalizer (W : Set G)) (htW : t ∈ normalizer (W : Set G))
    (htS : t ∈ normalizer (S : Set G))
    (hcard : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hWD : W ⊓ D = ⊥) (hsup : W ⊔ D = S ⊔ zpowers t) :
    ∃ C : Subgroup G, C ≤ S ∧ C ⊓ W = ⊥ ∧ W ⊔ C = S ∧ t ∈ normalizer (C : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hXN : S ⊔ zpowers t ≤ normalizer (W : Set G) := sup_le hSN (zpowers_le.2 htW)
  have hDX : D ≤ S ⊔ zpowers t := by
    rw [← hsup]
    exact le_sup_right
  have hDN : D ≤ normalizer (W : Set G) := hDX.trans hXN
  have htX : t ∈ ((W ⊔ D : Subgroup G) : Set G) := by
    rw [hsup]
    exact mem_sup_right (mem_zpowers t)
  rw [coe_mul_of_right_le_normalizer_left W D hDN] at htX
  obtain ⟨w₀, hw₀, d, hd, hwd⟩ := htX
  have hd' : d = w₀⁻¹ * t := by
    rw [← hwd]
    group
  have hddW : d * d ∈ W := by
    have h1 : d * d = w₀⁻¹ * (t * w₀⁻¹ * t⁻¹) * (t * t) := by
      rw [hd']
      group
    rw [h1, ht2, mul_one]
    exact mul_mem (inv_mem hw₀) ((mem_normalizer_iff.1 htW _).1 (inv_mem hw₀))
  have hdd : d * d = 1 := by
    have h := mem_inf.2 ⟨hddW, mul_mem hd hd⟩
    rw [hWD, mem_bot] at h
    exact h
  have hw₀inv : w₀⁻¹ = w₀ := inv_eq_self_of_forall_mul_self hW2 hw₀
  have hw₀t : w₀ * t = t * w₀ := by
    have h1 : w₀ * t * (w₀ * t) = 1 := by rw [← hdd, hd', hw₀inv]
    calc w₀ * t = (w₀ * t * (w₀ * t)) * t⁻¹ * w₀⁻¹ := by group
      _ = t * w₀ := by
        rw [h1, htinv, hw₀inv]
        group
  obtain ⟨u, huW, hu⟩ := exists_conj_mul_eq_of_card_eq_sq hW2 ht2 htW hcard
    (mem_inf.2 ⟨hw₀, mem_centralizer_singleton_iff.2 hw₀t⟩)
  have hcomm := mul_comm_of_mem_of_exponent_two hW2 ((mem_normalizer_iff.1 htW u).1 huW) huW
  have huinv : u⁻¹ = u := inv_eq_self_of_forall_mul_self hW2 huW
  have hdu : d = u * t * u⁻¹ := by
    calc d = w₀⁻¹ * t := hd'
      _ = (t * u * t⁻¹ * u) * t := by rw [hw₀inv, hu]
      _ = (u * (t * u * t⁻¹)) * t := by rw [hcomm]
      _ = u * t * u * (t⁻¹ * t) := by group
      _ = u * t * u⁻¹ := by rw [inv_mul_cancel, mul_one, huinv]
  set D' := D.map (MulAut.conj u⁻¹).toMonoidHom with hD'
  have hmemD' : ∀ y, y ∈ D' ↔ ∃ x ∈ D, u⁻¹ * x * u = y := by
    intro y
    rw [hD', mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have htD' : t ∈ D' := (hmemD' t).2 ⟨d, hd, by rw [hdu]; group⟩
  have huX : u ∈ S ⊔ zpowers t := mem_sup_left (hWS huW)
  have hWD' : W ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyW, hyD⟩ := mem_inf.1 hy
    obtain ⟨x, hx, rfl⟩ := (hmemD' y).1 hyD
    have hxW : x ∈ W := by
      have h1 : x = u * (u⁻¹ * x * u) * u⁻¹ := by group
      rw [h1]
      exact mul_mem (mul_mem huW hyW) (inv_mem huW)
    have hx1 : x = 1 := by
      have h := mem_inf.2 ⟨hxW, hx⟩
      rw [hWD, mem_bot] at h
      exact h
    rw [mem_bot, hx1]
    group
  have hsup' : W ⊔ D' = S ⊔ zpowers t := by
    apply le_antisymm
    · refine sup_le (hWS.trans le_sup_left) fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := (hmemD' y).1 hy
      exact mul_mem (mul_mem (inv_mem huX) (hDX hx)) huX
    · intro y hy
      have hy' : u * y * u⁻¹ ∈ ((W ⊔ D : Subgroup G) : Set G) := by
        rw [hsup]
        exact mul_mem (mul_mem huX hy) (inv_mem huX)
      rw [coe_mul_of_right_le_normalizer_left W D hDN] at hy'
      obtain ⟨w, hw, x, hx, hwx⟩ := hy'
      have hwx' : w * x = u * y * u⁻¹ := hwx
      have h1 : y = (u⁻¹ * w * u) * (u⁻¹ * x * u) := by
        calc y = u⁻¹ * (u * y * u⁻¹) * u := by group
          _ = u⁻¹ * (w * x) * u := by rw [hwx']
          _ = (u⁻¹ * w * u) * (u⁻¹ * x * u) := by group
      rw [h1]
      exact mul_mem (mem_sup_left (mul_mem (mul_mem (inv_mem huW) hw) huW))
        (mem_sup_right ((hmemD' _).2 ⟨x, hx, rfl⟩))
  have hD'N : D' ≤ normalizer (W : Set G) := by
    refine le_trans ?_ hXN
    rw [← hsup']
    exact le_sup_right
  refine ⟨S ⊓ D', inf_le_left, ?_, sup_inf_eq_of_le_of_sup_eq hWS le_sup_left hD'N hsup', ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    have h := mem_inf.2 ⟨(mem_inf.1 hy).2, (mem_inf.1 (mem_inf.1 hy).1).2⟩
    rw [hWD'] at h
    exact h
  · exact mem_normalizer_inf_of_mem_normalizer htS (le_normalizer htD')

end TypeFree

end CFSG.SeitzReduction.LinearPilot
