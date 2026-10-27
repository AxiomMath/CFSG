module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open Subgroup

theorem linodd_mem_map_conj_iff {G : Type*} [Group G] {H : Subgroup G} {j x : G} :
    x ∈ H.map (MulAut.conj j).toMonoidHom ↔ j⁻¹ * x * j ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨j⁻¹ * x * j, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem linodd_mem_normalizer_of_map_eq {G : Type*} [Group G] {n : G} {A : Subgroup G}
    (h : A.map (MulAut.conj n).toMonoidHom = A) : n ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : n * x * n⁻¹ ∈ A.map (MulAut.conj n).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by simpa [MulAut.conj_apply] using hyx
    rwa [← this]

theorem linodd_map_conj_mul {G : Type*} [Group G] (b t : G) (A : Subgroup G) :
    A.map (MulAut.conj (b * t)).toMonoidHom =
      (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem linodd_mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup A B (Subgroup.mem_inf.2 ⟨hA, hB⟩)

theorem linodd_mem_normalizer_D {G : Type*} [Group G] {D X L : Subgroup G} (hDL : D ≤ L)
    (hXL : X ≤ L) (hLD : L ≤ normalizer (D : Set G)) {d : G} (hd : d ∈ D) :
    d ∈ normalizer ((D ⊔ X : Subgroup G) : Set G) := by
  have key : ∀ e ∈ D, ∀ h ∈ D ⊔ X, e * h * e⁻¹ ∈ D ⊔ X := by
    intro e he
    have hle : D ⊔ X ≤ (D ⊔ X).comap (MulAut.conj e).toMonoidHom := by
      apply sup_le
      · intro d' hd'
        rw [Subgroup.mem_comap]
        show e * d' * e⁻¹ ∈ D ⊔ X
        exact Subgroup.mem_sup_left ((mem_normalizer_iff.1 (hLD (hDL he)) d').1 hd')
      · intro x hx
        rw [Subgroup.mem_comap]
        show e * x * e⁻¹ ∈ D ⊔ X
        have h1 : x * e⁻¹ * x⁻¹ ∈ D := (mem_normalizer_iff.1 (hLD (hXL hx)) e⁻¹).1 (inv_mem he)
        have e2 : e * x * e⁻¹ = (e * (x * e⁻¹ * x⁻¹)) * x := by group
        rw [e2]
        exact mul_mem (Subgroup.mem_sup_left (mul_mem he h1)) (Subgroup.mem_sup_right hx)
    intro h hh
    exact hle hh
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact key d hd h
  · intro hh
    have h2 := key d⁻¹ (inv_mem hd) _ hh
    have e : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := by group
    rwa [e] at h2

theorem linodd_le_normalizer_of_comm {G : Type*} [Group G] {X Y : Subgroup G}
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, y * x = x * y) : Y ≤ normalizer (X : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : y * h * y⁻¹ = h := by
      rw [hcomm h hh y hy]
      group
    rw [e]
    exact hh
  · intro hh
    have hc := hcomm _ hh y hy
    have e2 : y⁻¹ * (y * h * y⁻¹) * y = y * h * y⁻¹ := by
      calc y⁻¹ * (y * h * y⁻¹) * y = y⁻¹ * ((y * h * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * h * y⁻¹)) := by rw [hc]
        _ = y * h * y⁻¹ := by group
    have key : y⁻¹ * (y * h * y⁻¹) * y ∈ X := by
      rw [e2]
      exact hh
    have e : y⁻¹ * (y * h * y⁻¹) * y = h := by group
    rwa [e] at key

theorem linodd_mem_sup_decomp {G : Type*} [Group G] {A K : Subgroup G}
    (hK : K ≤ normalizer (A : Set G)) {g : G} (hg : g ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ k ∈ K, a * k = g := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left A K hK
  have hg' : g ∈ ((A ⊔ K : Subgroup G) : Set G) := hg
  rw [h] at hg'
  exact Set.mem_mul.1 hg'

theorem linodd_dec_of_le {G : Type*} [Group G] {L D X Y : Subgroup G}
    (hLeq : L = D ⊔ (X ⊔ Y)) (hK : X ⊔ Y ≤ normalizer (D : Set G))
    (hY : Y ≤ normalizer (X : Set G)) :
    ∀ g ∈ L, ∃ d ∈ D, ∃ x ∈ X, ∃ y ∈ Y, d * x * y = g := by
  intro g hg
  rw [hLeq] at hg
  obtain ⟨d, hd, k, hk, rfl⟩ := linodd_mem_sup_decomp hK hg
  obtain ⟨x, hx, y, hy, rfl⟩ := linodd_mem_sup_decomp hY hk
  exact ⟨d, hd, x, hx, y, hy, mul_assoc d x y⟩

theorem linodd_eq_one_of_mem_inter {G : Type*} [Group G] {D X Y : Subgroup G}
    (hDXY : D ⊓ (X ⊔ Y) = ⊥) (hXYbot : X ⊓ Y = ⊥) (hXD : X ≤ normalizer (D : Set G)) {y : G}
    (hyN : y ∈ D ⊔ X) (hyY : y ∈ Y) : y = 1 := by
  obtain ⟨d, hd, x, hx, rfl⟩ := linodd_mem_sup_decomp hXD hyN
  have hdm : d ∈ X ⊔ Y := by
    have e : d = (d * x) * x⁻¹ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hyY) (Subgroup.mem_sup_left (inv_mem hx))
  have hd1 : d = 1 := by
    have hmem : d ∈ D ⊓ (X ⊔ Y) := ⟨hd, hdm⟩
    rw [hDXY, Subgroup.mem_bot] at hmem
    exact hmem
  have hx1 : x ∈ X ⊓ Y := by
    refine ⟨hx, ?_⟩
    rw [hd1, one_mul] at hyY
    exact hyY
  rw [hXYbot, Subgroup.mem_bot] at hx1
  rw [hd1, hx1, mul_one]

theorem linodd_conj_mem {G : Type*} [Group G] {j : G} {S : Subgroup G}
    (hj : j ∈ normalizer (S : Set G)) {s : G} (hs : s ∈ S) : j * s * j⁻¹ ∈ S :=
  (mem_normalizer_iff.1 hj s).1 hs

theorem linodd_conj_inv_mem {G : Type*} [Group G] {j : G} {S : Subgroup G}
    (hj : j ∈ normalizer (S : Set G)) {s : G} (hs : s ∈ S) : j⁻¹ * s * j ∈ S := by
  have h := (mem_normalizer_iff.1 (inv_mem hj) s).1 hs
  rwa [inv_inv] at h

theorem linodd_bot_or_le {G : Type*} [Group G] {X H : Subgroup G} (hXs : IsSimpleGroup X)
    (hXH : X ≤ normalizer (H : Set G)) : (∀ x ∈ X, x ∈ H → x = 1) ∨ X ≤ H := by
  have hnorm : (H.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (hXH g.2) (n : G)).1 hn
    simpa using this
  rcases Subgroup.Normal.eq_bot_or_eq_top (H.subgroupOf X) with h | h
  · left
    intro x hx hxH
    have hmem : (⟨x, hx⟩ : X) ∈ H.subgroupOf X := Subgroup.mem_subgroupOf.2 hxH
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · right
    intro x hx
    have hmem : (⟨x, hx⟩ : X) ∈ H.subgroupOf X := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

theorem linodd_eq_one_of_central {G : Type*} [Group G] {X : Subgroup G} (hXs : IsSimpleGroup X)
    (hXn : ∃ a b : X, a * b ≠ b * a) {x : G} (hx : x ∈ X)
    (hc : ∀ x' ∈ X, x' * x = x * x') : x = 1 := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
  · have hmem : (⟨x, hx⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g.1 g.2)
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := hXn
    apply hab
    have ha : a ∈ Subgroup.center X := by
      rw [h]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem linodd_le_D_of_bot {G : Type*} [Group G] {L D X Y H : Subgroup G}
    (hXs : IsSimpleGroup X) (hXn : ∃ a b : X, a * b ≠ b * a)
    (hdec : ∀ g ∈ L, ∃ d ∈ D, ∃ x ∈ X, ∃ y ∈ Y, d * x * y = g)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, y * x = x * y) (hXL : X ≤ L) (hHL : H ≤ L) (hDH : D ≤ H)
    (hLH : L ≤ normalizer (H : Set G)) (hXb : ∀ x ∈ X, x ∈ H → x = 1)
    (hYb : ∀ y ∈ Y, y ∈ H → y = 1) : H ≤ D := by
  intro h hh
  obtain ⟨d, hd, x, hx, y, hy, rfl⟩ := hdec h (hHL hh)
  have hk : x * y ∈ H := by
    have h1 : d⁻¹ * (d * x * y) ∈ H := mul_mem (hDH (inv_mem hd)) hh
    have e : d⁻¹ * (d * x * y) = x * y := by group
    rwa [e] at h1
  have hcx : ∀ x' ∈ X, x' * x = x * x' := by
    intro x' hx'
    have hkH : x' * (x * y) * x'⁻¹ ∈ H :=
      (mem_normalizer_iff.1 (hLH (hXL hx')) (x * y)).1 hk
    have hc : x' * (x * y) * x'⁻¹ * (x * y)⁻¹ ∈ H := mul_mem hkH (inv_mem hk)
    have hyx' : y * x'⁻¹ = x'⁻¹ * y := by
      have h2 := hcomm x' hx' y hy
      calc y * x'⁻¹ = x'⁻¹ * (x' * y) * x'⁻¹ := by group
        _ = x'⁻¹ * (y * x') * x'⁻¹ := by rw [h2]
        _ = x'⁻¹ * y := by group
    have e : x' * (x * y) * x'⁻¹ * (x * y)⁻¹ = x' * x * x'⁻¹ * x⁻¹ := by
      calc x' * (x * y) * x'⁻¹ * (x * y)⁻¹ = x' * x * (y * x'⁻¹) * y⁻¹ * x⁻¹ := by group
        _ = x' * x * (x'⁻¹ * y) * y⁻¹ * x⁻¹ := by rw [hyx']
        _ = x' * x * x'⁻¹ * x⁻¹ := by group
    have hcX : x' * x * x'⁻¹ * x⁻¹ ∈ X :=
      mul_mem (mul_mem (mul_mem hx' hx) (inv_mem hx')) (inv_mem hx)
    have h1 : x' * x * x'⁻¹ * x⁻¹ = 1 := hXb _ hcX (by rw [← e]; exact hc)
    calc x' * x = (x' * x * x'⁻¹ * x⁻¹) * x * x' := by group
      _ = x * x' := by rw [h1, one_mul]
  have hx1 : x = 1 := linodd_eq_one_of_central hXs hXn hx hcx
  have hy' : y ∈ H := by
    have h3 := hk
    rwa [hx1, one_mul] at h3
  have hy1 : y = 1 := hYb y hy hy'
  rw [hx1, hy1, mul_one, mul_one]
  exact hd

theorem linodd_le_sup_right_of_bot {G : Type*} [Group G] {L D X Y H : Subgroup G}
    (hdec : ∀ g ∈ L, ∃ d ∈ D, ∃ x ∈ X, ∃ y ∈ Y, d * x * y = g) (hHL : H ≤ L) (hDH : D ≤ H)
    (hYH : Y ≤ H) (hXb : ∀ x ∈ X, x ∈ H → x = 1) : H ≤ D ⊔ Y := by
  intro h hh
  obtain ⟨d, hd, x, hx, y, hy, rfl⟩ := hdec h (hHL hh)
  have hx1 : x = 1 := by
    apply hXb x hx
    have h1 : d⁻¹ * (d * x * y) * y⁻¹ ∈ H :=
      mul_mem (mul_mem (hDH (inv_mem hd)) hh) (inv_mem (hYH hy))
    have e : d⁻¹ * (d * x * y) * y⁻¹ = x := by group
    rwa [e] at h1
  rw [hx1, mul_one]
  exact mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hy)

theorem linodd_le_sup_left_of_bot {G : Type*} [Group G] {L D X Y H : Subgroup G}
    (hdec : ∀ g ∈ L, ∃ d ∈ D, ∃ x ∈ X, ∃ y ∈ Y, d * x * y = g) (hHL : H ≤ L) (hDH : D ≤ H)
    (hXH : X ≤ H) (hYb : ∀ y ∈ Y, y ∈ H → y = 1) : H ≤ D ⊔ X := by
  intro h hh
  obtain ⟨d, hd, x, hx, y, hy, rfl⟩ := hdec h (hHL hh)
  have hy1 : y = 1 := by
    apply hYb y hy
    have h1 : x⁻¹ * (d⁻¹ * (d * x * y)) ∈ H :=
      mul_mem (inv_mem (hXH hx)) (mul_mem (hDH (inv_mem hd)) hh)
    have e : x⁻¹ * (d⁻¹ * (d * x * y)) = y := by group
    rwa [e] at h1
  rw [hy1, mul_one]
  exact mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hx)

theorem linodd_core {G : Type*} [Group G] {L D X Y : Subgroup G}
    (hDL : D ≤ L) (hLD : L ≤ normalizer (D : Set G)) (hXL : X ≤ L) (hYL : Y ≤ L)
    (hLeq : L = D ⊔ (X ⊔ Y)) (hDXY : D ⊓ (X ⊔ Y) = ⊥)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, y * x = x * y) (hXYbot : X ⊓ Y = ⊥)
    (hXs : IsSimpleGroup X) (hXn : ∃ a b : X, a * b ≠ b * a)
    (hYs : IsSimpleGroup Y) (hYn : ∃ a b : Y, a * b ≠ b * a)
    {j : G} (hjL : j ∈ normalizer (L : Set G)) (hjD : j ∈ normalizer (D : Set G))
    {H : Subgroup G} (hH : ∀ x : G, x ∈ H ↔ j⁻¹ * x * j ∈ D ⊔ X) :
    H = D ⊔ X ∨ H = D ⊔ Y := by
  have hXD : X ≤ normalizer (D : Set G) := fun x hx => hLD (hXL hx)
  have hYD : Y ≤ normalizer (D : Set G) := fun y hy => hLD (hYL hy)
  have hYX : Y ≤ normalizer (X : Set G) := linodd_le_normalizer_of_comm hcomm
  have hdec := linodd_dec_of_le hLeq (sup_le hXD hYD) hYX
  have hDN : D ≤ normalizer ((D ⊔ X : Subgroup G) : Set G) := fun d hd =>
    linodd_mem_normalizer_D hDL hXL hLD hd
  have hXN : X ≤ normalizer ((D ⊔ X : Subgroup G) : Set G) := fun x hx =>
    linodd_mem_normalizer_sup (hXD hx) (le_normalizer hx)
  have hYN : Y ≤ normalizer ((D ⊔ X : Subgroup G) : Set G) := fun y hy =>
    linodd_mem_normalizer_sup (hYD hy) (hYX hy)
  have hLN : L ≤ normalizer ((D ⊔ X : Subgroup G) : Set G) := by
    rw [hLeq]
    exact sup_le hDN (sup_le hXN hYN)
  have hHL : H ≤ L := by
    intro h hh
    have h1 := (hH h).1 hh
    have h2 := linodd_conj_mem hjL ((sup_le hDL hXL) h1)
    have e : j * (j⁻¹ * h * j) * j⁻¹ = h := by group
    rwa [e] at h2
  have hDH : D ≤ H := by
    intro d hd
    refine (hH d).2 (Subgroup.mem_sup_left ?_)
    exact linodd_conj_inv_mem hjD hd
  have hLH : L ≤ normalizer (H : Set G) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro h
    have hk : j⁻¹ * l * j ∈ normalizer ((D ⊔ X : Subgroup G) : Set G) :=
      hLN (linodd_conj_inv_mem hjL hl)
    rw [hH, hH]
    have e : (j⁻¹ * l * j) * (j⁻¹ * h * j) * (j⁻¹ * l * j)⁻¹ = j⁻¹ * (l * h * l⁻¹) * j := by
      group
    have h3 := mem_normalizer_iff.1 hk (j⁻¹ * h * j)
    rw [e] at h3
    exact h3
  have hXH : X ≤ normalizer (H : Set G) := fun x hx => hLH (hXL hx)
  have hYH : Y ≤ normalizer (H : Set G) := fun y hy => hLH (hYL hy)
  rcases linodd_bot_or_le hXs hXH with hXb | hXle
  · rcases linodd_bot_or_le hYs hYH with hYb | hYle
    · exfalso
      have hHD : H ≤ D := linodd_le_D_of_bot hXs hXn hdec hcomm hXL hHL hDH hLH hXb hYb
      have hX1 : ∀ x ∈ X, x = 1 := by
        intro x hx
        have hxH : j * x * j⁻¹ ∈ H := by
          rw [hH]
          have e : j⁻¹ * (j * x * j⁻¹) * j = x := by group
          rw [e]
          exact Subgroup.mem_sup_right hx
        have hxD : x ∈ D := by
          have h3 := linodd_conj_inv_mem hjD (hHD hxH)
          have e : j⁻¹ * (j * x * j⁻¹) * j = x := by group
          rwa [e] at h3
        have hmem : x ∈ D ⊓ (X ⊔ Y) := ⟨hxD, Subgroup.mem_sup_left hx⟩
        rw [hDXY, Subgroup.mem_bot] at hmem
        exact hmem
      obtain ⟨a, b, hab⟩ := hXn
      apply hab
      exact Subtype.ext (by simp [hX1 _ a.2, hX1 _ b.2])
    · right
      apply le_antisymm
      · exact linodd_le_sup_right_of_bot hdec hHL hDH hYle hXb
      · exact sup_le hDH hYle
  · rcases linodd_bot_or_le hYs hYH with hYb | hYle
    · left
      apply le_antisymm
      · exact linodd_le_sup_left_of_bot hdec hHL hDH hXle hYb
      · exact sup_le hDH hXle
    · exfalso
      have hLH' : L ≤ H := by
        rw [hLeq]
        exact sup_le hDH (sup_le hXle hYle)
      obtain ⟨a, b, hab⟩ := hYn
      have hY1 : ∀ y ∈ Y, y = 1 := by
        intro y hy
        have h1 := (hH (j * y * j⁻¹)).1 (hLH' (linodd_conj_mem hjL (hYL hy)))
        have e : j⁻¹ * (j * y * j⁻¹) * j = y := by group
        rw [e] at h1
        exact linodd_eq_one_of_mem_inter hDXY hXYbot hXD h1 hy
      apply hab
      exact Subtype.ext (by simp [hY1 _ a.2, hY1 _ b.2])

theorem normalizer_sup_of_odd {G : Type*} [Group G] [Finite G] {L D X Y : Subgroup G}
    (hDL : D ≤ L) (hLD : L ≤ Subgroup.normalizer (D : Set G)) (hXL : X ≤ L) (hYL : Y ≤ L)
    (hLeq : L = D ⊔ (X ⊔ Y)) (hDXY : D ⊓ (X ⊔ Y) = ⊥)
    (hXY : X ≤ Subgroup.centralizer (Y : Set G)) (hXYbot : X ⊓ Y = ⊥)
    (hXs : IsSimpleGroup X) (hXn : ∃ a b : X, a * b ≠ b * a)
    (hYs : IsSimpleGroup Y) (hYn : ∃ a b : Y, a * b ≠ b * a) (hne : D ⊔ X ≠ D ⊔ Y)
    {j : G} (hjL : j ∈ Subgroup.normalizer (L : Set G))
    (hjD : j ∈ Subgroup.normalizer (D : Set G)) (hjodd : Odd (orderOf j)) :
    j ∈ Subgroup.normalizer ((D ⊔ X : Subgroup G) : Set G) := by
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, y * x = x * y := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hXY hx) y hy
  have hcomm' : ∀ x ∈ Y, ∀ y ∈ X, y * x = x * y := fun x hx y hy =>
    (hcomm y hy x hx).symm
  have h1 := linodd_core hDL hLD hXL hYL hLeq hDXY hcomm hXYbot hXs hXn hYs hYn hjL hjD
    (H := (D ⊔ X : Subgroup G).map (MulAut.conj j).toMonoidHom)
    (fun x => linodd_mem_map_conj_iff)
  have h2 := linodd_core hDL hLD hYL hXL (by rw [hLeq, sup_comm Y X])
    (by rw [sup_comm Y X]; exact hDXY) hcomm' (by rw [inf_comm]; exact hXYbot) hYs hYn hXs hXn
    hjL hjD (H := (D ⊔ Y : Subgroup G).map (MulAut.conj j).toMonoidHom)
    (fun x => linodd_mem_map_conj_iff)
  have hinj : Function.Injective (Subgroup.map (MulAut.conj j).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj j).injective
  have hsq : ((D ⊔ X : Subgroup G).map (MulAut.conj j).toMonoidHom).map
      (MulAut.conj j).toMonoidHom = D ⊔ X := by
    rcases h1 with h1 | h1
    · rw [h1, h1]
    · rcases h2 with h2 | h2
      · exfalso
        apply hne
        apply hinj
        rw [h1, h2]
      · rw [h1, h2]
  have hjj : j * j ∈ Subgroup.normalizer ((D ⊔ X : Subgroup G) : Set G) := by
    apply linodd_mem_normalizer_of_map_eq
    rw [linodd_map_conj_mul j j, hsq]
  obtain ⟨m, hm⟩ := hjodd
  have hpow : j ^ (2 * (m + 1)) = j := by
    rw [show 2 * (m + 1) = orderOf j + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have hjm : (j * j) ^ (m + 1) = j := by
    calc (j * j) ^ (m + 1) = j ^ (2 * (m + 1)) := by rw [pow_mul, sq]
      _ = j := hpow
  have hfin := pow_mem hjj (m + 1)
  rwa [hjm] at hfin

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
