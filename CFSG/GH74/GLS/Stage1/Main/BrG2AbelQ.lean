module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

open QuaternionGroup

namespace CFSG.GH74.GLS.Stage1.Main

section QG

variable {m : ℕ}

theorem abq_m_add_m : ((m : ℕ) : ZMod (2 * m)) + (m : ℕ) = 0 := by
  have : ((m + m : ℕ) : ZMod (2 * m)) = 0 := by
    have e : m + m = 2 * m := by omega
    rw [e]
    exact ZMod.natCast_self (2 * m)
  push_cast at this
  exact this

theorem abq_a_comm_xa {i j : ZMod (2 * m)} (h : a j * xa i = xa i * a j) : j + j = 0 := by
  have h' : (xa (i - j) : QuaternionGroup m) = xa (i + j) := h
  have h2 := xa.inj h'
  linear_combination -h2

theorem abq_comm_a_xa (i j : ZMod (2 * m)) :
    (xa i * a j)⁻¹ * (a j * xa i) = a (-(j + j)) := by
  have h1 : (xa i * a j : QuaternionGroup m)⁻¹ = xa ((m : ZMod (2 * m)) + (i + j)) := by
    rw [xa_mul_a]; rfl
  rw [h1, a_mul_xa, xa_mul_xa]
  congr 1
  ring

theorem abq_quad_cases [NeZero m] {m' : ℕ} (hm' : m = m' + m') {j : ZMod (2 * m)}
    (h : (j + j) + (j + j) = 0) :
    j = 0 ∨ j = (m : ZMod (2 * m)) ∨ j = (m' : ZMod (2 * m)) ∨
      j = (m' : ZMod (2 * m)) + (m : ZMod (2 * m)) := by
  have hcast : ((m : ℕ) : ZMod (2 * m)) = (m' : ZMod (2 * m)) + (m' : ZMod (2 * m)) := by
    have := congrArg (Nat.cast : ℕ → ZMod (2 * m)) hm'
    push_cast at this
    exact this
  rcases (Thm3.Sec8.Basic.two_mul_eq_zero_iff (j + j)).1 h with h0 | h0
  · rcases (Thm3.Sec8.Basic.two_mul_eq_zero_iff j).1 h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have h1 : (j - (m' : ZMod (2 * m))) + (j - (m' : ZMod (2 * m))) = 0 := by
      rw [hcast] at h0
      linear_combination h0
    rcases (Thm3.Sec8.Basic.two_mul_eq_zero_iff _).1 h1 with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h2)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h2)))

theorem abq_card_le_of_xa_mem {H : Subgroup (QuaternionGroup m)} {i : ZMod (2 * m)}
    (hi : xa i ∈ H) (S : Finset (ZMod (2 * m))) (hS : ∀ j, a j ∈ H → j ∈ S) :
    Nat.card H ≤ 2 * S.card := by
  classical
  have hsub : (H : Set (QuaternionGroup m)) ⊆
      ↑(S.image (fun j => (a j : QuaternionGroup m)) ∪
        S.image (fun s => (xa (i - s) : QuaternionGroup m))) := by
    intro x hx
    cases x with
    | a j =>
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe]
      exact Or.inl ⟨j, hS j hx, rfl⟩
    | xa k =>
      have h1 : xa k * (xa i)⁻¹ ∈ H := H.mul_mem hx (H.inv_mem hi)
      have h2 : xa k * (xa i)⁻¹ = (a (i - k) : QuaternionGroup m) := by
        have e : (xa i : QuaternionGroup m)⁻¹ = xa ((m : ZMod (2 * m)) + i) := rfl
        rw [e, xa_mul_xa]
        congr 1
        linear_combination abq_m_add_m (m := m)
      rw [h2] at h1
      have h3 := hS _ h1
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe]
      exact Or.inr ⟨i - k, h3, by congr 1; ring⟩
  calc Nat.card H = (H : Set (QuaternionGroup m)).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ (↑(S.image (fun j => (a j : QuaternionGroup m)) ∪
        S.image (fun s => (xa (i - s) : QuaternionGroup m))) : Set (QuaternionGroup m)).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (S.image (fun j => (a j : QuaternionGroup m)) ∪
        S.image (fun s => (xa (i - s) : QuaternionGroup m))).card := Set.ncard_coe_finset _
    _ ≤ (S.image (fun j => (a j : QuaternionGroup m))).card +
        (S.image (fun s => (xa (i - s) : QuaternionGroup m))).card := Finset.card_union_le _ _
    _ ≤ S.card + S.card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card := by ring

theorem abq_le_zpowers [NeZero m] {H : Subgroup (QuaternionGroup m)}
    (hx : ∀ i, xa i ∉ H) : H ≤ Subgroup.zpowers (a 1 : QuaternionGroup m) := by
  intro x hxH
  cases x with
  | a j => exact Thm3.Sec8.Basic.a_mem_zpowers j
  | xa j => exact absurd hxH (hx j)

theorem abq_abelian_card [NeZero m] (hm : 3 ≤ m) {H : Subgroup (QuaternionGroup m)}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) :
    Nat.card H ≤ 2 * m ∧ (Nat.card H = 2 * m → ∃ c ∈ H, orderOf c = 2 * m) := by
  by_cases hx : ∃ i, xa i ∈ H
  · obtain ⟨i, hi⟩ := hx
    have hS : ∀ j, a j ∈ H → j ∈ ({0, (m : ZMod (2 * m))} : Finset (ZMod (2 * m))) := by
      intro j hj
      have := (Thm3.Sec8.Basic.two_mul_eq_zero_iff j).1 (abq_a_comm_xa (hH _ hj _ hi))
      simpa using this
    have h4 := abq_card_le_of_xa_mem hi _ hS
    have h5 : ({0, (m : ZMod (2 * m))} : Finset (ZMod (2 * m))).card ≤ 2 := Finset.card_le_two
    exact ⟨by omega, fun h => by omega⟩
  · have hx' : ∀ i, xa i ∉ H := fun i hi => hx ⟨i, hi⟩
    have hle := abq_le_zpowers hx'
    have hcard : Nat.card H ≤ 2 * m :=
      (Subgroup.card_le_of_le hle).trans (Thm3.Sec8.Basic.card_zpowers_a1 (m := m)).le
    refine ⟨hcard, fun h => ?_⟩
    have heq : H = Subgroup.zpowers (a 1 : QuaternionGroup m) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Thm3.Sec8.Basic.card_zpowers_a1]; omega)
    exact ⟨a 1, heq ▸ Subgroup.mem_zpowers _, orderOf_a_one⟩

theorem abq_comm_card [NeZero m] (hm : 4 ≤ m) {m' : ℕ} (hm' : m = m' + m')
    {H : Subgroup (QuaternionGroup m)}
    (hH : ∀ x ∈ H, ∀ y ∈ H, ((y * x)⁻¹ * (x * y)) * ((y * x)⁻¹ * (x * y)) = 1) :
    Nat.card H ≤ 2 * m := by
  by_cases hx : ∃ i, xa i ∈ H
  · obtain ⟨i, hi⟩ := hx
    have hS : ∀ j, a j ∈ H → j ∈ ({0, (m : ZMod (2 * m)), (m' : ZMod (2 * m)),
        (m' : ZMod (2 * m)) + (m : ZMod (2 * m))} : Finset (ZMod (2 * m))) := by
      intro j hj
      have h1 := hH _ hj _ hi
      rw [abq_comm_a_xa, a_mul_a] at h1
      have h2 : (-(j + j) + -(j + j) : ZMod (2 * m)) = 0 :=
        a.inj (h1.trans (a_zero (n := m)).symm)
      have h3 : (j + j) + (j + j) = 0 := by linear_combination -h2
      simpa using abq_quad_cases hm' h3
    have h4 := abq_card_le_of_xa_mem hi _ hS
    have h5 : ({0, (m : ZMod (2 * m)), (m' : ZMod (2 * m)),
        (m' : ZMod (2 * m)) + (m : ZMod (2 * m))} : Finset (ZMod (2 * m))).card ≤ 4 :=
      Finset.card_le_four
    omega
  · have hx' : ∀ i, xa i ∉ H := fun i hi => hx ⟨i, hi⟩
    exact (Subgroup.card_le_of_le (abq_le_zpowers hx')).trans
      (Thm3.Sec8.Basic.card_zpowers_a1 (m := m)).le

end QG

section Transport

theorem abq_exists_hom {X : Type*} [Group X] {P : Subgroup X} {m : ℕ}
    (e : ↥P ≃* QuaternionGroup m) :
    ∃ φ : QuaternionGroup m →* X, Function.Injective φ ∧ P ≤ φ.range :=
  ⟨P.subtype.comp e.symm.toMonoidHom, Subtype.val_injective.comp e.symm.injective,
    fun x hx => ⟨e ⟨x, hx⟩, by simp⟩⟩

theorem abq_transport_abelian {X : Type*} [Group X] {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    {φ : QuaternionGroup m →* X} (hφ : Function.Injective φ) {H : Subgroup X}
    (hle : H ≤ φ.range) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) :
    Nat.card H ≤ 2 * m ∧ (Nat.card H = 2 * m → ∃ c ∈ H, orderOf c = 2 * m) := by
  have hcard : Nat.card (H.comap φ) = Nat.card H := by
    rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hle]
  have hK : ∀ x ∈ H.comap φ, ∀ y ∈ H.comap φ, x * y = y * x := by
    intro x hx y hy
    apply hφ
    rw [map_mul, map_mul]
    exact hH _ hx _ hy
  obtain ⟨h1, h2⟩ := abq_abelian_card hm hK
  refine ⟨hcard ▸ h1, fun h => ?_⟩
  obtain ⟨c, hc, hco⟩ := h2 (hcard ▸ h)
  exact ⟨φ c, hc, by rw [orderOf_injective φ hφ c]; exact hco⟩

theorem abq_transport_comm {X : Type*} [Group X] {m : ℕ} [NeZero m] (hm : 4 ≤ m) {m' : ℕ}
    (hm' : m = m' + m') {φ : QuaternionGroup m →* X} (hφ : Function.Injective φ)
    {H : Subgroup X} (hle : H ≤ φ.range)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ((y * x)⁻¹ * (x * y)) * ((y * x)⁻¹ * (x * y)) = 1) :
    Nat.card H ≤ 2 * m := by
  have hcard : Nat.card (H.comap φ) = Nat.card H := by
    rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hle]
  have hK : ∀ x ∈ H.comap φ, ∀ y ∈ H.comap φ,
      ((y * x)⁻¹ * (x * y)) * ((y * x)⁻¹ * (x * y)) = 1 := by
    intro x hx y hy
    apply hφ
    simpa only [map_mul, map_inv, map_one] using hH _ hx _ hy
  exact hcard ▸ abq_comm_card hm hm' hK

end Transport

section Count

theorem abq_card_sup_mul_card_inf {X : Type*} [Group X] {A C : Subgroup X}
    (hC : C ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card ↥(C ⊔ A) * Nat.card ↥(C ⊓ A) = Nat.card C * Nat.card A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hC
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf C) = Nat.card (C ⊓ A : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

variable {X : Type*} [Group X]

theorem abq_le_normalizer {P₁ P₂ B : Subgroup X} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hB : B ≤ P₁ ⊔ P₂) : B ≤ Subgroup.normalizer (P₂ : Set X) := by
  refine hB.trans (sup_le ?_ Subgroup.le_normalizer)
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (P₂ : Set X))
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (hc a ha b hb).symm

def abq_proj (P₁ P₂ B : Subgroup X) (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) : Subgroup X where
  carrier := {p | p ∈ P₁ ∧ ∃ q ∈ P₂, p * q ∈ B}
  one_mem' := ⟨P₁.one_mem, 1, P₂.one_mem, by simp⟩
  mul_mem' := by
    rintro p p' ⟨hp, q, hq, hpq⟩ ⟨hp', q', hq', hpq'⟩
    refine ⟨P₁.mul_mem hp hp', q * q', P₂.mul_mem hq hq', ?_⟩
    have h : p * p' * (q * q') = (p * q) * (p' * q') := by
      calc p * p' * (q * q') = p * (p' * q) * q' := by simp only [mul_assoc]
        _ = p * (q * p') * q' := by rw [hc p' hp' q hq]
        _ = (p * q) * (p' * q') := by simp only [mul_assoc]
    rw [h]
    exact B.mul_mem hpq hpq'
  inv_mem' := by
    rintro p ⟨hp, q, hq, hpq⟩
    refine ⟨P₁.inv_mem hp, q⁻¹, P₂.inv_mem hq, ?_⟩
    have h : p⁻¹ * q⁻¹ = (p * q)⁻¹ := by
      rw [hc p hp q hq, mul_inv_rev]
    rw [h]
    exact B.inv_mem hpq

theorem abq_proj_le {P₁ P₂ B : Subgroup X} {hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a} :
    abq_proj P₁ P₂ B hc ≤ P₁ := fun _ hx => hx.1

theorem abq_inf_le_proj {P₁ P₂ B : Subgroup X} {hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a} :
    P₁ ⊓ P₂ ≤ abq_proj P₁ P₂ B hc := fun z hz =>
  ⟨hz.1, z⁻¹, P₂.inv_mem hz.2, by simp⟩

theorem abq_proj_comm {P₁ P₂ B : Subgroup X} {hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {x y : X} (hx : x ∈ abq_proj P₁ P₂ B hc)
    (hy : y ∈ abq_proj P₁ P₂ B hc) : (y * x)⁻¹ * (x * y) ∈ P₁ ⊓ P₂ := by
  obtain ⟨hx1, q, hq, hxq⟩ := hx
  obtain ⟨hy1, q', hq', hyq⟩ := hy
  have h1 : x * q * (y * q') = x * y * (q * q') := by
    calc x * q * (y * q') = x * (q * y) * q' := by simp only [mul_assoc]
      _ = x * (y * q) * q' := by rw [← hc y hy1 q hq]
      _ = x * y * (q * q') := by simp only [mul_assoc]
  have h2 : y * q' * (x * q) = y * x * (q' * q) := by
    calc y * q' * (x * q) = y * (q' * x) * q := by simp only [mul_assoc]
      _ = y * (x * q') * q := by rw [← hc x hx1 q' hq']
      _ = y * x * (q' * q) := by simp only [mul_assoc]
  have h3 : x * y * (q * q') = y * x * (q' * q) := by
    rw [← h1, ← h2]
    exact hBc _ hxq _ hyq
  have h4 : (y * x)⁻¹ * (x * y) = (q' * q) * (q * q')⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h3, inv_mul_cancel_left]
  refine ⟨P₁.mul_mem (P₁.inv_mem (P₁.mul_mem hy1 hx1)) (P₁.mul_mem hx1 hy1), ?_⟩
  rw [h4]
  exact P₂.mul_mem (P₂.mul_mem hq' hq) (P₂.inv_mem (P₂.mul_mem hq hq'))

theorem abq_count_key [Finite X] {P₁ P₂ : Subgroup X} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2) {B : Subgroup X} (hB : B ≤ P₁ ⊔ P₂)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∃ H : Subgroup X, H ≤ P₁ ∧ (∀ x ∈ H, ∀ y ∈ H, (y * x)⁻¹ * (x * y) ∈ P₁ ⊓ P₂) ∧
      2 * Nat.card ↥B = Nat.card ↥(B ⊓ P₂) * Nat.card ↥H := by
  set H := abq_proj P₁ P₂ B hc
  have hHle : H ≤ P₁ := abq_proj_le
  have hsup : B ⊔ P₂ = H ⊔ P₂ := by
    apply le_antisymm
    · refine sup_le (fun b hb => ?_) le_sup_right
      obtain ⟨p, hp, q, hq, rfl⟩ := Thm3.Sec8.Basic.mem_sup_of_commute' hc (hB hb)
      exact mul_mem (Subgroup.mem_sup_left (show p ∈ H from ⟨hp, q, hq, hb⟩))
        (Subgroup.mem_sup_right hq)
    · refine sup_le (fun p hp => ?_) le_sup_right
      obtain ⟨-, q, hq, hpq⟩ := hp
      have : p = (p * q) * q⁻¹ := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hpq) (Subgroup.mem_sup_right (P₂.inv_mem hq))
  have hHinf : H ⊓ P₂ = P₁ ⊓ P₂ :=
    le_antisymm (inf_le_inf_right _ hHle) (le_inf abq_inf_le_proj inf_le_right)
  have h1 := abq_card_sup_mul_card_inf (abq_le_normalizer hc hB)
  have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H P₂
    (fun x hx y hy => hc x (hHle hx) y hy)).1
  rw [hsup] at h1
  rw [hHinf, hinf] at h2
  refine ⟨H, hHle, fun x hx y hy => abq_proj_comm hBc hx hy, ?_⟩
  have hpos : 0 < Nat.card ↥P₂ := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc Nat.card ↥P₂ * (2 * Nat.card ↥B) = 2 * (Nat.card ↥B * Nat.card ↥P₂) := by ring
    _ = 2 * (Nat.card ↥(H ⊔ P₂) * Nat.card ↥(B ⊓ P₂)) := by rw [h1]
    _ = (Nat.card ↥(H ⊔ P₂) * 2) * Nat.card ↥(B ⊓ P₂) := by ring
    _ = (Nat.card ↥H * Nat.card ↥P₂) * Nat.card ↥(B ⊓ P₂) := by rw [h2]
    _ = Nat.card ↥P₂ * (Nat.card ↥(B ⊓ P₂) * Nat.card ↥H) := by ring

theorem abq_sq_eq_one {P₁ P₂ : Subgroup X} (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2) {c : X}
    (hc : c ∈ P₁ ⊓ P₂) : c * c = 1 := by
  have h : (⟨c, hc⟩ : ↥(P₁ ⊓ P₂)) ^ Nat.card ↥(P₁ ⊓ P₂) = 1 := pow_card_eq_one'
  rw [hinf] at h
  have := congrArg Subtype.val h
  simpa [pow_two] using this

end Count

section Final

variable {X : Type*} [Group X]

theorem abq_side [Finite X] {m : ℕ} [NeZero m] (hm : 4 ≤ m) {m' : ℕ} (hm' : m = m' + m')
    {P₁ P₂ : Subgroup X} (e₁ : ↥P₁ ≃* QuaternionGroup m) (e₂ : ↥P₂ ≃* QuaternionGroup m)
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2)
    {B : Subgroup X} (hB : B ≤ P₁ ⊔ P₂) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    2 * Nat.card ↥B ≤ (2 * m) * (2 * m) ∧
      (2 * Nat.card ↥B = (2 * m) * (2 * m) → ∃ c ∈ P₂, c ∈ B ∧ orderOf c = 2 * m) := by
  obtain ⟨φ₁, hφ₁, hle₁⟩ := abq_exists_hom e₁
  obtain ⟨φ₂, hφ₂, hle₂⟩ := abq_exists_hom e₂
  obtain ⟨H, hH1, hHc, hcard⟩ := abq_count_key hc hinf hB hBc
  have hH : Nat.card ↥H ≤ 2 * m := by
    refine abq_transport_comm hm hm' hφ₁ (hH1.trans hle₁) fun x hx y hy => ?_
    exact abq_sq_eq_one hinf (hHc x hx y hy)
  obtain ⟨hC, hCo⟩ := abq_transport_abelian (by omega) hφ₂ (H := B ⊓ P₂)
    (inf_le_right.trans hle₂) (fun x hx y hy => hBc x hx.1 y hy.1)
  refine ⟨?_, fun heq => ?_⟩
  · rw [hcard]
    exact Nat.mul_le_mul hC hH
  · have hpos : 0 < 2 * m := by omega
    have hCeq : Nat.card ↥(B ⊓ P₂) = 2 * m := by
      by_contra hne
      have hlt : Nat.card ↥(B ⊓ P₂) < 2 * m := lt_of_le_of_ne hC hne
      have hlt2 : Nat.card ↥(B ⊓ P₂) * Nat.card ↥H < (2 * m) * (2 * m) :=
        calc _ ≤ Nat.card ↥(B ⊓ P₂) * (2 * m) := Nat.mul_le_mul_left _ hH
          _ < (2 * m) * (2 * m) := Nat.mul_lt_mul_of_pos_right hlt hpos
      exact absurd (hcard.symm.trans heq) hlt2.ne
    obtain ⟨c, hcmem, hco⟩ := hCo hCeq
    exact ⟨c, hcmem.2, hcmem.1, hco⟩

theorem abq_final_aux [Finite X] {m : ℕ} [NeZero m] (hm : 4 ≤ m) {m' : ℕ} (hm' : m = m' + m')
    {P₁ P₂ : Subgroup X} (e₁ : ↥P₁ ≃* QuaternionGroup m) (e₂ : ↥P₂ ≃* QuaternionGroup m)
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2)
    {B : Subgroup X} (hB : B ≤ P₁ ⊔ P₂) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    2 * Nat.card ↥B ≤ (2 * m) * (2 * m) ∧
      (2 * Nat.card ↥B = (2 * m) * (2 * m) →
        (∃ c ∈ P₁, c ∈ B ∧ orderOf c = 2 * m) ∧ ∃ c ∈ P₂, c ∈ B ∧ orderOf c = 2 * m) := by
  obtain ⟨h1, h1'⟩ := abq_side hm hm' e₁ e₂ hc hinf hB hBc
  have hc' : ∀ a ∈ P₂, ∀ b ∈ P₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : Nat.card ↥(P₂ ⊓ P₁) = 2 := by rw [inf_comm]; exact hinf
  obtain ⟨-, h2'⟩ := abq_side hm hm' e₂ e₁ hc' hinf' (sup_comm P₁ P₂ ▸ hB) hBc
  exact ⟨h1, fun h => ⟨h2' h, h1' h⟩⟩

end Final

theorem abelian_in_quaternion_product {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    {P₁ P₂ : Subgroup X} (h₁ : IVK.IsQuaternionTwoGroup ↥P₁ (n + 1))
    (h₂ : IVK.IsQuaternionTwoGroup ↥P₂ (n + 1))
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : Nat.card ↥(P₁ ⊓ P₂) = 2)
    {B : Subgroup X} (hB : B ≤ P₁ ⊔ P₂) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥B ≤ 2 ^ (2 * n - 1) ∧
      (Nat.card ↥B = 2 ^ (2 * n - 1) →
        (∃ c ∈ P₁, c ∈ B ∧ orderOf c = 2 ^ n) ∧ ∃ c ∈ P₂, c ∈ B ∧ orderOf c = 2 ^ n) := by
  obtain ⟨-, ⟨e₁⟩⟩ := h₁
  obtain ⟨-, ⟨e₂⟩⟩ := h₂
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hk : j + 3 + 1 - 2 = j + 2 := by omega
  rw [hk] at e₁ e₂
  have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hm : 4 ≤ 2 ^ (j + 2) := by
    have e : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    omega
  have hm' : 2 ^ (j + 2) = 2 ^ (j + 1) + 2 ^ (j + 1) := by ring
  obtain ⟨hle, heq⟩ := abq_final_aux hm hm' e₁ e₂ hc hinf hB hBc
  have hN : 2 * 2 ^ (j + 2) = 2 ^ (j + 3) := by ring
  have hexp : 2 * (j + 3) - 1 = 2 * j + 5 := by omega
  have hNN : (2 * 2 ^ (j + 2)) * (2 * 2 ^ (j + 2)) = 2 * 2 ^ (2 * (j + 3) - 1) := by
    rw [hexp]; ring
  rw [hNN] at hle heq
  rw [hN] at heq
  refine ⟨by omega, fun h => heq (by omega)⟩

end CFSG.GH74.GLS.Stage1.Main
