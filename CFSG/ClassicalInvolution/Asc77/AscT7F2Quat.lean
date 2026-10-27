module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRQuat
public import CFSG.ClassicalInvolution.Asc77.AscL62Quat

public section

namespace CFSG.ClassicalInvolution.Asc77.T7F2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure QuatCoord (R : Subgroup G) (a b : G) (n : ℕ) : Prop where
  ha : a ∈ R
  hb : b ∈ R
  hbab : b * a * b⁻¹ = a⁻¹
  hn : 1 ≤ n
  hord : orderOf a = 2 ^ (n + 1)
  hbb : b * b = a ^ (2 ^ n)
  cover : ∀ r ∈ R, (∃ i : ℤ, r = a ^ i) ∨ ∃ i : ℤ, r = b * a ^ i

namespace QuatCoord

variable {R : Subgroup G} {a b : G} {n : ℕ}

theorem pow_card (c : QuatCoord R a b n) : a ^ (2 ^ (n + 1)) = 1 := by
  rw [← c.hord]; exact pow_orderOf_eq_one a

theorem zpow_eq_iff (c : QuatCoord R a b n) {i j : ℤ} :
    a ^ i = a ^ j ↔ ((2 : ℤ) ^ (n + 1)) ∣ i - j := by
  rw [zpow_eq_zpow_iff_modEq, c.hord]
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h; simpa [dvd_sub_comm] using h
  · intro h; simpa [dvd_sub_comm] using h

theorem a_sq_ne_one (c : QuatCoord R a b n) : a * a ≠ 1 := by
  intro h
  have h2 : a ^ 2 = 1 := by rw [pow_two]; exact h
  have := orderOf_dvd_of_pow_eq_one h2
  rw [c.hord] at this
  have h3 : 2 ^ (n + 1) ≤ 2 := Nat.le_of_dvd (by norm_num) this
  have h4 : 2 ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by have := c.hn; omega)
  omega

theorem b_not_mem (c : QuatCoord R a b n) : b ∉ Subgroup.zpowers a :=
  T7DR.not_mem_zpowers_of_inv c.hbab c.a_sq_ne_one

theorem zpow_a_mul_b (c : QuatCoord R a b n) (i : ℤ) : a ^ i * b = b * a ^ (-i) :=
  T7DR.zpow_mul_eq_of_inv c.hbab i

theorem conj_zpow (c : QuatCoord R a b n) (i : ℤ) : b * a ^ i * b⁻¹ = a ^ (-i) :=
  T7DR.conj_zpow_of_inv c.hbab i

theorem sq_mul (c : QuatCoord R a b n) (i : ℤ) : (b * a ^ i) * (b * a ^ i) = a ^ (2 ^ n) := by
  rw [T7DR.mul_zpow_mul_self_eq c.hbab i, c.hbb]

theorem natCard (c : QuatCoord R a b n) : Nat.card R = 2 ^ (n + 2) := by
  have hA : (Subgroup.zpowers a) ⊓ R = Subgroup.zpowers a :=
    inf_eq_left.mpr (Subgroup.zpowers_le.mpr c.ha)
  have hidx : (Subgroup.zpowers a).relIndex R = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨b, c.hb⟩, fun y => ?_⟩
    obtain ⟨r, hr⟩ := y
    rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have h1 : (⟨a ^ i, hr⟩ : ↥R) ∈ (Subgroup.zpowers a).subgroupOf R :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.zpow_mem_zpowers a i)
      have h2 : (⟨a ^ i, hr⟩ * ⟨b, c.hb⟩ : ↥R) ∉ (Subgroup.zpowers a).subgroupOf R := by
        intro h
        have h' : a ^ i * b ∈ Subgroup.zpowers a := Subgroup.mem_subgroupOf.mp h
        apply c.b_not_mem
        have := (Subgroup.zpowers a).mul_mem (Subgroup.zpow_mem_zpowers a (-i)) h'
        simpa [← mul_assoc, ← zpow_add] using this
      exact Or.inr ⟨h1, h2⟩
    · have h1 : (⟨b * a ^ i, hr⟩ : ↥R) ∉ (Subgroup.zpowers a).subgroupOf R := by
        intro h
        have h' : b * a ^ i ∈ Subgroup.zpowers a := Subgroup.mem_subgroupOf.mp h
        apply c.b_not_mem
        have := (Subgroup.zpowers a).mul_mem h' (Subgroup.zpow_mem_zpowers a (-i))
        simpa [mul_assoc, ← zpow_add] using this
      have h2 : (⟨b * a ^ i, hr⟩ * ⟨b, c.hb⟩ : ↥R) ∈ (Subgroup.zpowers a).subgroupOf R := by
        rw [Subgroup.mem_subgroupOf]
        show b * a ^ i * b ∈ Subgroup.zpowers a
        have : b * a ^ i * b = a ^ (2 ^ n - i) := by
          calc b * a ^ i * b = b * (a ^ i * b) := by group
            _ = b * (b * a ^ (-i)) := by rw [c.zpow_a_mul_b]
            _ = (b * b) * a ^ (-i) := by group
            _ = a ^ (2 ^ n) * a ^ (-i) := by rw [c.hbb]
            _ = a ^ ((2 ^ n : ℤ) - i) := by
              rw [← zpow_natCast, ← zpow_add]; push_cast; ring_nf
            _ = a ^ (2 ^ n - i) := rfl
        rw [this]
        exact Subgroup.zpow_mem_zpowers a _
      exact Or.inl ⟨h2, h1⟩
  have hmul := Subgroup.relIndex_mul_card (Subgroup.zpowers a) R
  rw [hA, hidx, Nat.card_zpowers, c.hord] at hmul
  rw [← hmul]
  ring

theorem zpow_eq_val (c : QuatCoord R a b n) (t : ℤ) (i : ZMod (2 * 2 ^ n))
    (h : (t : ZMod (2 * 2 ^ n)) = i) : a ^ t = a ^ (i.val : ℤ) := by
  rw [c.zpow_eq_iff]
  have e : ((2 : ℤ) ^ (n + 1)) = ((2 * 2 ^ n : ℕ) : ℤ) := by push_cast; ring
  rw [e, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h]
  simp

theorem mul_xa_xa (c : QuatCoord R a b n) (i j : ℤ) :
    (b * a ^ i) * (b * a ^ j) = a ^ (((2 ^ n : ℕ) : ℤ) - i + j) := by
  calc b * a ^ i * (b * a ^ j) = b * (a ^ i * b) * a ^ j := by group
    _ = b * (b * a ^ (-i)) * a ^ j := by rw [c.zpow_a_mul_b]
    _ = (b * b) * (a ^ (-i) * a ^ j) := by group
    _ = a ^ (((2 ^ n : ℕ) : ℤ)) * a ^ (-i + j) := by rw [c.hbb, ← zpow_natCast, ← zpow_add]
    _ = a ^ (((2 ^ n : ℕ) : ℤ) - i + j) := by rw [← zpow_add]; ring_nf

end QuatCoord

@[expose] noncomputable def qmap (a b : G) (n : ℕ) : QuaternionGroup (2 ^ n) → G
  | .a i => a ^ (i.val : ℤ)
  | .xa i => b * a ^ (i.val : ℤ)

namespace QuatCoord

variable {R : Subgroup G} {a b : G} {n : ℕ}

theorem qmap_mul (c : QuatCoord R a b n) (x y : QuaternionGroup (2 ^ n)) :
    qmap a b n (x * y) = qmap a b n x * qmap a b n y := by
  cases x with
  | a i =>
    cases y with
    | a j =>
      rw [QuaternionGroup.a_mul_a]
      show a ^ ((i + j).val : ℤ) = a ^ (i.val : ℤ) * a ^ (j.val : ℤ)
      rw [← zpow_add]
      exact (c.zpow_eq_val _ _ (by simp)).symm
    | xa j =>
      rw [QuaternionGroup.a_mul_xa]
      show b * a ^ ((j - i).val : ℤ) = a ^ (i.val : ℤ) * (b * a ^ (j.val : ℤ))
      rw [← mul_assoc, c.zpow_a_mul_b, mul_assoc, ← zpow_add]
      congr 1
      rw [neg_add_eq_sub]
      exact (c.zpow_eq_val (j.val - i.val) (j - i) (by simp)).symm
  | xa i =>
    cases y with
    | a j =>
      rw [QuaternionGroup.xa_mul_a]
      show b * a ^ ((i + j).val : ℤ) = (b * a ^ (i.val : ℤ)) * a ^ (j.val : ℤ)
      rw [mul_assoc, ← zpow_add]
      congr 1
      exact (c.zpow_eq_val _ _ (by simp)).symm
    | xa j =>
      rw [QuaternionGroup.xa_mul_xa]
      show a ^ (((2 ^ n : ℕ) + j - i : ZMod (2 * 2 ^ n)).val : ℤ) =
        (b * a ^ (i.val : ℤ)) * (b * a ^ (j.val : ℤ))
      rw [c.mul_xa_xa]
      exact (c.zpow_eq_val _ _ (by simp; ring)).symm


@[expose] noncomputable def qhom (c : QuatCoord R a b n) : QuaternionGroup (2 ^ n) →* G where
  toFun := qmap a b n
  map_one' := by
    show qmap a b n (QuaternionGroup.a 0) = 1
    simp [qmap]
  map_mul' := c.qmap_mul

theorem qhom_a (c : QuatCoord R a b n) (i : ZMod (2 * 2 ^ n)) :
    c.qhom (QuaternionGroup.a i) = a ^ (i.val : ℤ) := rfl

theorem qhom_xa (c : QuatCoord R a b n) (i : ZMod (2 * 2 ^ n)) :
    c.qhom (QuaternionGroup.xa i) = b * a ^ (i.val : ℤ) := rfl

theorem val_eq_of_zpow_eq (c : QuatCoord R a b n) {i j : ZMod (2 * 2 ^ n)}
    (h : a ^ (i.val : ℤ) = a ^ (j.val : ℤ)) : i = j := by
  rw [c.zpow_eq_iff] at h
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have e : ((2 : ℤ) ^ (n + 1)) = ((2 * 2 ^ n : ℕ) : ℤ) := by push_cast; ring
  rw [e] at h
  have h0 : ((i.val : ℤ) - (j.val : ℤ)) = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd h
    rw [abs_lt]
    constructor <;> omega
  exact ZMod.val_injective _ (by omega)

theorem qhom_injective (c : QuatCoord R a b n) : Function.Injective c.qhom := by
  intro x y hxy
  have hnot : ∀ i j : ℤ, a ^ i ≠ b * a ^ j := by
    intro i j h
    apply c.b_not_mem
    have : b = a ^ i * (a ^ j)⁻¹ := by rw [h]; group
    rw [this]
    exact (Subgroup.zpowers a).mul_mem (Subgroup.zpow_mem_zpowers a i)
      ((Subgroup.zpowers a).inv_mem (Subgroup.zpow_mem_zpowers a j))
  cases x with
  | a i =>
    cases y with
    | a j => exact congrArg QuaternionGroup.a (c.val_eq_of_zpow_eq hxy)
    | xa j => exact absurd hxy (hnot _ _)
  | xa i =>
    cases y with
    | a j => exact absurd hxy.symm (hnot _ _)
    | xa j =>
      have h : a ^ (i.val : ℤ) = a ^ (j.val : ℤ) := mul_left_cancel hxy
      exact congrArg QuaternionGroup.xa (c.val_eq_of_zpow_eq h)

theorem qhom_mem (c : QuatCoord R a b n) (x : QuaternionGroup (2 ^ n)) : c.qhom x ∈ R := by
  cases x with
  | a i => exact R.zpow_mem c.ha _
  | xa i => exact R.mul_mem c.hb (R.zpow_mem c.ha _)

theorem isQuatSub (c : QuatCoord R a b n) : IsQuatSub R := by
  refine ⟨n, c.hn, ⟨(MulEquiv.ofBijective (c.qhom.codRestrict R c.qhom_mem) ?_).symm⟩⟩
  constructor
  · intro x y hxy
    exact c.qhom_injective (congrArg Subtype.val hxy)
  · rintro ⟨r, hr⟩
    rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨QuaternionGroup.a (i : ZMod (2 * 2 ^ n)), Subtype.ext ?_⟩
      exact (c.zpow_eq_val i _ rfl).symm
    · refine ⟨QuaternionGroup.xa (i : ZMod (2 * 2 ^ n)), Subtype.ext ?_⟩
      show b * a ^ (((i : ZMod (2 * 2 ^ n))).val : ℤ) = b * a ^ i
      rw [← c.zpow_eq_val i _ rfl]

end QuatCoord

section Extract

variable [Finite G] {R V : Subgroup G} {z : G}

theorem exists_coord (hR : IsQuatSub R) (hz : IsUniqueInvolution R z) (hV2 : IsPGroup 2 V)
    (hVR : ∀ y ∈ V, conjSub y R = R) :
    ∃ (a b : G) (n : ℕ), QuatCoord R a b n ∧
      ∀ y ∈ V, conjSub y (Subgroup.zpowers a) = Subgroup.zpowers a := by
  obtain ⟨C, hCR, hCc, hcard, hCinv⟩ := AscL62.exists_invariant_cyclic hR hz hV2 hVR
  obtain ⟨k, hk, hRk⟩ := hR.natCard_eq
  obtain ⟨a, ha⟩ : ∃ a : G, Subgroup.zpowers a = C := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
    refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨j, congrArg Subtype.val hj⟩
  have haC : a ∈ C := ha ▸ Subgroup.mem_zpowers a
  have hCcard : Nat.card C = 2 ^ (k + 1) := by
    have : 2 ^ (k + 2) = 2 * Nat.card C := hRk ▸ hcard
    have h2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    omega
  have hord : orderOf a = 2 ^ (k + 1) := by
    rw [← Nat.card_zpowers, ha, hCcard]
  obtain ⟨b, hbR, hbC⟩ : ∃ b ∈ R, b ∉ C := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show R ≤ C from hcon)
    have h2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    have h3 : 0 < 2 ^ (k + 1) := by positivity
    omega
  have hbab : b * a * b⁻¹ = a⁻¹ := AscL62.conj_eq_inv_of_not_mem hR hz hCR hCc hcard hbR hbC haC
  have hbb : b * b = z := AscL62.sq_eq_of_not_mem hR hz hCR hCc hcard hbR hbC
  have hzC : z ∈ C := AscL62.mem_of_index_two hR hz hCR hcard
  have hzpow : z = a ^ (2 ^ k) := by
    have h1 : (a ^ (2 ^ k)) * (a ^ (2 ^ k)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      have := pow_orderOf_eq_one a
      rwa [hord] at this
    have h2 : a ^ (2 ^ k) ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hord] at this
      have := Nat.le_of_dvd (by positivity) this
      have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rcases hz.unique (a ^ (2 ^ k)) (R.pow_mem (hCR haC) _) h1 with h | h
    · exact absurd h h2
    · exact h.symm
  have hidx : (C.subgroupOf R).index = 2 := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf R)
    have h2 : Nat.card (C.subgroupOf R) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv
    rw [h2, hCcard, hRk] at h1
    have h3 : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
    have h4 : 0 < 2 ^ (k + 1) := by positivity
    nlinarith
  refine ⟨a, b, k, ⟨hCR haC, hbR, hbab, hk, hord, hbb.trans hzpow, ?_⟩, fun y hy => ?_⟩
  · intro r hr
    by_cases hrC : r ∈ C
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (ha ▸ hrC)
      exact Or.inl ⟨i, hi.symm⟩
    · right
      have hx : (⟨b⁻¹, R.inv_mem hbR⟩ : ↥R) ∉ C.subgroupOf R := fun h => hbC (by
        have := C.inv_mem (Subgroup.mem_subgroupOf.mp h)
        simpa using this)
      have hy' : (⟨r, hr⟩ : ↥R) ∉ C.subgroupOf R := hrC
      have hm := (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        ⟨fun h => absurd h hx, fun h => absurd h hy'⟩
      have hm' : b⁻¹ * r ∈ C := Subgroup.mem_subgroupOf.mp hm
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (ha ▸ hm')
      exact ⟨i, by rw [hi]; group⟩
  · rw [← ha] at hCinv
    exact hCinv y hy

end Extract


end CFSG.ClassicalInvolution.Asc77.T7F2
