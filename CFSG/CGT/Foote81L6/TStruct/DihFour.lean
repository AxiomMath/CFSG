module

public import CFSG.CGT.Foote81L6.Star
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import CFSG.CGT.Foote81L6.TStruct.ElemBound

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup DihedralGroup

theorem zc_eq_r {k : ℕ} (hk : 1 ≤ k) : zc k = r ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  rw [← rho_pow hk, r_pow, one_mul]

theorem add_self_eq_zero_iff {k : ℕ} (hk : 1 ≤ k) {j : ZMod (2 ^ k)} :
    j + j = 0 ↔ j = 0 ∨ j = ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · exact eq_zero_or_half
  · rintro (rfl | rfl)
    · simp
    · exact two_pow_add_self b

theorem quarter_add_quarter {k : ℕ} (hk : 2 ≤ k) :
    ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) + ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) =
      ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  rw [← Nat.cast_add, ← two_mul, ← pow_succ']
  congr 2
  omega

theorem zpar_half {k : ℕ} (hk : 1 ≤ k) (hk2 : 2 ≤ k) :
    zpar k hk ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) = 0 := by
  rw [zpar_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_pow_self 2 (by omega)

theorem zpar_add_self {k : ℕ} (hk : 1 ≤ k) (c : ZMod (2 ^ k)) : zpar k hk (c + c) = 0 :=
  (zpar_eq_zero_iff hk).2 ⟨c, rfl⟩

theorem sr_ne_one' {n : ℕ} (i : ZMod n) : (sr i : DihedralGroup n) ≠ 1 := by
  rw [one_def]
  intro h
  cases h

theorem sr_ne_zc {k : ℕ} (hk : 1 ≤ k) (i : ZMod (2 ^ k)) : sr i ≠ zc k := by
  rw [zc_eq_r hk]
  intro h
  cases h

theorem r_eq_of_mul_self {k : ℕ} (hk : 1 ≤ k) {j : ZMod (2 ^ k)}
    (h : (r j : DihedralGroup (2 ^ k)) * r j = 1) : r j = 1 ∨ r j = zc k := by
  rw [r_mul_r, one_def, r.injEq] at h
  rcases (add_self_eq_zero_iff hk).1 h with rfl | rfl
  · exact Or.inl r_zero
  · exact Or.inr (zc_eq_r hk).symm

@[expose] def dihFour (k : ℕ) (i : ZMod (2 ^ k)) : Subgroup (DihedralGroup (2 ^ k)) :=
  zpowers (sr i) ⊔ zpowers (zc k)

section Four

variable {k : ℕ} (hk : 1 ≤ k)

include hk in
theorem mem_dihFour {i : ZMod (2 ^ k)} {x : DihedralGroup (2 ^ k)} :
    x ∈ dihFour k i ↔ x = 1 ∨ x = zc k ∨ x = sr i ∨ x = sr i * zc k := by
  have hcomm : ∀ u ∈ zpowers (sr i), ∀ v ∈ zpowers (zc k), u * v = v * u :=
    fun u _ v hv => by
      rcases eq_one_or_eq_of_mem_zpowers (zc_mul_self hk) hv with rfl | rfl
      · rw [mul_one, one_mul]
      · exact zc_comm hk u
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 hx
    rcases eq_one_or_eq_of_mem_zpowers (sr_mul_self i) hu with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers (zc_mul_self hk) hv with rfl | rfl
    · exact Or.inl (mul_one 1)
    · exact Or.inr (Or.inl (one_mul _))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem zc_mem_dihFour (i : ZMod (2 ^ k)) : zc k ∈ dihFour k i := mem_sup_right (mem_zpowers _)

theorem sr_mem_dihFour (i : ZMod (2 ^ k)) : sr i ∈ dihFour k i := mem_sup_left (mem_zpowers _)

include hk in
theorem card_dihFour (i : ZMod (2 ^ k)) : Nat.card (dihFour k i) = 4 :=
  card_zpowers_sup_zpowers (sr_mul_self i) (zc_mul_self hk) (sr_ne_one' i) (zc_ne_one hk)
    (sr_ne_zc hk i) (zc_comm hk _)

include hk in
theorem mul_self_of_mem_dihFour (i : ZMod (2 ^ k)) : ∀ x ∈ dihFour k i, x * x = 1 :=
  fun _ hx => mul_self_of_mem_zpowers_sup_zpowers (sr_mul_self i) (zc_mul_self hk)
    (zc_comm hk _) hx

include hk in
theorem mem_dihFour_of_comm {i : ZMod (2 ^ k)} {x : DihedralGroup (2 ^ k)}
    (hc : x * sr i = sr i * x) : x ∈ dihFour k i := by
  rw [mem_dihFour hk]
  cases x with
  | r j =>
    rw [r_mul_sr, sr_mul_r] at hc
    have hj : j + j = 0 := by
      have := sr.inj hc
      linear_combination -this
    rcases (add_self_eq_zero_iff hk).1 hj with rfl | rfl
    · exact Or.inl r_zero
    · exact Or.inr (Or.inl (zc_eq_r hk).symm)
  | sr j =>
    rw [sr_mul_sr, sr_mul_sr] at hc
    have hj : (j - i) + (j - i) = 0 := by
      have := r.inj hc
      linear_combination -this
    rcases (add_self_eq_zero_iff hk).1 hj with h0 | hh
    · refine Or.inr (Or.inr (Or.inl ?_))
      congr 1
      linear_combination h0
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [zc_eq_r hk, sr_mul_r]
      congr 1
      linear_combination hh

include hk in
theorem eq_dihFour {V : Subgroup (DihedralGroup (2 ^ k))} (hV2 : ∀ x ∈ V, x * x = 1)
    (hV4 : Nat.card V = 4) : ∃ i, V = dihFour k i := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  have hrefl : ∃ i, sr i ∈ V := by
    by_contra hno
    have hle : V ≤ zpowers (zc k) := by
      intro x hx
      cases x with
      | r j =>
        rcases r_eq_of_mul_self hk (hV2 _ hx) with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact mem_zpowers _
      | sr j => exact absurd ⟨j, hx⟩ hno
    have h1 := card_le_of_le hle
    rw [hV4, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact zc_mul_self hk)
      (zc_ne_one hk)] at h1
    omega
  obtain ⟨i, hi⟩ := hrefl
  refine ⟨i, eq_of_le_of_card_ge (fun x hx => mem_dihFour_of_comm hk
    (comm_of_mul_self hV2 hx hi)) ?_⟩
  rw [card_dihFour hk, hV4]

include hk in
theorem dihFour_eq_iff {i j : ZMod (2 ^ k)} :
    dihFour k i = dihFour k j ↔ j = i ∨ j = i + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  constructor
  · intro h
    have hj : sr j ∈ dihFour k i := h ▸ sr_mem_dihFour j
    rw [mem_dihFour hk] at hj
    rcases hj with h1 | h1 | h1 | h1
    · exact absurd h1 (sr_ne_one' j)
    · exact absurd h1 (sr_ne_zc hk j)
    · exact Or.inl (sr.inj h1)
    · rw [zc_eq_r hk, sr_mul_r] at h1
      exact Or.inr (sr.inj h1)
  · rintro (rfl | rfl)
    · rfl
    · haveI : NeZero (2 ^ k) := ⟨by positivity⟩
      have hle : dihFour k (i + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k))) ≤ dihFour k i := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 (zc_mem_dihFour i))
        rw [mem_dihFour hk, zc_eq_r hk, sr_mul_r]
        exact Or.inr (Or.inr (Or.inr rfl))
      exact (eq_of_le_of_card_ge hle (by rw [card_dihFour hk, card_dihFour hk])).symm

include hk in
theorem map_conj_r_dihFour (i c : ZMod (2 ^ k)) :
    (dihFour k i).map (MulAut.conj (r c)).toMonoidHom = dihFour k (i - (c + c)) := by
  rw [dihFour, dihFour, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  congr 2
  · show r c * sr i * (r c)⁻¹ = sr (i - (c + c))
    rw [inv_r, r_mul_sr, sr_mul_r]
    congr 1
    ring
  · show r c * zc k * (r c)⁻¹ = zc k
    rw [zc_comm hk, mul_inv_cancel_right]

include hk in
theorem map_conj_sr_dihFour (i c : ZMod (2 ^ k)) :
    (dihFour k i).map (MulAut.conj (sr c)).toMonoidHom = dihFour k (c + c - i) := by
  rw [dihFour, dihFour, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  congr 2
  · show sr c * sr i * (sr c)⁻¹ = sr (c + c - i)
    rw [inv_sr, sr_mul_sr, r_mul_sr]
    congr 1
    ring
  · show sr c * zc k * (sr c)⁻¹ = zc k
    rw [zc_comm hk, mul_inv_cancel_right]

include hk in
theorem exists_conj_dihFour_iff (hk2 : 2 ≤ k) {i j : ZMod (2 ^ k)} :
    (∃ g : DihedralGroup (2 ^ k), (dihFour k i).map (MulAut.conj g).toMonoidHom = dihFour k j) ↔
      zpar k hk i = zpar k hk j := by
  constructor
  · rintro ⟨g, hg⟩
    cases g with
    | r c =>
      rw [map_conj_r_dihFour hk, dihFour_eq_iff hk] at hg
      rcases hg with rfl | rfl
      · rw [map_sub, zpar_add_self hk]
        generalize zpar k hk i = u
        revert u
        decide
      · rw [map_add, map_sub, zpar_add_self hk, zpar_half hk hk2]
        generalize zpar k hk i = u
        revert u
        decide
    | sr c =>
      rw [map_conj_sr_dihFour hk, dihFour_eq_iff hk] at hg
      rcases hg with rfl | rfl
      · rw [map_sub, zpar_add_self hk]
        generalize zpar k hk i = u
        revert u
        decide
      · rw [map_add, map_sub, zpar_add_self hk, zpar_half hk hk2]
        generalize zpar k hk i = u
        revert u
        decide
  · intro h
    have h0 : zpar k hk (i - j) = 0 := by
      rw [map_sub, h]
      generalize zpar k hk j = u
      revert u
      decide
    obtain ⟨c, hc⟩ := (zpar_eq_zero_iff hk).1 h0
    refine ⟨r c, ?_⟩
    rw [map_conj_r_dihFour hk]
    congr 1
    linear_combination hc

include hk in
theorem centralizer_dihFour (i : ZMod (2 ^ k)) :
    centralizer (dihFour k i : Set (DihedralGroup (2 ^ k))) = dihFour k i := by
  apply le_antisymm
  · intro x hx
    exact mem_dihFour_of_comm hk ((mem_centralizer_iff.1 hx) _ (sr_mem_dihFour i)).symm
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact comm_of_mul_self (mul_self_of_mem_dihFour hk i) hy hx

include hk in
theorem conj_of_mem_normalizer {i : ZMod (2 ^ k)} {x : DihedralGroup (2 ^ k)}
    (hx : x ∈ normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))) {v : DihedralGroup (2 ^ k)}
    (hv : v ∈ dihFour k i) : x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * zc k := by
  have hz : x * zc k * x⁻¹ = zc k := by rw [zc_comm hk, mul_inv_cancel_right]
  have hs : x * sr i * x⁻¹ = sr i ∨ x * sr i * x⁻¹ = sr i * zc k := by
    have hmem := (mem_normalizer_iff.1 hx (sr i)).1 (sr_mem_dihFour i)
    rw [mem_dihFour hk] at hmem
    rcases hmem with h | h | h | h
    · exfalso
      apply sr_ne_one' i
      have : sr i = x⁻¹ * (x * sr i * x⁻¹) * x := by group
      rw [this, h]
      group
    · exfalso
      apply sr_ne_zc hk i
      have : sr i = x⁻¹ * (x * sr i * x⁻¹) * x := by group
      rw [this, h, zc_comm hk x⁻¹, inv_mul_cancel_right]
    · exact Or.inl h
    · exact Or.inr h
  rw [mem_dihFour hk] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · left
    group
  · exact Or.inl hz
  · exact hs
  · have e : x * (sr i * zc k) * x⁻¹ = (x * sr i * x⁻¹) * (x * zc k * x⁻¹) := by group
    rw [e, hz]
    rcases hs with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

include hk in
theorem conj_sr_of_not_mem {i : ZMod (2 ^ k)} {x : DihedralGroup (2 ^ k)}
    (hx : x ∈ normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))) (hxV : x ∉ dihFour k i) :
    x * sr i * x⁻¹ = sr i * zc k := by
  rcases conj_of_mem_normalizer hk hx (sr_mem_dihFour i) with h | h
  · exfalso
    apply hxV
    apply mem_dihFour_of_comm hk
    calc x * sr i = (x * sr i * x⁻¹) * x := by group
      _ = sr i * x := by rw [h]
  · exact h

end Four

section Quarter

variable {k : ℕ} (hk : 2 ≤ k)

@[expose] def quarter (k : ℕ) : ZMod (2 ^ k) := ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k))

include hk in
theorem quarter_ne_zero : quarter k ≠ 0 := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  intro h
  have hv := congrArg ZMod.val h
  rw [quarter, ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    ZMod.val_zero] at hv
  exact absurd hv (by positivity)

include hk in
theorem quarter_ne_half : quarter k ≠ ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  intro h
  have hv := congrArg ZMod.val h
  rw [quarter, ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))] at hv
  have := Nat.pow_right_injective (le_refl 2) hv
  omega

include hk in
theorem sr_quarter_mem_normalizer (i : ZMod (2 ^ k)) :
    sr (i + quarter k) ∈ normalizer (dihFour k i : Set (DihedralGroup (2 ^ k))) := by
  have hk1 : 1 ≤ k := by omega
  refine mem_normalizer_of_involution (sr_mul_self _) fun v hv => ?_
  rw [mem_dihFour hk1] at hv ⊢
  have hs : sr (i + quarter k) * sr i * (sr (i + quarter k))⁻¹ = sr i * zc k := by
    rw [inv_sr, sr_mul_sr, r_mul_sr, zc_eq_r hk1, sr_mul_r, ← quarter_add_quarter hk, quarter]
    congr 1
    ring
  have hz : sr (i + quarter k) * zc k * (sr (i + quarter k))⁻¹ = zc k := by
    rw [zc_comm hk1, mul_inv_cancel_right]
  rcases hv with rfl | rfl | rfl | rfl
  · left
    group
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr (Or.inr hs))
  · right; right; left
    have e : sr (i + quarter k) * (sr i * zc k) * (sr (i + quarter k))⁻¹ =
        (sr (i + quarter k) * sr i * (sr (i + quarter k))⁻¹) *
          (sr (i + quarter k) * zc k * (sr (i + quarter k))⁻¹) := by group
    rw [e, hs, hz, mul_assoc, zc_mul_self hk1, mul_one]

include hk in
theorem sr_quarter_not_mem (i : ZMod (2 ^ k)) : sr (i + quarter k) ∉ dihFour k i := by
  have hk1 : 1 ≤ k := by omega
  rw [mem_dihFour hk1]
  rintro (h | h | h | h)
  · exact sr_ne_one' _ h
  · exact sr_ne_zc hk1 _ h
  · exact quarter_ne_zero hk (by have := sr.inj h; linear_combination this)
  · rw [zc_eq_r hk1, sr_mul_r] at h
    exact quarter_ne_half hk (by have := sr.inj h; linear_combination this)

include hk in
theorem card_normalizer_dihFour (i : ZMod (2 ^ k)) :
    Nat.card (normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))) = 8 := by
  have hk1 : 1 ≤ k := by omega
  set N := normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))
  set V := dihFour k i
  have hVN : V ≤ N := le_normalizer
  have hd := sr_quarter_mem_normalizer hk i
  have hdV := sr_quarter_not_mem hk i
  have hdvd : V.relIndex N ∣ 2 := by
    rw [relIndex_dvd_two_iff']
    refine ⟨_, hd, fun b hb => ?_⟩
    by_cases hbV : b ∈ V
    · exact Or.inr hbV
    · left
      have h1 := conj_sr_of_not_mem hk1 hb hbV
      have h2 := conj_sr_of_not_mem hk1 hd hdV
      apply mem_dihFour_of_comm hk1
      have h3 : (sr (i + quarter k) * b) * sr i * (sr (i + quarter k) * b)⁻¹ = sr i := by
        calc (sr (i + quarter k) * b) * sr i * (sr (i + quarter k) * b)⁻¹
            = sr (i + quarter k) * (b * sr i * b⁻¹) * (sr (i + quarter k))⁻¹ := by group
          _ = (sr (i + quarter k) * sr i * (sr (i + quarter k))⁻¹) *
              (sr (i + quarter k) * zc k * (sr (i + quarter k))⁻¹) := by rw [h1]; group
          _ = sr i := by
              have hz : sr (i + quarter k) * zc k * (sr (i + quarter k))⁻¹ = zc k := by
                rw [zc_comm hk1, mul_inv_cancel_right]
              rw [h2, hz, mul_assoc, zc_mul_self hk1, mul_one]
      calc sr (i + quarter k) * b * sr i =
          ((sr (i + quarter k) * b) * sr i * (sr (i + quarter k) * b)⁻¹) *
            (sr (i + quarter k) * b) := by group
        _ = sr i * (sr (i + quarter k) * b) := by rw [h3]
  have hne : V.relIndex N ≠ 1 := by
    intro h1
    rw [relIndex_eq_one] at h1
    exact hdV (h1 hd)
  have h2 : V.relIndex N = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have hcard := relIndex_mul_card (H := V) (K := N)
  rw [h2, inf_of_le_left hVN, card_dihFour hk1] at hcard
  omega

theorem nonempty_dihedralFour_of_card {R : Type*} [Group R] (h8 : Nat.card R = 8) {s t : R}
    (hs : s * s = 1) (ht : t * t = 1) (hst : orderOf (s * t) = 4) :
    Nonempty (DihedralGroup 4 ≃* R) := by
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [one_mul] at hst
    have := orderOf_dvd_of_pow_eq_one (show t ^ 2 = 1 by rw [pow_two]; exact ht)
    rw [hst] at this
    norm_num at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at hst
    have := orderOf_dvd_of_pow_eq_one (show s ^ 2 = 1 by rw [pow_two]; exact hs)
    rw [hst] at this
    norm_num at this
  refine TauCeti.nonempty_dihedralGroup_mulEquiv hs ht hs1 ht1 hst ?_
  set K := closure ({s, t} : Set R)
  have hz : zpowers (s * t) ≤ K :=
    zpowers_le.2 (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
  have hsK : s ∈ K := subset_closure (by simp)
  have h4 : 4 ∣ Nat.card K := by
    have := card_dvd_of_le hz
    rwa [Nat.card_zpowers, hst] at this
  have h8' : Nat.card K ∣ 8 := h8 ▸ card_subgroup_dvd_card K
  have hne : Nat.card K ≠ 4 := by
    intro h
    have heq : zpowers (s * t) = K := eq_of_le_of_card_ge hz (by rw [h, Nat.card_zpowers, hst])
    have hsz : s ∈ zpowers (s * t) := heq ▸ hsK
    have htz : t ∈ zpowers (s * t) := by
      have := mul_mem (inv_mem hsz) (mem_zpowers (s * t))
      rwa [inv_mul_cancel_left] at this
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 hsz
    obtain ⟨b, hb⟩ := mem_zpowers_iff.1 htz
    have hcomm : s * t = t * s := by
      have := (Commute.zpow_zpow_self (s * t) a b).eq
      rwa [ha, hb] at this
    have hsq : (s * t) ^ 2 = 1 := by
      calc (s * t) ^ 2 = s * (t * s) * t := by rw [pow_two]; group
        _ = s * (s * t) * t := by rw [hcomm]
        _ = (s * s) * (t * t) := by group
        _ = 1 := by rw [hs, ht, one_mul]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hst] at this
    norm_num at this
  have hK : Nat.card K = 8 := by
    have hmem : Nat.card K ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨h8', by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [h] at h4; norm_num at h4
    · rw [h] at h4; norm_num at h4
    · exact absurd h hne
    · exact h
  exact eq_top_of_card_eq K (by rw [hK, h8])

include hk in
theorem nonempty_normalizer_dihFour_equiv (i : ZMod (2 ^ k)) :
    Nonempty (DihedralGroup 4 ≃* normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))) := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  set N := normalizer (dihFour k i : Set (DihedralGroup (2 ^ k)))
  have hsN : sr i ∈ N := le_normalizer (sr_mem_dihFour i)
  have hdN := sr_quarter_mem_normalizer hk i
  refine nonempty_dihedralFour_of_card (card_normalizer_dihFour hk i) (s := ⟨sr i, hsN⟩)
    (t := ⟨sr (i + quarter k), hdN⟩) (Subtype.ext (sr_mul_self _)) (Subtype.ext (sr_mul_self _))
    ?_
  rw [← orderOf_injective N.subtype N.subtype_injective]
  show orderOf (sr i * sr (i + quarter k)) = 4
  rw [sr_mul_sr, show i + quarter k - i = quarter k by ring, orderOf_r, quarter,
    ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)),
    Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega)), Nat.pow_div (by omega) (by norm_num),
    show k - (k - 2) = 2 by omega]

end Quarter

end CFSG.CGT.Foote81L6.TStruct
