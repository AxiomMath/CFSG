module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4S1
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step410
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup Q47 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

variable {G : Type} [Group G]

structure VCode (Q : Subgroup G) (z : G) where
  rep : Fin 64 → G
  rep_mem : ∀ v, rep v ∈ Q
  rep_zero : rep 0 = 1
  rep_mul : ∀ u v, rep u * rep v = rep (xr u v) ∨ rep u * rep v = rep (xr u v) * z
  cover : ∀ x ∈ Q, ∃ v, x = rep v ∨ x = rep v * z
  sq : ∀ v, (rep v * rep v = 1 ∧ qv v = 0) ∨ (rep v * rep v = z ∧ qv v = 1)

namespace VCode

variable {Q : Subgroup G} {z : G} (c : VCode Q z)

structure Std (Q : Subgroup G) (z : G) : Prop where
  z_mem : z ∈ Q
  z_comm : ∀ x ∈ Q, x * z = z * x
  z_sq : z * z = 1
  z_ne : z ≠ 1
  card : Nat.card Q = 128
  comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z
  norm_cent : normalizer (Q : Set G) ≤ centralizer ({z} : Set G)

variable {c}

theorem mem_zpowers_iff (hs : Std Q z) {x : G} : x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hs.z_sq) hs.z_ne
  constructor
  · exact eq_one_or_eq_of_mem_zpowers hz2
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem eq_of_rep (hs : Std Q z) {u v : Fin 64} {a b : Bool}
    (h : c.rep u * (if a then z else 1) = c.rep v * (if b then z else 1)) : u = v ∧ a = b := by
  let φ : Fin 64 × Bool → ↥Q := fun p =>
    ⟨c.rep p.1 * (if p.2 then z else 1), Q.mul_mem (c.rep_mem _) (by
      split_ifs
      · exact hs.z_mem
      · exact one_mem _)⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv | hv⟩ := c.cover x hx
    · exact ⟨(v, false), Subtype.ext (by simp [φ, hv])⟩
    · exact ⟨(v, true), Subtype.ext (by simp [φ, hv])⟩
  have hinj : Function.Injective φ := by
    have hcard : Nat.card (Fin 64 × Bool) ≤ Nat.card ↥Q := by
      rw [hs.card, Nat.card_eq_fintype_card]
      simp
    exact (Function.Surjective.bijective_of_nat_card_le hsurj hcard).1
  have := @hinj (u, a) (v, b) (Subtype.ext h)
  simp only [Prod.mk.injEq] at this
  exact this

theorem rep_inj (hs : Std Q z) {u v : Fin 64} (h : c.rep u = c.rep v) : u = v :=
  (eq_of_rep hs (a := false) (b := false) (by simpa using h)).1

theorem rep_mul_z_inj (hs : Std Q z) {u v : Fin 64} (h : c.rep u * z = c.rep v * z) : u = v :=
  (eq_of_rep hs (a := true) (b := true) (by simpa using h)).1

theorem rep_ne_mul_z (hs : Std Q z) (u v : Fin 64) : c.rep u ≠ c.rep v * z := fun h => by
  have := (eq_of_rep hs (a := false) (b := true) (by simpa using h)).2
  exact absurd this (by decide)

open scoped Classical in
@[expose] noncomputable def code (c : VCode Q z) (x : G) : Fin 64 :=
  if h : x ∈ Q then (c.cover x h).choose else 0

theorem code_spec {x : G} (hx : x ∈ Q) :
    x = c.rep (c.code x) ∨ x = c.rep (c.code x) * z := by
  classical
  have : c.code x = (c.cover x hx).choose := by
    unfold code
    split
    · rfl
    · contradiction
  rw [this]
  exact (c.cover x hx).choose_spec

theorem code_eq (hs : Std Q z) {x : G} {v : Fin 64} (h : x = c.rep v ∨ x = c.rep v * z) :
    c.code x = v := by
  have hx : x ∈ Q := by
    rcases h with rfl | rfl
    · exact c.rep_mem v
    · exact Q.mul_mem (c.rep_mem v) hs.z_mem
  rcases h with h | h <;> rcases code_spec (c := c) hx with h1 | h1
  · exact rep_inj hs (h1.symm.trans h)
  · exact absurd (h.symm.trans h1) (rep_ne_mul_z hs _ _)
  · exact absurd (h1.symm.trans h) (rep_ne_mul_z hs _ _)
  · exact rep_mul_z_inj hs (h1.symm.trans h)

theorem code_rep (hs : Std Q z) (v : Fin 64) : c.code (c.rep v) = v :=
  code_eq hs (Or.inl rfl)

theorem code_mul_z (hs : Std Q z) {x : G} (hx : x ∈ Q) : c.code (x * z) = c.code x := by
  have h1 := code_spec (c := c) hx
  generalize c.code x = u at h1 ⊢
  refine code_eq hs ?_
  rcases h1 with rfl | rfl
  · exact Or.inr rfl
  · left
    rw [mul_assoc, hs.z_sq, mul_one]

theorem code_z (hs : Std Q z) : c.code z = 0 := code_eq hs (Or.inr (by rw [c.rep_zero, one_mul]))

theorem code_mul (hs : Std Q z) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    c.code (x * y) = xr (c.code x) (c.code y) := by
  have hzc := hs.z_comm
  have h1 := code_spec (c := c) hx
  have h2 := code_spec (c := c) hy
  generalize c.code x = u at h1 ⊢
  generalize c.code y = w at h2 ⊢
  refine code_eq hs ?_
  have hz' : ∀ a : G, a ∈ Q → a * z * z = a := fun a _ => by rw [mul_assoc, hs.z_sq, mul_one]
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases c.rep_mul u w with h3 | h3
  · exact Or.inl h3
  · exact Or.inr h3
  · right
    rw [← mul_assoc, h3]
  · left
    rw [← mul_assoc, h3, hz' _ (c.rep_mem _)]
  · right
    rw [mul_assoc, ← hzc _ (c.rep_mem _), ← mul_assoc, h3]
  · left
    rw [mul_assoc, ← hzc _ (c.rep_mem _), ← mul_assoc, h3, hz' _ (c.rep_mem _)]
  · left
    rw [show c.rep u * z * (c.rep w * z) = c.rep u * c.rep w from by
      calc c.rep u * z * (c.rep w * z) = c.rep u * (z * c.rep w) * z := by simp only [mul_assoc]
        _ = c.rep u * (c.rep w * z) * z := by rw [← hzc _ (c.rep_mem w)]
        _ = c.rep u * c.rep w * (z * z) := by simp only [mul_assoc]
        _ = c.rep u * c.rep w := by rw [hs.z_sq, mul_one], h3]
  · right
    rw [show c.rep u * z * (c.rep w * z) = c.rep u * c.rep w from by
      calc c.rep u * z * (c.rep w * z) = c.rep u * (z * c.rep w) * z := by simp only [mul_assoc]
        _ = c.rep u * (c.rep w * z) * z := by rw [← hzc _ (c.rep_mem w)]
        _ = c.rep u * c.rep w * (z * z) := by simp only [mul_assoc]
        _ = c.rep u * c.rep w := by rw [hs.z_sq, mul_one], h3]

theorem code_inv (hs : Std Q z) {x : G} (hx : x ∈ Q) : c.code x⁻¹ = c.code x := by
  have h := code_mul (c := c) hs (Q.inv_mem hx) hx
  rw [inv_mul_cancel, show (1 : G) = c.rep 0 from c.rep_zero.symm, code_rep hs] at h
  rw [← xr_xr_cancel (c.code x⁻¹) (c.code x), ← h, xr_comm, xr_zero]

theorem code_eq_zero_iff (hs : Std Q z) {x : G} (hx : x ∈ Q) :
    c.code x = 0 ↔ x ∈ zpowers z := by
  rw [mem_zpowers_iff hs]
  constructor
  · intro h
    rcases code_spec (c := c) hx with h1 | h1 <;> rw [h, c.rep_zero] at h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1, one_mul])
  · rintro (rfl | rfl)
    · rw [show (1 : G) = c.rep 0 from c.rep_zero.symm, code_rep hs]
    · exact code_z hs

theorem rep_sq (v : Fin 64) : c.rep v * c.rep v = z ^ qv v := by
  rcases c.sq v with ⟨h, hq⟩ | ⟨h, hq⟩
  · rw [h, hq, pow_zero]
  · rw [h, hq, pow_one]

theorem qv_eq_zero_or_one (c : VCode Q z) (v : Fin 64) : qv v = 0 ∨ qv v = 1 := by
  rcases c.sq v with ⟨-, hq⟩ | ⟨-, hq⟩
  exacts [Or.inl hq, Or.inr hq]

theorem zp_comm (hs : Std Q z) {w : G} (hw : w ∈ zpowers z) {x : G} (hx : x ∈ Q) :
    Commute x w := by
  rcases (mem_zpowers_iff hs).1 hw with rfl | rfl
  · exact Commute.one_right x
  · exact hs.z_comm x hx

theorem zp_mul_self (hs : Std Q z) {w : G} (hw : w ∈ zpowers z) : w * w = 1 := by
  rcases (mem_zpowers_iff hs).1 hw with rfl | rfl
  · rw [mul_one]
  · exact hs.z_sq

theorem orderOf_z (hs : Std Q z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [_root_.sq]; exact hs.z_sq) hs.z_ne

theorem pow_mod_two (hs : Std Q z) (m : ℕ) : z ^ (m % 2) = z ^ m := by
  rw [← orderOf_z hs]
  exact pow_mod_orderOf z m

theorem exists_rep_xr (hs : Std Q z) (u v : Fin 64) :
    ∃ w ∈ zpowers z, c.rep (xr u v) = c.rep u * c.rep v * w := by
  rcases c.rep_mul u v with h | h
  · exact ⟨1, one_mem _, by rw [h, mul_one]⟩
  · exact ⟨z, mem_zpowers z, by rw [h, mul_assoc, hs.z_sq, mul_one]⟩

theorem bilin_comm (a b : ℕ) : bilin a b = bilin b a := by
  unfold bilin
  rw [Nat.xor_comm]
  omega

theorem comm_rep (hs : Std Q z) (u v : Fin 64) :
    c.rep u * c.rep v * (c.rep u)⁻¹ * (c.rep v)⁻¹ = z ^ bilin u.val v.val := by
  have hx := c.rep_mem u
  have hy := c.rep_mem v
  obtain ⟨w, hw, hr⟩ := exists_rep_xr hs u v
  have h5 := c.rep_sq (xr u v)
  rw [hr] at h5
  set x := c.rep u with hxdef
  set y := c.rep v with hydef
  set k := x * y * x⁻¹ * y⁻¹ with hk
  have hkz : k ∈ zpowers z := hs.comm x hx y hy
  have hkk := zp_mul_self hs hkz
  have h1 : x * y = k * (y * x) := by rw [hk]; group
  have h2 : y * x = k * (x * y) := by rw [h1, ← mul_assoc, hkk, one_mul]
  have h3 : (x * y) * (x * y) = k * ((x * x) * (y * y)) := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (k * (x * y)) * y := by rw [h2]
      _ = (x * k) * (x * y) * y := by group
      _ = (k * x) * (x * y) * y := by rw [(zp_comm hs hkz hx).eq]
      _ = k * ((x * x) * (y * y)) := by group
  have hxyQ : x * y ∈ Q := Q.mul_mem hx hy
  have h4 : (x * y * w) * (x * y * w) = (x * y) * (x * y) := by
    calc (x * y * w) * (x * y * w) = x * y * (w * (x * y)) * w := by group
      _ = x * y * ((x * y) * w) * w := by rw [(zp_comm hs hw hxyQ).eq]
      _ = (x * y) * (x * y) * (w * w) := by group
      _ = (x * y) * (x * y) := by rw [zp_mul_self hs hw, mul_one]
  rw [h4, h3, hxdef, hydef, c.rep_sq, c.rep_sq] at h5
  have hzz : ∀ m : ℕ, z ^ m * z ^ m = 1 := fun m => by
    rw [← pow_add, ← two_mul, pow_mul, _root_.sq, hs.z_sq, one_pow]
  have h6 : k = z ^ qv (xr u v) * z ^ (qv u + qv v) := by
    rw [← h5, ← pow_add, mul_assoc, hzz, mul_one]
  have hb : bilin u.val v.val = (qv (xr u v) + (qv u + qv v)) % 2 := by
    simp only [bilin, qv, xr_val, add_assoc]
  rw [hb, pow_mod_two hs, pow_add, ← h6]

theorem delta_mul (hs : Std Q z) {n : G} (hn : Commute n z)
    (hδ : ∀ v, n * c.rep v * n⁻¹ * (c.rep v)⁻¹ ∈ zpowers z) (u v : Fin 64) :
    n * c.rep (xr u v) * n⁻¹ * (c.rep (xr u v))⁻¹ =
      (n * c.rep u * n⁻¹ * (c.rep u)⁻¹) * (n * c.rep v * n⁻¹ * (c.rep v)⁻¹) := by
  obtain ⟨w, hw, hr⟩ := exists_rep_xr hs u v
  have hdva : Commute (c.rep u) (n * c.rep v * n⁻¹ * (c.rep v)⁻¹) :=
    zp_comm hs (hδ v) (c.rep_mem u)
  have hnw : Commute n w := by
    rcases (mem_zpowers_iff hs).1 hw with h | h <;> rw [h]
    · exact Commute.one_right n
    · exact hn
  set a := c.rep u
  set b := c.rep v
  set du := n * a * n⁻¹ * a⁻¹ with hdu
  set dv := n * b * n⁻¹ * b⁻¹ with hdv
  have ea : n * a * n⁻¹ = du * a := by rw [hdu]; group
  have eb : n * b * n⁻¹ = dv * b := by rw [hdv]; group
  rw [hr]
  have e : n * (a * b * w) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) * w := by
    calc n * (a * b * w) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹) * (n * w * n⁻¹) := by group
      _ = n * a * n⁻¹ * (n * b * n⁻¹) * w := by rw [hnw.eq, mul_inv_cancel_right]
  rw [e, ea, eb]
  calc du * a * (dv * b) * w * (a * b * w)⁻¹ = du * (a * dv) * b * w * (a * b * w)⁻¹ := by
        group
    _ = du * (dv * a) * b * w * (a * b * w)⁻¹ := by rw [hdva.eq]
    _ = du * dv := by group

theorem eq_of_char {δ γ : Fin 64 → G} (hδ : ∀ u v, δ (xr u v) = δ u * δ v)
    (hγ : ∀ u v, γ (xr u v) = γ u * γ v) (h : ∀ i, δ (bv i) = γ (bv i)) : δ = γ := by
  have h0 : ∀ ε : Fin 64 → G, (∀ u v, ε (xr u v) = ε u * ε v) → ε 0 = 1 := fun ε hε => by
    have h1 := hε 0 0
    rw [xr_self] at h1
    have h2 : ε 0 * ε 0 = ε 0 * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  funext v
  induction hn : v.val using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    subst hn
    by_cases hv0 : v.val = 0
    · rw [show v = 0 from Fin.ext hv0, h0 δ hδ, h0 γ hγ]
    · obtain ⟨i, -, hlt⟩ := exists_bit_lt 6 v (by simp) hv0
      have hlt' : (xr v (bv i)).val < v.val := by
        rw [xr_val, bv_val]
        exact hlt
      rw [← xr_xr_cancel v (bv i), hδ, hγ, ih _ hlt' (xr v (bv i)) rfl, h i]

theorem exists_bits (b : Fin 6 → Bool) :
    ∃ m < 64, ∀ i : Fin 6, (m >>> i.val) % 2 = (b i).toNat := by
  have key : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ i : Fin 6,
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat +
        32 * b5.toNat) >>> i.val) % 2 = (![b0, b1, b2, b3, b4, b5] i).toNat := by decide
  have hle : ∀ x : Bool, x.toNat ≤ 1 := by decide
  refine ⟨(b 0).toNat + 2 * (b 1).toNat + 4 * (b 2).toNat + 8 * (b 3).toNat +
    16 * (b 4).toNat + 32 * (b 5).toNat, ?_, fun i => ?_⟩
  · have := hle (b 0); have := hle (b 1); have := hle (b 2); have := hle (b 3)
    have := hle (b 4); have := hle (b 5)
    omega
  · rw [key]
    fin_cases i <;> rfl

theorem exists_inner (hs : Std Q z) (hnd : nondegCheck = true) {n : G} (hn : Commute n z)
    (hδ : ∀ v, n * c.rep v * n⁻¹ * (c.rep v)⁻¹ ∈ zpowers z) :
    ∃ w, (c.rep w)⁻¹ * n ∈ centralizer (Q : Set G) := by
  classical
  set δ : Fin 64 → G := fun v => n * c.rep v * n⁻¹ * (c.rep v)⁻¹ with hδdef
  obtain ⟨m, hm, hbits⟩ := exists_bits fun i => decide (δ (bv i) = z)
  have hnd' := List.all_eq_true.1 hnd m (List.mem_range.2 hm)
  rw [List.any_eq_true] at hnd'
  obtain ⟨u, hu, hu'⟩ := hnd'
  have hu64 : u < 64 := List.mem_range.1 hu
  set w : Fin 64 := ⟨u, hu64⟩ with hwdef
  set γ : Fin 64 → G := fun v => c.rep w * c.rep v * (c.rep w)⁻¹ * (c.rep v)⁻¹ with hγdef
  have hγz : ∀ v, γ v ∈ zpowers z := fun v => hs.comm _ (c.rep_mem w) _ (c.rep_mem v)
  have hγ : ∀ a b, γ (xr a b) = γ a * γ b := delta_mul hs (hs.z_comm _ (c.rep_mem w)) hγz
  have hδm : ∀ a b, δ (xr a b) = δ a * δ b := delta_mul hs hn hδ
  have heq : δ = γ := by
    refine eq_of_char hδm hγ fun i => ?_
    have hi := List.all_eq_true.1 hu' i.val (List.mem_range.2 i.2)
    rw [beq_iff_eq] at hi
    have hγi : γ (bv i) = z ^ bilin u (2 ^ i.val) := comm_rep hs w (bv i)
    rw [hγi, bilin_comm, hi, hbits i]
    by_cases h : δ (bv i) = z
    · rw [decide_eq_true h, h, Bool.toNat_true, pow_one]
    · rw [decide_eq_false h, Bool.toNat_false, pow_zero]
      rcases (mem_zpowers_iff hs).1 (hδ (bv i)) with h1 | h1
      · exact h1
      · exact absurd h1 h
  refine ⟨w, mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hmv : ∀ v, Commute ((c.rep w)⁻¹ * n) (c.rep v) := by
    intro v
    have h1 : n * c.rep v * n⁻¹ = δ v * c.rep v := by simp only [hδdef]; group
    have h2 : δ v = γ v := congrFun heq v
    have h3 : γ v * c.rep v = c.rep w * c.rep v * (c.rep w)⁻¹ := by simp only [hγdef]; group
    show (c.rep w)⁻¹ * n * c.rep v = c.rep v * ((c.rep w)⁻¹ * n)
    calc (c.rep w)⁻¹ * n * c.rep v = (c.rep w)⁻¹ * (n * c.rep v * n⁻¹) * n := by group
      _ = (c.rep w)⁻¹ * (c.rep w * c.rep v * (c.rep w)⁻¹) * n := by rw [h1, h2, h3]
      _ = c.rep v * ((c.rep w)⁻¹ * n) := by group
  have hmz : Commute ((c.rep w)⁻¹ * n) z :=
    (Commute.inv_left (hs.z_comm _ (c.rep_mem w))).mul_left hn
  obtain ⟨v, rfl | rfl⟩ := c.cover x hx
  · exact (hmv v).eq.symm
  · exact ((hmv v).mul_right hmz).eq.symm

@[expose] noncomputable def act (c : VCode Q z) (n : G) (v : Fin 64) : Fin 64 :=
  c.code (n * c.rep v * n⁻¹)

theorem conj_mem_Q {n : G} (hn : n ∈ normalizer (Q : Set G)) {x : G} (hx : x ∈ Q) :
    n * x * n⁻¹ ∈ Q :=
  (mem_normalizer_iff.mp hn x).mp hx

theorem commute_z (hs : Std Q z) {n : G} (hn : n ∈ normalizer (Q : Set G)) : Commute n z :=
  mem_centralizer_singleton_iff.mp (hs.norm_cent hn)

theorem conj_z (hs : Std Q z) {n : G} (hn : n ∈ normalizer (Q : Set G)) : n * z * n⁻¹ = z := by
  rw [(commute_z hs hn).eq, mul_inv_cancel_right]

theorem act_spec {n : G} (hn : n ∈ normalizer (Q : Set G)) (v : Fin 64) :
    n * c.rep v * n⁻¹ = c.rep (c.act n v) ∨ n * c.rep v * n⁻¹ = c.rep (c.act n v) * z :=
  code_spec (conj_mem_Q hn (c.rep_mem v))

theorem act_eq (hs : Std Q z) {n : G} {v w : Fin 64}
    (h : n * c.rep v * n⁻¹ = c.rep w ∨ n * c.rep v * n⁻¹ = c.rep w * z) : c.act n v = w :=
  code_eq hs h

theorem act_one (hs : Std Q z) (v : Fin 64) : c.act 1 v = v :=
  act_eq hs (Or.inl (by rw [one_mul, inv_one, mul_one]))

theorem act_mul (hs : Std Q z) {n m : G} (hn : n ∈ normalizer (Q : Set G))
    (hm : m ∈ normalizer (Q : Set G)) (v : Fin 64) : c.act (n * m) v = c.act n (c.act m v) := by
  have hnz := conj_z hs hn
  refine act_eq hs ?_
  have e : n * m * c.rep v * (n * m)⁻¹ = n * (m * c.rep v * m⁻¹) * n⁻¹ := by group
  have ez : ∀ w : Fin 64, n * (c.rep w * z) * n⁻¹ = n * c.rep w * n⁻¹ * (n * z * n⁻¹) :=
    fun w => by group
  rw [e]
  rcases act_spec hm v with h | h <;> rw [h] <;> rcases act_spec hn (c.act m v) with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · exact Or.inr (by rw [ez, hnz, h'])
  · exact Or.inl (by rw [ez, hnz, h', mul_assoc, hs.z_sq, mul_one])

@[expose] noncomputable def rho (c : VCode Q z) (hs : Std Q z) :
    ↥(normalizer (Q : Set G)) →* Equiv.Perm (Fin 64) where
  toFun n :=
    { toFun := c.act n
      invFun := c.act (n : G)⁻¹
      left_inv := fun v => by
        rw [← act_mul hs (inv_mem n.2) n.2, inv_mul_cancel, act_one hs]
      right_inv := fun v => by
        rw [← act_mul hs n.2 (inv_mem n.2), mul_inv_cancel, act_one hs] }
  map_one' := Equiv.ext fun v => act_one hs v
  map_mul' n m := Equiv.ext fun v => act_mul hs n.2 m.2 v

theorem rho_apply (hs : Std Q z) (n : ↥(normalizer (Q : Set G))) (v : Fin 64) :
    c.rho hs n v = c.act n v := rfl

theorem code_mul_zp (hs : Std Q z) {x w : G} (hx : x ∈ Q) (hw : w ∈ zpowers z) :
    c.code (x * w) = c.code x := by
  rcases (mem_zpowers_iff hs).1 hw with rfl | rfl
  · rw [mul_one]
  · exact code_mul_z hs hx

theorem code_conj (hs : Std Q z) {n : G} (hn : n ∈ normalizer (Q : Set G)) {x : G}
    (hx : x ∈ Q) : c.code (n * x * n⁻¹) = c.act n (c.code x) := by
  have h1 := code_spec (c := c) hx
  generalize c.code x = u at h1 ⊢
  have hQ := conj_mem_Q hn (c.rep_mem u)
  rcases h1 with rfl | rfl
  · rfl
  · rw [show n * (c.rep u * z) * n⁻¹ = n * c.rep u * n⁻¹ * (n * z * n⁻¹) by group, conj_z hs hn,
      code_mul_z hs hQ]
    rfl

theorem rho_mem_oV (hs : Std Q z) (n : ↥(normalizer (Q : Set G))) : c.rho hs n ∈ oV := by
  have hn := n.2
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · show c.act n (xr u v) = xr (c.act n u) (c.act n v)
    obtain ⟨w, hw, hr⟩ := exists_rep_xr hs u v
    have hu := conj_mem_Q hn (c.rep_mem u)
    have hv := conj_mem_Q hn (c.rep_mem v)
    have hnw : (n : G) * w * (n : G)⁻¹ = w := by
      rcases (mem_zpowers_iff hs).1 hw with h | h <;> rw [h]
      · group
      · exact conj_z hs hn
    have e : (n : G) * c.rep (xr u v) * (n : G)⁻¹ =
        ((n : G) * c.rep u * (n : G)⁻¹) * ((n : G) * c.rep v * (n : G)⁻¹) * w := by
      calc (n : G) * c.rep (xr u v) * (n : G)⁻¹ =
            (n : G) * (c.rep u * c.rep v * w) * (n : G)⁻¹ := by rw [hr]
        _ = ((n : G) * c.rep u * (n : G)⁻¹) * ((n : G) * c.rep v * (n : G)⁻¹) *
            ((n : G) * w * (n : G)⁻¹) := by group
        _ = _ := by rw [hnw]
    show c.code _ = xr (c.code _) (c.code _)
    rw [e, code_mul_zp hs (Q.mul_mem hu hv) hw, code_mul hs hu hv]
  · show qv (c.act n v) = qv v
    have hsq : ((n : G) * c.rep v * (n : G)⁻¹) * ((n : G) * c.rep v * (n : G)⁻¹) = z ^ qv v := by
      rw [show (n : G) * c.rep v * (n : G)⁻¹ * ((n : G) * c.rep v * (n : G)⁻¹) =
        (n : G) * (c.rep v * c.rep v) * (n : G)⁻¹ by group, c.rep_sq,
        ((commute_z hs hn).pow_right (qv v)).eq, mul_inv_cancel_right]
    have hsq' : ((n : G) * c.rep v * (n : G)⁻¹) * ((n : G) * c.rep v * (n : G)⁻¹) =
        z ^ qv (c.act n v) := by
      rcases act_spec hn v with h | h <;> rw [h]
      · exact c.rep_sq _
      · rw [← c.rep_sq]
        calc c.rep (c.act n v) * z * (c.rep (c.act n v) * z) =
            c.rep (c.act n v) * (z * c.rep (c.act n v)) * z := by group
          _ = c.rep (c.act n v) * (c.rep (c.act n v) * z) * z := by
            rw [← hs.z_comm _ (c.rep_mem _)]
          _ = c.rep (c.act n v) * c.rep (c.act n v) := by
            rw [mul_assoc, mul_assoc, hs.z_sq, mul_one]
    have h := hsq'.symm.trans hsq
    rcases c.qv_eq_zero_or_one v with h1 | h1 <;>
      rcases c.qv_eq_zero_or_one (c.act n v) with h2 | h2 <;> rw [h1, h2] at h ⊢
    · exact absurd (by simpa using h : z = 1) hs.z_ne
    · exact absurd (by simpa using h.symm : z = 1) hs.z_ne

theorem isPGroup_Q (hs : Std Q z) : IsPGroup 2 Q :=
  IsPGroup.of_card (n := 7) (by rw [hs.card]; norm_num)

theorem oddCoreIn_le_centralizer [Finite G] (hs : Std Q z) :
    AS76b.oddCoreIn (normalizer (Q : Set G)) ≤ centralizer (Q : Set G) :=
  oddCoreIn_le_centralizer_of_isPGroup (isPGroup_Q hs)

theorem rho_eq_one_of_mem [Finite G] (hs : Std Q z) (n : ↥(normalizer (Q : Set G)))
    (h : (n : G) ∈ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) : c.rho hs n = 1 := by
  have hle : Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)) ≤
      (c.rho hs).ker.map (normalizer (Q : Set G)).subtype := by
    refine sup_le (fun q hq => ⟨⟨q, le_normalizer hq⟩, MonoidHom.mem_ker.2 ?_, rfl⟩)
      (fun o ho => ⟨⟨o, AS76b.oddCoreIn_le _ ho⟩, MonoidHom.mem_ker.2 ?_, rfl⟩)
    · refine Equiv.ext fun v => ?_
      show c.act q v = v
      refine act_eq hs ?_
      have e : q * c.rep v * q⁻¹ = (q * c.rep v * q⁻¹ * (c.rep v)⁻¹) * c.rep v := by group
      rcases (mem_zpowers_iff hs).1 (hs.comm q hq (c.rep v) (c.rep_mem v)) with hk | hk <;>
        rw [e, hk]
      · exact Or.inl (one_mul _)
      · exact Or.inr (hs.z_comm _ (c.rep_mem v)).symm
    · refine Equiv.ext fun v => ?_
      show c.act o v = v
      refine act_eq hs (Or.inl ?_)
      have hc := mem_centralizer_iff.mp (oddCoreIn_le_centralizer hs ho) (c.rep v) (c.rep_mem v)
      rw [← hc, mul_inv_cancel_right]
  obtain ⟨k, hk, hkn⟩ := hle h
  have : k = n := Subtype.ext hkn
  rw [← this]
  exact hk

theorem rho_eq_one_iff [Finite G] (hs : Std Q z) (hnd : nondegCheck = true)
    (hcent : centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)))
    (n : ↥(normalizer (Q : Set G))) :
    c.rho hs n = 1 ↔ (n : G) ∈ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)) := by
  refine ⟨fun h => ?_, rho_eq_one_of_mem hs n⟩
  have hfix : ∀ v, c.act n v = v := fun v => congrArg (fun π : Equiv.Perm (Fin 64) => π v) h
  have hδ : ∀ v, (n : G) * c.rep v * (n : G)⁻¹ * (c.rep v)⁻¹ ∈ zpowers z := by
    intro v
    rcases act_spec n.2 v with h1 | h1 <;> rw [hfix] at h1 <;> rw [h1]
    · rw [mul_inv_cancel]
      exact one_mem _
    · rw [hs.z_comm _ (c.rep_mem v), mul_inv_cancel_right]
      exact mem_zpowers z
  obtain ⟨w, hw⟩ := exists_inner hs hnd (commute_z hs n.2) hδ
  rw [show (n : G) = c.rep w * ((c.rep w)⁻¹ * n) by group]
  exact mul_mem (mem_sup_left (c.rep_mem w)) (hcent hw)

theorem ker_rho [Finite G] (hs : Std Q z) (hnd : nondegCheck = true)
    (hcent : centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) :
    (c.rho hs).ker =
      (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf (normalizer (Q : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, rho_eq_one_iff hs hnd hcent, mem_subgroupOf]

structure IsSubsp (S : Set (Fin 64)) : Prop where
  zero : (0 : Fin 64) ∈ S
  xr_mem : ∀ u ∈ S, ∀ v ∈ S, xr u v ∈ S

theorem code_one (hs : Std Q z) : c.code 1 = 0 := by
  rw [show (1 : G) = c.rep 0 from c.rep_zero.symm, code_rep hs]

@[expose] noncomputable def preim (c : VCode Q z) (hs : Std Q z) {S : Set (Fin 64)}
    (hS : IsSubsp S) : Subgroup G where
  carrier := {x | x ∈ Q ∧ c.code x ∈ S}
  mul_mem' {x y} hx hy :=
    ⟨Q.mul_mem hx.1 hy.1, by rw [code_mul hs hx.1 hy.1]; exact hS.xr_mem _ hx.2 _ hy.2⟩
  one_mem' := ⟨Q.one_mem, by rw [code_one hs]; exact hS.zero⟩
  inv_mem' {x} hx := ⟨Q.inv_mem hx.1, by rw [code_inv hs hx.1]; exact hx.2⟩

variable {S T : Set (Fin 64)}

theorem preim_le (hs : Std Q z) (hS : IsSubsp S) : c.preim hs hS ≤ Q := fun _ hx => hx.1

theorem zpowers_le_preim (hs : Std Q z) (hS : IsSubsp S) : zpowers z ≤ c.preim hs hS :=
  zpowers_le.mpr ⟨hs.z_mem, by rw [code_z hs]; exact hS.zero⟩

theorem mem_of_code_eq (hs : Std Q z) {W : Subgroup G} (hzW : zpowers z ≤ W) {x y : G}
    (hx : x ∈ Q) (hyW : y ∈ W) (hy : y ∈ Q) (h : c.code x = c.code y) : x ∈ W := by
  have h0 : c.code (x * y⁻¹) = 0 := by rw [code_mul hs hx (Q.inv_mem hy), code_inv hs hy, h,
    xr_self]
  have hz := (code_eq_zero_iff hs (Q.mul_mem hx (Q.inv_mem hy))).1 h0
  rw [show x = x * y⁻¹ * y by group]
  exact W.mul_mem (hzW hz) hyW

theorem preim_inf (hs : Std Q z) (hS : IsSubsp S) (hT : IsSubsp T)
    (hST : ∀ v ∈ S, v ∈ T → v = 0) : c.preim hs hS ⊓ c.preim hs hT = zpowers z := by
  refine le_antisymm (fun x hx => ?_) (le_inf (zpowers_le_preim hs hS) (zpowers_le_preim hs hT))
  exact (code_eq_zero_iff hs hx.1.1).1 (hST _ hx.1.2 hx.2.2)

theorem preim_sup (hs : Std Q z) (hS : IsSubsp S) (hT : IsSubsp T)
    (hspan : ∀ v, ∃ a ∈ S, ∃ b ∈ T, xr a b = v) : c.preim hs hS ⊔ c.preim hs hT = Q := by
  refine le_antisymm (sup_le (preim_le hs hS) (preim_le hs hT)) (fun x hx => ?_)
  obtain ⟨a, ha, b, hb, hab⟩ := hspan (c.code x)
  have haS : c.rep a ∈ c.preim hs hS := ⟨c.rep_mem a, by rw [code_rep hs]; exact ha⟩
  have hbT : c.rep b ∈ c.preim hs hT := ⟨c.rep_mem b, by rw [code_rep hs]; exact hb⟩
  have hW : zpowers z ≤ c.preim hs hS ⊔ c.preim hs hT :=
    (zpowers_le_preim hs hS).trans le_sup_left
  refine mem_of_code_eq (c := c) hs hW hx (mul_mem (mem_sup_left haS) (mem_sup_right hbT))
    (Q.mul_mem (c.rep_mem a) (c.rep_mem b)) ?_
  rw [code_mul hs (c.rep_mem a) (c.rep_mem b), code_rep hs, code_rep hs, hab]

theorem card_preim [Finite G] (hs : Std Q z) (hS : IsSubsp S) :
    Nat.card (c.preim hs hS) = S.ncard * 2 := by
  let φ : ↥S × Bool → ↥(c.preim hs hS) := fun p =>
    ⟨c.rep p.1 * (if p.2 then z else 1), Q.mul_mem (c.rep_mem _) (by
      split_ifs
      · exact hs.z_mem
      · exact one_mem _), by
      rw [code_mul_zp hs (c.rep_mem _) (by split_ifs <;> simp [mem_zpowers, one_mem]),
        code_rep hs]
      exact p.1.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨u, hu⟩, a⟩ ⟨⟨v, hv⟩, b⟩ h
    have h' := eq_of_rep hs (congrArg Subtype.val h)
    simp only at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rcases code_spec (c := c) hx.1 with h | h
    · exact ⟨(⟨c.code x, hx.2⟩, false), Subtype.ext (by simp [φ, ← h])⟩
    · exact ⟨(⟨c.code x, hx.2⟩, true), Subtype.ext (by simp [φ, ← h])⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

theorem isElemAbelian_preim (hs : Std Q z) (hS : IsSubsp S) (hsing : ∀ v ∈ S, qv v = 0) :
    CFSG.Open.IsElemAbelian 2 (c.preim hs hS) := by
  have hrep : ∀ x ∈ c.preim hs hS, ∃ w ∈ zpowers z, x = c.rep (c.code x) * w := by
    intro x hx
    rcases code_spec (c := c) hx.1 with h | h
    · exact ⟨1, one_mem _, by rw [mul_one]; exact h⟩
    · exact ⟨z, mem_zpowers z, h⟩
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, ea⟩ := hrep x hx
    obtain ⟨b, hb, eb⟩ := hrep y hy
    have hb0 : bilin (c.code x).val (c.code y).val = 0 := by
      have h1 := hsing _ (hS.xr_mem _ hx.2 _ hy.2)
      have h2 := hsing _ hx.2
      have h3 := hsing _ hy.2
      simp only [qv, xr_val] at h1 h2 h3
      simp only [bilin, h1, h2, h3]
    have hc := comm_rep (c := c) hs (c.code x) (c.code y)
    rw [hb0, pow_zero, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    have hxy : Commute (c.rep (c.code x)) (c.rep (c.code y)) := hc
    have hab : Commute a b := by
      rcases (mem_zpowers_iff hs).1 ha with rfl | rfl
      · exact Commute.one_left b
      · exact (zp_comm hs hb hs.z_mem)
    rw [ea, eb]
    exact (Commute.mul_left (hxy.mul_right (zp_comm hs hb (c.rep_mem _)))
      ((zp_comm hs ha (c.rep_mem _)).symm.mul_right hab)).eq
  · obtain ⟨a, ha, ea⟩ := hrep x hx
    have hq := hsing _ hx.2
    rw [ea, _root_.sq]
    calc c.rep (c.code x) * a * (c.rep (c.code x) * a) =
        c.rep (c.code x) * (a * c.rep (c.code x)) * a := by group
      _ = c.rep (c.code x) * (c.rep (c.code x) * a) * a := by
        rw [(zp_comm hs ha (c.rep_mem _)).eq]
      _ = (c.rep (c.code x) * c.rep (c.code x)) * (a * a) := by group
      _ = 1 := by rw [c.rep_sq, hq, pow_zero, zp_mul_self hs ha, mul_one]

theorem mem_normalizer_preim [Finite G] (hs : Std Q z) (hS : IsSubsp S)
    (n : ↥(normalizer (Q : Set G))) (hn : ∀ v ∈ S, c.rho hs n v ∈ S) :
    (n : G) ∈ normalizer (c.preim hs hS : Set G) := by
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ⟨conj_mem_Q n.2 hx.1, by rw [code_conj hs n.2 hx.1]; exact hn _ hx.2⟩

end VCode

end CFSG.ComponentClassification.AS81
