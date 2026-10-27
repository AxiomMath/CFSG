module

public import Certificates.Data.Kernel.SporSch.Co1RankCoord
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

abbrev bitB (v s : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight v s) 1) 1

theorem bitB_eq (v s : ℕ) : bitB v s = v.testBit s := by
  rw [Nat.testBit, bitB]
  change ((v >>> s) &&& 1).beq 1 = (1 &&& v >>> s != 0)
  rw [Nat.land_comm]
  rcases Nat.and_one_is_mod (v >>> s) ▸ Nat.mod_two_eq_zero_or_one (v >>> s) with h | h <;>
    simp [Nat.land_comm, Nat.and_one_is_mod, h]
  all_goals rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem mask_eq (n : ℕ) : mask n = 2 ^ n - 1 := by
  simp [mask, Nat.shiftLeft_eq]

theorem land_mask (x n : ℕ) : Nat.land x (mask n) = x % 2 ^ n := by
  rw [mask_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x n

theorem land_mask_lt (x n : ℕ) : Nat.land x (mask n) < 2 ^ n := by
  rw [land_mask]
  exact Nat.mod_lt _ (by positivity)

section Mon

variable {M : Type*} [Monoid M]

@[expose] def qProd (b : ℕ → M) : ℕ → ℕ → M
  | 0, _ => 1
  | n + 1, v => if bitB v n then qProd b n v * b n else qProd b n v

theorem qProd_congr (b : ℕ → M) : ∀ n {u v : ℕ}, (∀ s < n, u.testBit s = v.testBit s) →
    qProd b n u = qProd b n v
  | 0, _, _, _ => rfl
  | n + 1, u, v, h => by
    rw [qProd, qProd, bitB_eq, bitB_eq, h n (Nat.lt_succ_self n),
      qProd_congr b n fun s hs => h s (Nat.lt_succ_of_lt hs)]

theorem qProd_zero (b : ℕ → M) : ∀ n, qProd b n 0 = 1
  | 0 => rfl
  | n + 1 => by rw [qProd, bitB_eq, Nat.zero_testBit, if_neg (by simp), qProd_zero b n]

theorem qProd_mod (b : ℕ → M) (n v : ℕ) : qProd b n (v % 2 ^ n) = qProd b n v :=
  qProd_congr b n fun s hs => by rw [Nat.testBit_mod_two_pow, decide_eq_true hs, Bool.true_and]

theorem qProd_congr_fun {b b' : ℕ → M} : ∀ n, (∀ s < n, b s = b' s) → ∀ v,
    qProd b n v = qProd b' n v
  | 0, _, _ => rfl
  | n + 1, h, v => by
    rw [qProd, qProd, qProd_congr_fun n (fun s hs => h s (Nat.lt_succ_of_lt hs)) v,
      h n (Nat.lt_succ_self n)]

theorem qProd_map {M' : Type*} [Monoid M'] (f : M →* M') (b : ℕ → M) : ∀ n v,
    f (qProd b n v) = qProd (fun s => f (b s)) n v
  | 0, _ => map_one f
  | n + 1, v => by
    rw [qProd, qProd]
    split
    · rw [map_mul, qProd_map f b n v]
    · exact qProd_map f b n v

end Mon

variable {G : Type*} [Group G]

@[expose] noncomputable def phiR (row : ℕ → ℕ) (n v : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun s acc => nIf(Nat.beq (Nat.land (Nat.shiftRight v s) 1) 1, Nat.xor acc (row s), acc)) n

theorem phi_eq (d PH i v : ℕ) :
    phi d PH i v = phiR (fun s => fld(PH, Nat.mul d (Nat.add (Nat.mul d i) s), mask d)) d v := rfl

section Comm

variable {b : ℕ → G} {d : ℕ} (hc : ∀ s < d, ∀ t < d, b s * b t = b t * b s)
  (hsq : ∀ s < d, b s * b s = 1)
include hc

theorem qProd_comm : ∀ n ≤ d, ∀ v, ∀ t < d, qProd b n v * b t = b t * qProd b n v
  | 0, _, _, _, _ => by simp [qProd]
  | n + 1, hn, v, t, ht => by
    rw [qProd]
    split
    · rw [mul_assoc, hc n (by omega) t ht, ← mul_assoc, qProd_comm n (by omega) v t ht, mul_assoc]
    · exact qProd_comm n (by omega) v t ht

include hsq

theorem qProd_xor : ∀ n ≤ d, ∀ u v, qProd b n (u ^^^ v) = qProd b n u * qProd b n v
  | 0, _, _, _ => by simp [qProd]
  | n + 1, hn, u, v => by
    have ih := qProd_xor n (by omega) u v
    have hcm := qProd_comm hc n (by omega) v n (by omega)
    rw [qProd, qProd, qProd, bitB_eq, bitB_eq, bitB_eq, Nat.testBit_xor, ih]
    cases u.testBit n <;> cases v.testBit n <;> simp only [Bool.xor, Bool.false_bne, Bool.true_bne,
      Bool.not_true, Bool.not_false, Bool.bne_false, if_true, if_false, Bool.false_eq_true]
    all_goals first
      | rfl
      | (simp only [mul_assoc]; done)
      | rw [hsq n (by omega), mul_one]
      | rw [mul_assoc, hcm, mul_assoc]
      | (simp only [mul_assoc]; rw [hcm, ← mul_assoc (b n), hsq n (by omega), one_mul])

theorem qProd_xor' (u v : ℕ) : qProd b d (Nat.xor u v) = qProd b d u * qProd b d v :=
  qProd_xor hc hsq d le_rfl u v

theorem qProd_mul_self (v : ℕ) : qProd b d v * qProd b d v = 1 := by
  rw [← qProd_xor hc hsq d le_rfl, Nat.xor_self, qProd_zero]

theorem qProd_inv (v : ℕ) : (qProd b d v)⁻¹ = qProd b d v :=
  inv_eq_of_mul_eq_one_right (qProd_mul_self hc hsq v)

theorem conj_qProd {w : G} {row : ℕ → ℕ} (hrow : ∀ s < d, w * b s * w⁻¹ = qProd b d (row s)) :
    ∀ n ≤ d, ∀ v, w * qProd b n v * w⁻¹ = qProd b d (phiR row n v)
  | 0, _, _ => by simp [qProd, phiR, qProd_zero]
  | n + 1, hn, v => by
    have ih := conj_qProd hrow n (by omega) v
    change w * qProd b (n + 1) v * w⁻¹ =
      qProd b d (nIf(Nat.beq (Nat.land (Nat.shiftRight v n) 1) 1, Nat.xor (phiR row n v) (row n),
        phiR row n v))
    rw [qProd]
    change _ = qProd b d (Bool.rec (motive := fun _ => ℕ) _ _ (bitB v n))
    cases bitB v n
    · simpa using ih
    · change w * (qProd b n v * b n) * w⁻¹ = qProd b d (phiR row n v ^^^ row n)
      rw [qProd_xor hc hsq d le_rfl, ← ih, ← hrow n (by omega)]
      group

end Comm

@[expose] def el (d : ℕ) (b w : ℕ → G) (x : ℕ) : G := qProd b d x * w (x >>> d)

structure Model (C : Dat) (b w : ℕ → G) : Prop where
  comm : ∀ s < C.d, ∀ t < C.d, b s * b t = b t * b s
  sq : ∀ s < C.d, b s * b s = 1
  row : ∀ i < 128, ∀ s < C.d,
    w i * b s * (w i)⁻¹ = qProd b C.d (fld(C.PHt, Nat.mul C.d (Nat.add (Nat.mul C.d i) s), mask C.d))
  cocycle : ∀ i < 128, ∀ j < 128, w i * w j = qProd b C.d (nc C.d C.NCt i j) * w (kt C.Kt i j)

theorem phiR_lt {d : ℕ} (row : ℕ → ℕ) (hr : ∀ s, row s < 2 ^ d) : ∀ n v, phiR row n v < 2 ^ d
  | 0, _ => by simp [phiR]
  | n + 1, v => by
    change Bool.rec (motive := fun _ => ℕ) (phiR row n v) (Nat.xor (phiR row n v) (row n))
      (bitB v n) < 2 ^ d
    cases bitB v n
    · exact phiR_lt row hr n v
    · exact Nat.xor_lt_two_pow (phiR_lt row hr n v) (hr n)

theorem phi_lt (d PH i v : ℕ) : phi d PH i v < 2 ^ d := by
  rw [phi_eq]
  exact phiR_lt _ (fun s => land_mask_lt _ _) d v

theorem kt_lt (KT i j : ℕ) : kt KT i j < 128 := by
  have := land_mask_lt (Nat.shiftRight KT (Nat.mul 7 (Nat.add (Nat.mul 128 i) j))) 7
  rw [mask_eq] at this
  exact this

theorem nc_lt (d NC i j : ℕ) : nc d NC i j < 2 ^ d := land_mask_lt _ _

theorem lo_lt (C : Dat) (x y i j : ℕ) :
    Nat.xor (Nat.xor (Nat.land x (mask C.d)) (phi C.d C.PHt i (Nat.land y (mask C.d))))
      (nc C.d C.NCt i j) < 2 ^ C.d :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (land_mask_lt _ _) (phi_lt _ _ _ _)) (nc_lt _ _ _ _)

theorem mulC_eq (C : Dat) (x y : ℕ) : mulC C x y = kt C.Kt (x >>> C.d) (y >>> C.d) * 2 ^ C.d +
    Nat.xor (Nat.xor (Nat.land x (mask C.d)) (phi C.d C.PHt (x >>> C.d) (Nat.land y (mask C.d))))
      (nc C.d C.NCt (x >>> C.d) (y >>> C.d)) := by
  rw [mulC, strictN_eq, strictN_eq]
  change (_ <<< C.d) ||| _ = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (lo_lt C x y _ _), Nat.shiftLeft_eq]
  rfl

theorem shiftRight_lt {x d : ℕ} (hx : x < 2 ^ (d + 7)) : x >>> d < 128 := by
  rw [Nat.shiftRight_eq_div_pow]
  refine Nat.div_lt_of_lt_mul ?_
  rw [pow_add] at hx
  exact hx

theorem mulC_lt (C : Dat) (x y : ℕ) : mulC C x y < 2 ^ (C.d + 7) := by
  have h1 := kt_lt C.Kt (x >>> C.d) (y >>> C.d)
  have h2 := lo_lt C x y (x >>> C.d) (y >>> C.d)
  rw [mulC_eq]
  calc _ < kt C.Kt (x >>> C.d) (y >>> C.d) * 2 ^ C.d + 2 ^ C.d := Nat.add_lt_add_left h2 _
    _ = (kt C.Kt (x >>> C.d) (y >>> C.d) + 1) * 2 ^ C.d := (Nat.succ_mul _ _).symm
    _ ≤ 128 * 2 ^ C.d := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (C.d + 7) := by rw [pow_add, Nat.mul_comm]; rfl

theorem el_split (d : ℕ) (b w : ℕ → G) (k lo : ℕ) (hlo : lo < 2 ^ d) :
    el d b w (k * 2 ^ d + lo) = qProd b d lo * w k := by
  have hdiv : (k * 2 ^ d + lo) >>> d = k := by
    rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos d),
      Nat.div_eq_of_lt hlo, zero_add]
  rw [el, hdiv, ← qProd_mod b d, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo]

theorem el_mulC {C : Dat} {b w : ℕ → G} (hM : Model C b w) {x y : ℕ} (hx : x < 2 ^ (C.d + 7))
    (hy : y < 2 ^ (C.d + 7)) : el C.d b w (mulC C x y) = el C.d b w x * el C.d b w y := by
  have hi := shiftRight_lt hx
  have hj := shiftRight_lt hy
  have hqx : qProd b C.d x = qProd b C.d (Nat.land x (mask C.d)) := by rw [land_mask, qProd_mod]
  have hqy : qProd b C.d y = qProd b C.d (Nat.land y (mask C.d)) := by rw [land_mask, qProd_mod]
  have hφ : qProd b C.d (phi C.d C.PHt (x >>> C.d) (Nat.land y (mask C.d))) =
      w (x >>> C.d) * qProd b C.d (Nat.land y (mask C.d)) * (w (x >>> C.d))⁻¹ := by
    rw [phi_eq, ← conj_qProd hM.comm hM.sq (hM.row _ hi) _ le_rfl]
  have hw : (w (x >>> C.d))⁻¹ * (qProd b C.d (nc C.d C.NCt (x >>> C.d) (y >>> C.d)) *
      w (kt C.Kt (x >>> C.d) (y >>> C.d))) = w (y >>> C.d) := by
    rw [← hM.cocycle _ hi _ hj]
    group
  rw [mulC_eq, el_split _ _ _ _ _ (lo_lt C x y _ _), qProd_xor' hM.comm hM.sq,
    qProd_xor' hM.comm hM.sq, hφ, el, el, hqx, hqy, ← hw]
  group

theorem qProd_inj {b : ℕ → G} {d : ℕ} (hc : ∀ s < d, ∀ t < d, b s * b t = b t * b s)
    (hsq : ∀ s < d, b s * b s = 1) (hq : ∀ v < 2 ^ d, qProd b d v = 1 → v = 0) {u v : ℕ}
    (hu : u < 2 ^ d) (hv : v < 2 ^ d) (h : qProd b d u = qProd b d v) : u = v := by
  have e : qProd b d (u ^^^ v) = 1 := by
    rw [qProd_xor hc hsq d le_rfl, h, qProd_mul_self hc hsq]
  have h0 := hq _ (Nat.xor_lt_two_pow hu hv) e
  calc u = (u ^^^ v) ^^^ v := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    _ = v := by rw [h0, Nat.zero_xor]

theorem el_injective {C : Dat} {b w : ℕ → G} (hM : Model C b w)
    (hq : ∀ v < 2 ^ C.d, qProd b C.d v = 1 → v = 0)
    (hw : ∀ i < 128, ∀ j < 128, ∀ z, w i = qProd b C.d z * w j → i = j)
    {x y : ℕ} (hx : x < 2 ^ (C.d + 7)) (hy : y < 2 ^ (C.d + 7))
    (h : el C.d b w x = el C.d b w y) : x = y := by
  rw [el, el, ← qProd_mod b C.d x, ← qProd_mod b C.d y] at h
  have hij : x >>> C.d = y >>> C.d := by
    refine hw _ (shiftRight_lt hx) _ (shiftRight_lt hy) (x % 2 ^ C.d ^^^ y % 2 ^ C.d) ?_
    rw [qProd_xor hM.comm hM.sq _ le_rfl, mul_assoc, ← h, ← mul_assoc,
      qProd_mul_self hM.comm hM.sq, one_mul]
  rw [hij, mul_left_inj] at h
  have hm := qProd_inj hM.comm hM.sq hq (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.mod_lt _ (Nat.two_pow_pos _)) h
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hij
  calc x = 2 ^ C.d * (x / 2 ^ C.d) + x % 2 ^ C.d := (Nat.div_add_mod x _).symm
    _ = 2 ^ C.d * (y / 2 ^ C.d) + y % 2 ^ C.d := by rw [hij, hm]
    _ = y := Nat.div_add_mod y _

theorem inv_mem_of_mul_closed [Finite G] {X : Set G} (h1 : (1 : G) ∈ X)
    (hm : ∀ a ∈ X, ∀ c ∈ X, a * c ∈ X) {x : G} (hx : x ∈ X) : x⁻¹ ∈ X := by
  have hp : ∀ n : ℕ, x ^ n ∈ X := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ]
      exact hm _ ih _ hx
  have e : x ^ (orderOf x - 1) = x⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos x),
      pow_orderOf_eq_one]
  exact e ▸ hp _

theorem el_zero (d : ℕ) (b w : ℕ → G) (h0 : w 0 = 1) : el d b w 0 = 1 := by
  rw [el, qProd_zero, Nat.zero_shiftRight, h0, one_mul]

@[expose] def elSub [Finite G] {C : Dat} {b w : ℕ → G} (hM : Model C b w) (h0 : w 0 = 1) :
    Subgroup G where
  carrier := el C.d b w '' {x | x < 2 ^ (C.d + 7)}
  one_mem' := ⟨0, Nat.two_pow_pos _, el_zero _ _ _ h0⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨mulC C x y, mulC_lt C x y, el_mulC hM hx hy⟩
  inv_mem' := by
    intro x hx
    refine inv_mem_of_mul_closed (X := el C.d b w '' {x | x < 2 ^ (C.d + 7)})
      ⟨0, Nat.two_pow_pos _, el_zero _ _ _ h0⟩ ?_ hx
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨mulC C x y, mulC_lt C x y, el_mulC hM hx hy⟩

theorem closure_eq_elSub [Finite G] {C : Dat} {b w : ℕ → G} (hM : Model C b w) (h0 : w 0 = 1)
    {gg : ℕ → G} {nG : ℕ} (hrel : ∀ g < nG, ∃ x < 2 ^ (C.d + 7), w 0 * gg g = el C.d b w x)
    (hwS : ∀ j < 128, w j ∈ Subgroup.closure (gg '' {g | g < nG}))
    (hqS : ∀ v < 2 ^ C.d, qProd b C.d v ∈ Subgroup.closure (gg '' {g | g < nG})) :
    Subgroup.closure (gg '' {g | g < nG}) = elSub hM h0 := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx, e⟩ := hrel g hg
    rw [h0, one_mul] at e
    exact ⟨x, hx, e.symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [el, ← qProd_mod]
    exact Subgroup.mul_mem _ (hqS _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (hwS _ (shiftRight_lt hx))

theorem card_elSub [Finite G] {C : Dat} {b w : ℕ → G} (hM : Model C b w) (h0 : w 0 = 1)
    (hq : ∀ v < 2 ^ C.d, qProd b C.d v = 1 → v = 0)
    (hw : ∀ i < 128, ∀ j < 128, ∀ z, w i = qProd b C.d z * w j → i = j) :
    Nat.card (elSub hM h0) = 2 ^ (C.d + 7) := by
  have e : {x : ℕ | x < 2 ^ (C.d + 7)} = ↑(Finset.range (2 ^ (C.d + 7))) := by
    ext x
    simp
  change Nat.card ↥(el C.d b w '' {x | x < 2 ^ (C.d + 7)}) = _
  have hinj : Set.InjOn (el C.d b w) {x | x < 2 ^ (C.d + 7)} :=
    fun x hx y hy h => el_injective hM hq hw hx hy h
  rw [Nat.card_coe_set_eq, hinj.ncard_image, e, Set.ncard_coe_finset,
    Finset.card_range]

end CFSG.KS.SporSch.Co1Rank

end
