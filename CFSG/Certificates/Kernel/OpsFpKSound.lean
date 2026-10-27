module

public import Certificates.Data.Kernel.OpsFpK
public import CFSG.Certificates.Kernel.OpsKSound
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
public import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Certificates.Kernel.Spor.OrdCanon

public section

namespace CFSG.KC.OpsK

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.SporSch.LyM CFSG.SectionRank.Native CFSG.Sporadic.He.Native
open CFSG.KC.OpsHom

theorem row0_mulM {p d : Nat} (hd : 0 < d) (X Y : Array (Array Nat)) :
    (mulM p d X Y)[0]! = vecMulRow p d X[0]! Y := by
  unfold mulM vecMulRow
  rw [ofFn_get! _ hd]

theorem row0_unpackL {d w S : Nat} (hd : 0 < d) (X : Nat) :
    (unpackL d w S X)[0]! = Array.ofFn (n := d) fun j => X / 2 ^ (w * j.val) % 2 ^ w := by
  unfold unpackL
  rw [ofFn_get! _ hd]
  congr 1
  funext j
  rw [land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change X >>> (S * 0 + w * j.val) % 2 ^ w = _
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_zero, Nat.zero_add]

theorem pow_lane {w k j : Nat} (hw : 0 < w) :
    2 ^ (w * k) / 2 ^ (w * j) % 2 ^ w = if j = k then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow]
  have key : (w * k = b + w * j ∧ b < w) ↔ (j = k ∧ b = 0) := by
    constructor
    · rintro ⟨h, hb⟩
      have h1 : (b + w * j) / w = j := by
        rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hb, Nat.zero_add]
      have h2 : w * k / w = k := Nat.mul_div_cancel_left k hw
      rw [h] at h2
      rw [h1] at h2
      subst h2
      omega
    · rintro ⟨rfl, rfl⟩
      exact ⟨by omega, hw⟩
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [and_comm, key]
  by_cases hjk : j = k
  · simp [hjk, Nat.testBit_one_eq_true_iff_self_eq_zero]
  · simp [hjk]

variable {p w S d T L H CM RM ONE LV HV : Nat}

theorem unit_eq (hd : 0 < d) (hw : 0 < w) (k : Nat) :
    (opsP p d).unit k = (unpackL d w S ((opsFpK p w S d T L H CM RM ONE).unit k))[0]! := by
  change (Array.ofFn (n := d) fun j => if j.val = k then 1 else 0) = _
  rw [row0_unpackL hd]
  congr 1
  funext j
  change _ = (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mul w k)) (Nat.blt k d)) /
    2 ^ (w * j.val) % 2 ^ w
  by_cases hk : k < d
  · have e : Nat.blt k d = true := Eq.mpr Nat.blt_eq hk
    rw [e]
    change _ = Nat.shiftLeft 1 (w * k) / 2 ^ (w * j.val) % 2 ^ w
    rw [shl_one, pow_lane hw]
  · have e : Nat.blt k d = false := by
      cases h : Nat.blt k d
      · rfl
      · exact absurd (Eq.mp Nat.blt_eq h) hk
    rw [e]
    have : j.val ≠ k := by omega
    simp [this]

theorem unit_valid (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (k : Nat) :
    validM p (d * S) L H ((opsFpK p w S d T L H CM RM ONE).unit k) = true := by
  obtain ⟨hp, -, hw, -⟩ := cfacts hc
  apply CFSG.KS.OrdCanon.validM_of_canon hc
  change Canon p d w (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mul w k))
    (Nat.blt k d))
  by_cases hk : k < d
  · have e : Nat.blt k d = true := Eq.mpr Nat.blt_eq hk
    rw [e]
    change Canon p d w (Nat.shiftLeft 1 (w * k))
    rw [shl_one]
    refine ⟨Nat.pow_lt_pow_right (by norm_num) (Nat.mul_lt_mul_of_pos_left
      (Nat.lt_of_lt_of_le hk (Nat.le_mul_of_pos_left d (by omega))) hw), fun t _ => ?_⟩
    unfold lane
    rw [pow_lane hw]
    split <;> omega
  · have e : Nat.blt k d = false := by
      cases h : Nat.blt k d
      · rfl
      · exact absurd (Eq.mp Nat.blt_eq h) hk
    rw [e]
    refine ⟨Nat.two_pow_pos _, fun t _ => ?_⟩
    unfold lane
    simp only [Nat.zero_div, Nat.zero_mod]
    omega

theorem vne_eqP (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 0 < d) {u v : Nat}
    (hu : validM p (d * S) L H u = true) (hv : validM p (d * S) L H v = true) :
    (opsP p d).vne (unpackL d w S u)[0]! (unpackL d w S v)[0]! =
      (opsFpK p w S d T L H CM RM ONE).vne u v := by
  obtain ⟨hp, hS, hw, -⟩ := cfacts hc
  have cu := validM_canon hc hu
  have cv := validM_canon hc hv
  have hent : ∀ {X : Nat}, Canon p d w X → ∀ j < d,
      ((unpackL d w S X)[0]!)[j]! % p = X / 2 ^ (w * j) % 2 ^ w := by
    intro X hX j hj
    rw [row0_unpackL hd, ofFn_get! _ hj]
    have h := hX.2 j (Nat.lt_of_lt_of_le hj (Nat.le_mul_of_pos_left d hd))
    unfold lane at h
    exact Nat.mod_eq_of_lt h
  change ((List.range d).any fun j => ((unpackL d w S u)[0]!)[j]! % p !=
    ((unpackL d w S v)[0]!)[j]! % p) = Bool.not (Nat.beq (Nat.mod u (Nat.shiftLeft 1 S))
      (Nat.mod v (Nat.shiftLeft 1 S)))
  have e2 : Nat.shiftLeft 1 S = 2 ^ (w * d) := by rw [shl_one, hS, Nat.mul_comm]
  rw [e2]
  change _ = !Nat.beq (u % 2 ^ (w * d)) (v % 2 ^ (w * d))
  by_cases h : u % 2 ^ (w * d) = v % 2 ^ (w * d)
  · have hb : Nat.beq (u % 2 ^ (w * d)) (v % 2 ^ (w * d)) = true := by rw [Nat.beq_eq]; exact h
    rw [hb]
    apply List.any_eq_false.2
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [hent cu j hj', hent cv j hj', (fields_eq_iff hw d u v).2 h j hj']
    simp
  · have hb : Nat.beq (u % 2 ^ (w * d)) (v % 2 ^ (w * d)) = false := by
      cases e : Nat.beq (u % 2 ^ (w * d)) (v % 2 ^ (w * d))
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [hb]
    apply List.any_eq_true.2
    by_contra hcon
    apply h
    refine (fields_eq_iff hw d u v).1 fun j hj => ?_
    by_contra hne
    refine hcon ⟨j, List.mem_range.2 hj, ?_⟩
    rw [hent cu j hj, hent cv j hj]
    simp [hne]

@[expose] noncomputable def homP (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 0 < d) :
    Hom (opsP p d) (opsFpK p w S d T L H CM RM ONE) where
  U := unpackL d w S
  W v := (unpackL d w S v)[0]!
  P X := validM p (d * S) L H X = true
  Q X := validM p (d * S) L H X = true
  mul hX hY := mulR_eqL hc hX hY
  one := idM_eqL hc
  eq hX hY := beq_eqL hc hX hY
  vmul {v a} hv ha := by
    obtain ⟨e, h⟩ := mulR_eqL hc hv ha
    refine ⟨?_, h⟩
    change vecMulRow p d (unpackL d w S v)[0]! (unpackL d w S a) =
      (unpackL d w S (mulR p w S d T L H CM RM v a))[0]!
    rw [← e, row0_mulM hd]
  unit k := ⟨unit_eq hd (cfacts hc).2.2.1 k, unit_valid hc k⟩
  vne hu hv := vne_eqP hc hd hu hv

end CFSG.KC.OpsK

end
