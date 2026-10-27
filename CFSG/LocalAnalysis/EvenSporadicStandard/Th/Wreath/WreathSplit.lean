module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.VEndCentralizer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

@[expose] def wFix (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) : Subgroup G where
  carrier := {v | ∃ x : VSub hD, x.val = v ∧ w x = x}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro v v' ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x + y, by simp, by rw [map_add, hx, hy]⟩
  inv_mem' := by
    rintro v ⟨x, rfl, hx⟩
    exact ⟨-x, by simp, by rw [map_neg, hx]⟩

@[expose] def wKer (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) : Subgroup G where
  carrier := {v | ∃ x : VSub hD, x.val = v ∧ w x = 0}
  one_mem' := ⟨0, by simp, by simp⟩
  mul_mem' := by
    rintro v v' ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x + y, by simp, by rw [map_add, hx, hy, add_zero]⟩
  inv_mem' := by
    rintro v ⟨x, rfl, hx⟩
    exact ⟨-x, by simp, by rw [map_neg, hx, neg_zero]⟩

@[expose] def wComm (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) : Subgroup G where
  carrier := {n | n ∈ normalizer (omega1 D hD.comm : Set G) ∧
    vConj hD n * w = w * vConj hD n}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    rw [vConj_one, one_mul, mul_one]
  mul_mem' := by
    rintro n m ⟨hn, hcommn⟩ ⟨hm, hcommm⟩
    refine ⟨(normalizer (omega1 D hD.comm : Set G)).mul_mem hn hm, ?_⟩
    rw [vConj_mul hD hn hm, mul_assoc, hcommm, ← mul_assoc, hcommn, mul_assoc]
  inv_mem' := by
    rintro n ⟨hn, hcommn⟩
    refine ⟨(normalizer (omega1 D hD.comm : Set G)).inv_mem hn, ?_⟩
    have hleft := vConj_inv_mul hD hn
    have hright := vConj_mul_inv hD hn
    calc vConj hD n⁻¹ * w
        = vConj hD n⁻¹ * w * (vConj hD n * vConj hD n⁻¹) := by rw [hright, mul_one]
      _ = vConj hD n⁻¹ * (w * vConj hD n) * vConj hD n⁻¹ := by noncomm_ring
      _ = vConj hD n⁻¹ * (vConj hD n * w) * vConj hD n⁻¹ := by rw [hcommn]
      _ = (vConj hD n⁻¹ * vConj hD n) * w * vConj hD n⁻¹ := by noncomm_ring
      _ = w * vConj hD n⁻¹ := by rw [hleft, one_mul]

theorem mem_wFix_iff_exists (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) {v : G} :
    v ∈ wFix hD w ↔ ∃ x : VSub hD, x.val = v ∧ w x = x := Iff.rfl

theorem mem_wKer_iff_exists (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) {v : G} :
    v ∈ wKer hD w ↔ ∃ x : VSub hD, x.val = v ∧ w x = 0 := Iff.rfl

theorem mem_wFix_iff (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) {v : G}
    (hv : v ∈ omega1 D hD.comm) :
    v ∈ wFix hD w ↔ w (AbelianSub.mk v hv) = AbelianSub.mk v hv := by
  constructor
  · rintro ⟨x, hxv, hx⟩
    have hx' : AbelianSub.mk v hv = x := AbelianSub.ext (by rw [AbelianSub.val_mk, hxv])
    rw [hx', hx]
  · intro h
    exact ⟨AbelianSub.mk v hv, AbelianSub.val_mk v hv, h⟩

theorem mem_wKer_iff (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) {v : G}
    (hv : v ∈ omega1 D hD.comm) :
    v ∈ wKer hD w ↔ w (AbelianSub.mk v hv) = 0 := by
  constructor
  · rintro ⟨x, hxv, hx⟩
    have hx' : AbelianSub.mk v hv = x := AbelianSub.ext (by rw [AbelianSub.val_mk, hxv])
    rw [hx', hx]
  · intro h
    exact ⟨AbelianSub.mk v hv, AbelianSub.val_mk v hv, h⟩

theorem wFix_le_omega1 (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    wFix hD w ≤ omega1 D hD.comm := by
  rintro v ⟨x, rfl, -⟩
  exact x.2

theorem wKer_le_omega1 (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    wKer hD w ≤ omega1 D hD.comm := by
  rintro v ⟨x, rfl, -⟩
  exact x.2

theorem VSub.add_self_apply (hD : DHyp A Aa t D) (x : VSub hD) : x + x = 0 := by
  apply AbelianSub.ext
  rw [AbelianSub.val_add, AbelianSub.val_zero, ← pow_two]
  exact x.2.2

theorem wFix_inf_wKer_eq_bot (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    wFix hD w ⊓ wKer hD w = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro v ⟨⟨x, hxv, hx⟩, ⟨y, hyv, hy⟩⟩
  rw [Subgroup.mem_bot]
  have hxy : x = y := AbelianSub.ext (by rw [hxv, hyv])
  rw [← hxv, ← hx, hxy, hy]
  exact AbelianSub.val_zero

theorem exists_mem_wFix_mul_mem_wKer (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD))
    (hww : w * w = w) {v : G} (hv : v ∈ omega1 D hD.comm) :
    ∃ v₁ ∈ wFix hD w, ∃ v₂ ∈ wKer hD w, v = v₁ * v₂ := by
  refine ⟨(w (AbelianSub.mk v hv)).val,
    ⟨w (AbelianSub.mk v hv), rfl, ?_⟩,
    (AbelianSub.mk v hv - w (AbelianSub.mk v hv)).val,
    ⟨AbelianSub.mk v hv - w (AbelianSub.mk v hv), rfl, ?_⟩, ?_⟩
  · change (w * w) (AbelianSub.mk v hv) = w (AbelianSub.mk v hv)
    rw [hww]
  · rw [map_sub, show w (w (AbelianSub.mk v hv)) =
        (w * w) (AbelianSub.mk v hv) from rfl, hww, sub_self]
  · have hsum : w (AbelianSub.mk v hv) +
        (AbelianSub.mk v hv - w (AbelianSub.mk v hv)) = AbelianSub.mk v hv := by abel
    have hval := congrArg AbelianSub.val hsum
    rw [AbelianSub.val_add] at hval
    simpa using hval.symm

private theorem w_mul_vConj_t_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) :
    w * vConj hD t = vConj hD t * w + vConj hD t := by
  have hτ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  calc w * vConj hD t
      = (vConj hD t * vConj hD t) * w * vConj hD t := by rw [hτ, one_mul]
    _ = vConj hD t * (vConj hD t * w * vConj hD t) := by noncomm_ring
    _ = vConj hD t * (w + 1) := by rw [hτw]
    _ = vConj hD t * w + vConj hD t := by rw [mul_add, mul_one]

private theorem w_vConj_t_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) (x : VSub hD) :
    w (vConj hD t x) = vConj hD t (w x) + vConj hD t x := by
  have hwτ := w_mul_vConj_t_eq H W W2 hD hτw
  calc w (vConj hD t x) = (w * vConj hD t) x := by
        rw [AddMonoid.End.coe_mul]; rfl
    _ = ((vConj hD t * w + vConj hD t) x) := by rw [hwτ]
    _ = (vConj hD t * w) x + vConj hD t x := rfl
    _ = vConj hD t (w x) + vConj hD t x := by
        rw [AddMonoid.End.coe_mul]; rfl

theorem conj_t_mem_wKer_of_mem_wFix (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) {v : G} (hv : v ∈ wFix hD w) :
    t * v * t⁻¹ ∈ wKer hD w := by
  have ht := H.t_mem_normalizer_omega1 W W2 hD
  obtain ⟨x, rfl, hx⟩ := hv
  refine ⟨vConj hD t x, val_vConj_apply hD ht x, ?_⟩
  rw [w_vConj_t_apply H W W2 hD hτw, hx]
  exact VSub.add_self_apply hD _

def iota1 (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) (hww : w * w = w)
    (hAV : A ≤ omega1 D hD.comm) (a : A) : wFix hD w :=
  ⟨(w (AbelianSub.mk a.val (hAV a.2))).val,
    ⟨w (AbelianSub.mk a.val (hAV a.2)), rfl, by
      change (w * w) (AbelianSub.mk a.val (hAV a.2)) =
        w (AbelianSub.mk a.val (hAV a.2))
      rw [hww]⟩⟩

def iota2 (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) (hww : w * w = w)
    (hAV : A ≤ omega1 D hD.comm) (a : A) : wKer hD w :=
  ⟨((1 + w) (AbelianSub.mk a.val (hAV a.2))).val,
    ⟨(1 + w) (AbelianSub.mk a.val (hAV a.2)), rfl, by
      have h1 : (1 + w) (AbelianSub.mk a.val (hAV a.2)) =
          AbelianSub.mk a.val (hAV a.2) + w (AbelianSub.mk a.val (hAV a.2)) := rfl
      rw [h1, map_add, show w (w (AbelianSub.mk a.val (hAV a.2))) =
        (w * w) (AbelianSub.mk a.val (hAV a.2)) from rfl, hww]
      exact VSub.add_self_apply hD _⟩⟩

theorem iota1_mul (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) (hww : w * w = w)
    (hAV : A ≤ omega1 D hD.comm) (a a' : A) :
    iota1 hD w hww hAV (a * a') = iota1 hD w hww hAV a * iota1 hD w hww hAV a' := by
  apply Subtype.ext
  show (w (AbelianSub.mk (a * a').val _)).val =
    (w (AbelianSub.mk a.val _)).val * (w (AbelianSub.mk a'.val _)).val
  have hmk : (AbelianSub.mk (a * a').val (hAV (a * a').2) : VSub hD) =
      (AbelianSub.mk a.val (hAV a.2) : VSub hD) +
        (AbelianSub.mk a'.val (hAV a'.2) : VSub hD) := by
    apply AbelianSub.ext
    simp only [AbelianSub.val_mk, AbelianSub.val_add]
    rfl
  calc (w (AbelianSub.mk (a * a').val _)).val
      = (w (AbelianSub.mk a.val (hAV a.2) + AbelianSub.mk a'.val (hAV a'.2))).val := by
          rw [hmk]
    _ = (w (AbelianSub.mk a.val (hAV a.2)) + w (AbelianSub.mk a'.val (hAV a'.2))).val := by
          rw [map_add]
    _ = (w (AbelianSub.mk a.val (hAV a.2))).val *
          (w (AbelianSub.mk a'.val (hAV a'.2))).val := AbelianSub.val_add _ _

theorem iota2_mul (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) (hww : w * w = w)
    (hAV : A ≤ omega1 D hD.comm) (a a' : A) :
    iota2 hD w hww hAV (a * a') = iota2 hD w hww hAV a * iota2 hD w hww hAV a' := by
  apply Subtype.ext
  show ((1 + w) (AbelianSub.mk (a * a').val _)).val =
    ((1 + w) (AbelianSub.mk a.val _)).val * ((1 + w) (AbelianSub.mk a'.val _)).val
  have hmk : (AbelianSub.mk (a * a').val (hAV (a * a').2) : VSub hD) =
      (AbelianSub.mk a.val (hAV a.2) : VSub hD) +
        (AbelianSub.mk a'.val (hAV a'.2) : VSub hD) := by
    apply AbelianSub.ext
    simp only [AbelianSub.val_mk, AbelianSub.val_add]
    rfl
  calc ((1 + w) (AbelianSub.mk (a * a').val _)).val
      = ((1 + w) (AbelianSub.mk a.val (hAV a.2) +
          AbelianSub.mk a'.val (hAV a'.2))).val := by rw [hmk]
    _ = ((1 + w) (AbelianSub.mk a.val (hAV a.2)) +
          (1 + w) (AbelianSub.mk a'.val (hAV a'.2))).val := by rw [map_add]
    _ = ((1 + w) (AbelianSub.mk a.val (hAV a.2))).val *
          ((1 + w) (AbelianSub.mk a'.val (hAV a'.2))).val := AbelianSub.val_add _ _

theorem iota1_thV (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)} (hww : w * w = w)
    (hτw : vConj hD t * w * vConj hD t = w + 1) {y : VSub hD}
    (hy : y.val ∈ wFix hD w) :
    iota1 hD w hww (H.A_le_omega1 W W2 hD)
        ⟨thV t y.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem y)⟩ = ⟨y.val, hy⟩ := by
  have hy' : w y = y := by
    obtain ⟨x, hxv, hx⟩ := (mem_wFix_iff_exists hD w).1 hy
    have hxy : x = y := AbelianSub.ext (by rw [hxv])
    rwa [← hxy]
  apply Subtype.ext
  show (w (AbelianSub.mk (thV t y.val) _)).val = y.val
  have hNy : (AbelianSub.mk (thV t y.val)
        (H.A_le_omega1 W W2 hD (H.thV_mem_A W W2 hD (AbelianSub.val_mem y))) : VSub hD) =
      (vConj hD t + 1) y := by
    apply AbelianSub.ext
    rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk]
  rw [hNy]
  have hstep : w ((vConj hD t + 1) y) = y := by
    have h1 : (vConj hD t + 1) y = vConj hD t y + y := rfl
    rw [h1, map_add, w_vConj_t_apply H W W2 hD hτw, hy', VSub.add_self_apply hD, zero_add]
  rw [hstep]

theorem iota2_thV (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)} (hww : w * w = w)
    (hτw : vConj hD t * w * vConj hD t = w + 1) {y : VSub hD}
    (hy : y.val ∈ wKer hD w) :
    iota2 hD w hww (H.A_le_omega1 W W2 hD)
        ⟨thV t y.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem y)⟩ = ⟨y.val, hy⟩ := by
  have hy' : w y = 0 := by
    obtain ⟨x, hxv, hx⟩ := (mem_wKer_iff_exists hD w).1 hy
    have hxy : x = y := AbelianSub.ext (by rw [hxv])
    rwa [← hxy]
  apply Subtype.ext
  show ((1 + w) (AbelianSub.mk (thV t y.val) _)).val = y.val
  have hNy : (AbelianSub.mk (thV t y.val)
        (H.A_le_omega1 W W2 hD (H.thV_mem_A W W2 hD (AbelianSub.val_mem y))) : VSub hD) =
      (vConj hD t + 1) y := by
    apply AbelianSub.ext
    rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk]
  rw [hNy]
  have hwNy : w ((vConj hD t + 1) y) = vConj hD t y := by
    have h1 : (vConj hD t + 1) y = vConj hD t y + y := rfl
    rw [h1, map_add, w_vConj_t_apply H W W2 hD hτw, hy', map_zero, zero_add, add_zero]
  have hstep : (1 + w) ((vConj hD t + 1) y) = y := by
    have h1 : (1 + w) ((vConj hD t + 1) y) =
        (vConj hD t + 1) y + w ((vConj hD t + 1) y) := rfl
    rw [h1, hwNy]
    have h2 : (vConj hD t + 1) y = vConj hD t y + y := rfl
    rw [h2]
    calc (vConj hD t y + y) + vConj hD t y
        = y + (vConj hD t y + vConj hD t y) := by abel
      _ = y + 0 := by rw [VSub.add_self_apply hD]
      _ = y := add_zero y
  rw [hstep]

private theorem eq_zero_of_mem_A_of_w_eq_zero (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) {x : VSub hD} (hxA : x.val ∈ A)
    (hx0 : w x = 0) : x = 0 := by
  have hτx : vConj hD t x = x := by
    apply AbelianSub.ext
    rw [val_vConj_apply hD (H.t_mem_normalizer_omega1 W W2 hD)]
    have hcomm : t * x.val = x.val * t :=
      H.comm_of_mem_L (W.S_le ((W.mem_A_iff x.val).1 hxA).1)
    calc t * x.val * t⁻¹ = (x.val * t) * t⁻¹ := by rw [hcomm]
      _ = x.val := by group
  have hwx : w (vConj hD t x) = x := by
    rw [w_vConj_t_apply H W W2 hD hτw, hx0, map_zero, zero_add, hτx]
  rw [← hwx, hτx, hx0]

private theorem eq_zero_of_mem_A_of_one_add_w_eq_zero (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} (hτw : vConj hD t * w * vConj hD t = w + 1)
    {x : VSub hD} (hxA : x.val ∈ A) (hx0 : (1 + w) x = 0) : x = 0 := by
  have hτx : vConj hD t x = x := by
    apply AbelianSub.ext
    rw [val_vConj_apply hD (H.t_mem_normalizer_omega1 W W2 hD)]
    have hcomm : t * x.val = x.val * t :=
      H.comm_of_mem_L (W.S_le ((W.mem_A_iff x.val).1 hxA).1)
    calc t * x.val * t⁻¹ = (x.val * t) * t⁻¹ := by rw [hcomm]
      _ = x.val := by group
  have hwx : w x = x := by
    have h1 : x + w x = 0 := hx0
    have h2 : x + x = 0 := VSub.add_self_apply hD x
    exact add_left_cancel (by rw [h1, h2])
  have hwτx : w (vConj hD t x) = 0 := by
    rw [w_vConj_t_apply H W W2 hD hτw, hwx, hτx]
    exact VSub.add_self_apply hD _
  rw [← hwx, ← hτx]
  exact hwτx

theorem iota1_injective (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) :
    Function.Injective (iota1 hD w hww (H.A_le_omega1 W W2 hD)) := by
  intro a b hab
  let x : VSub hD := AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) -
    AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)
  have hweq : w (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)) =
      w (AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)) :=
    AbelianSub.ext (congrArg (fun x : wFix hD w => (x : G)) hab)
  have hxA : x.val ∈ A := by
    change (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) -
      AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)).val ∈ A
    rw [AbelianSub.val_sub, AbelianSub.val_mk, AbelianSub.val_mk]
    exact A.mul_mem a.2 (A.inv_mem b.2)
  have hx0 : w x = 0 := by
    change w (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) -
      AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)) = 0
    rw [map_sub, hweq, sub_self]
  have hzero : x = 0 := eq_zero_of_mem_A_of_w_eq_zero H W W2 hD hτw hxA hx0
  have heq : (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) : VSub hD) =
      (AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2) : VSub hD) := by
    have h' : (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) : VSub hD) -
        (AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2) : VSub hD) = 0 := by
      simpa only [x] using hzero
    exact sub_eq_zero.1 h'
  exact Subtype.ext (by simpa using congrArg AbelianSub.val heq)

theorem iota2_injective (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) :
    Function.Injective (iota2 hD w hww (H.A_le_omega1 W W2 hD)) := by
  intro a b hab
  let x : VSub hD := AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) -
    AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)
  have hweq : (1 + w) (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)) =
      (1 + w) (AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)) :=
    AbelianSub.ext (congrArg (fun x : wKer hD w => (x : G)) hab)
  have hxA : x.val ∈ A := by
    change (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) -
      AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)).val ∈ A
    rw [AbelianSub.val_sub, AbelianSub.val_mk, AbelianSub.val_mk]
    exact A.mul_mem a.2 (A.inv_mem b.2)
  have hx0 : (1 + w) x = 0 := by
    change (1 + w) (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) -
      AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2)) = 0
    rw [map_sub, hweq, sub_self]
  have hzero : x = 0 := eq_zero_of_mem_A_of_one_add_w_eq_zero H W W2 hD hτw hxA hx0
  have heq : (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) : VSub hD) =
      (AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2) : VSub hD) := by
    have h' : (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) : VSub hD) -
        (AbelianSub.mk b.val (H.A_le_omega1 W W2 hD b.2) : VSub hD) = 0 := by
      simpa only [x] using hzero
    exact sub_eq_zero.1 h'
  exact Subtype.ext (by simpa using congrArg AbelianSub.val heq)

theorem iota1_surjective (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) :
    Function.Surjective (iota1 hD w hww (H.A_le_omega1 W W2 hD)) := by
  intro y
  let y' : VSub hD := AbelianSub.mk y.val (wFix_le_omega1 hD w y.2)
  refine ⟨⟨thV t y.val, H.thV_mem_A W W2 hD (wFix_le_omega1 hD w y.2)⟩, ?_⟩
  have h := iota1_thV H W W2 hD hww hτw (y := y') y.2
  simpa only [y', AbelianSub.val_mk] using h

theorem iota2_surjective (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) :
    Function.Surjective (iota2 hD w hww (H.A_le_omega1 W W2 hD)) := by
  intro y
  let y' : VSub hD := AbelianSub.mk y.val (wKer_le_omega1 hD w y.2)
  refine ⟨⟨thV t y.val, H.thV_mem_A W W2 hD (wKer_le_omega1 hD w y.2)⟩, ?_⟩
  have h := iota2_thV H W W2 hD hww hτw (y := y') y.2
  simpa only [y', AbelianSub.val_mk] using h

theorem card_wFix (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)} (hww : w * w = w)
    (hτw : vConj hD t * w * vConj hD t = w + 1) : Nat.card (wFix hD w) = 16 := by
  rw [← W.A_card]
  exact (Nat.card_congr (Equiv.ofBijective (iota1 hD w hww (H.A_le_omega1 W W2 hD))
    ⟨iota1_injective H W W2 hD hww hτw, iota1_surjective H W W2 hD hww hτw⟩)).symm

theorem card_wKer (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)} (hww : w * w = w)
    (hτw : vConj hD t * w * vConj hD t = w + 1) : Nat.card (wKer hD w) = 16 := by
  rw [← W.A_card]
  exact (Nat.card_congr (Equiv.ofBijective (iota2 hD w hww (H.A_le_omega1 W W2 hD))
    ⟨iota2_injective H W W2 hD hww hτw, iota2_surjective H W W2 hD hww hτw⟩)).symm

theorem Hn_le_wComm (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n) :
    L ⊓ normalizer (A : Set G) ≤ wComm hD w := by
  rintro n ⟨hnL, hnA⟩
  refine ⟨?_, hwH n ⟨hnL, hnA⟩⟩
  have hn' : n ∈ normInL L A := ⟨hnL, fun x hx => (mem_normalizer_iff.1 hnA x).1 hx⟩
  exact H.normalizer_le_normalizer_omega1 W W2 hD
    (H.mem_normalizer_W5_of_mem_normInL W W2 hD hn')

private theorem w_conj_apply (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)} {n : G}
    (hn : n ∈ wComm hD w) (x : VSub hD) : w (vConj hD n x) = vConj hD n (w x) := by
  calc w (vConj hD n x) = (w * vConj hD n) x := by
        rw [AddMonoid.End.coe_mul]; rfl
    _ = (vConj hD n * w) x := by rw [← hn.2]
    _ = vConj hD n (w x) := by rw [AddMonoid.End.coe_mul]; rfl

theorem conj_mem_wFix_of_mem_wComm (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    {n : G} (hn : n ∈ wComm hD w) {v : G} (hv : v ∈ wFix hD w) :
    n * v * n⁻¹ ∈ wFix hD w := by
  obtain ⟨x, hxv, hx⟩ := hv
  refine ⟨vConj hD n x, ?_, ?_⟩
  · rw [val_vConj_apply hD hn.1, hxv]
  · rw [w_conj_apply hD hn, hx]

theorem conj_mem_wKer_of_mem_wComm (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    {n : G} (hn : n ∈ wComm hD w) {v : G} (hv : v ∈ wKer hD w) :
    n * v * n⁻¹ ∈ wKer hD w := by
  obtain ⟨x, hxv, hx⟩ := hv
  refine ⟨vConj hD n x, ?_, ?_⟩
  · rw [val_vConj_apply hD hn.1, hxv]
  · rw [w_conj_apply hD hn, hx, map_zero]

theorem iota1_conj_val (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G)) (a : A) :
    (iota1 hD w hww (H.A_le_omega1 W W2 hD)
        ⟨n * a.val * n⁻¹, (mem_normalizer_iff.1 hn.2 a.val).1 a.2⟩ : G) =
      n * (iota1 hD w hww (H.A_le_omega1 W W2 hD) a : G) * n⁻¹ := by
  have hnw : n ∈ wComm hD w := Hn_le_wComm H W W2 hD hwH hn
  show (w (AbelianSub.mk (n * a.val * n⁻¹) _)).val =
    n * (w (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))).val * n⁻¹
  have hmk : (AbelianSub.mk (n * a.val * n⁻¹)
        (H.A_le_omega1 W W2 hD ((mem_normalizer_iff.1 hn.2 a.val).1 a.2)) : VSub hD) =
      vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)) := by
    apply AbelianSub.ext
    rw [AbelianSub.val_mk, val_vConj_apply hD hnw.1, AbelianSub.val_mk]
  rw [hmk, w_conj_apply hD hnw, val_vConj_apply hD hnw.1]

theorem iota2_conj_val (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {n : G} (hn : n ∈ L ⊓ normalizer (A : Set G)) (a : A) :
    (iota2 hD w hww (H.A_le_omega1 W W2 hD)
        ⟨n * a.val * n⁻¹, (mem_normalizer_iff.1 hn.2 a.val).1 a.2⟩ : G) =
      n * (iota2 hD w hww (H.A_le_omega1 W W2 hD) a : G) * n⁻¹ := by
  have hnw : n ∈ wComm hD w := Hn_le_wComm H W W2 hD hwH hn
  show ((1 + w) (AbelianSub.mk (n * a.val * n⁻¹) _)).val =
    n * ((1 + w) (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))).val * n⁻¹
  have hmk : (AbelianSub.mk (n * a.val * n⁻¹)
        (H.A_le_omega1 W W2 hD ((mem_normalizer_iff.1 hn.2 a.val).1 a.2)) : VSub hD) =
      vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)) := by
    apply AbelianSub.ext
    rw [AbelianSub.val_mk, val_vConj_apply hD hnw.1, AbelianSub.val_mk]
  have hcomm : (1 + w) (vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))) =
      vConj hD n ((1 + w) (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))) := by
    calc (1 + w) (vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)))
        = vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)) +
            w (vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))) := rfl
      _ = vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2)) +
            vConj hD n (w (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))) := by
            rw [w_conj_apply hD hnw]
      _ = vConj hD n (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2) +
            w (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))) := by rw [map_add]
      _ = vConj hD n ((1 + w) (AbelianSub.mk a.val (H.A_le_omega1 W W2 hD a.2))) := rfl
  rw [hmk, hcomm, val_vConj_apply hD hnw.1]

private theorem thV_injective_on_wKer (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) {y z : VSub hD}
    (hy : y.val ∈ wKer hD w) (hz : z.val ∈ wKer hD w) (h : thV t y.val = thV t z.val) :
    y = z := by
  have h1 := iota2_thV H W W2 hD hww hτw hy
  have h2 := iota2_thV H W W2 hD hww hτw hz
  have hA : (⟨thV t y.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem y)⟩ : A) =
      ⟨thV t z.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem z)⟩ := Subtype.ext h
  have hfix : (⟨y.val, hy⟩ : wKer hD w) = ⟨z.val, hz⟩ := by
    rw [← h1, ← h2, hA]
  exact Subtype.ext (congrArg (fun x : wKer hD w => (x : G)) hfix)

private theorem thV_injective_on_wFix (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) {y z : VSub hD}
    (hy : y.val ∈ wFix hD w) (hz : z.val ∈ wFix hD w) (h : thV t y.val = thV t z.val) :
    y = z := by
  have h1 := iota1_thV H W W2 hD hww hτw hy
  have h2 := iota1_thV H W W2 hD hww hτw hz
  have hA : (⟨thV t y.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem y)⟩ : A) =
      ⟨thV t z.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem z)⟩ := Subtype.ext h
  have hfix : (⟨y.val, hy⟩ : wFix hD w) = ⟨z.val, hz⟩ := by
    rw [← h1, ← h2, hA]
  exact Subtype.ext (congrArg (fun x : wFix hD w => (x : G)) hfix)

theorem exists_mem_Hn_conj_eq_of_mem_wComm (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {n : G} (hn : n ∈ wComm hD w) :
    ∃ h₁ ∈ L ⊓ normalizer (A : Set G),
      ∀ v ∈ wFix hD w, h₁ * v * h₁⁻¹ = n * v * n⁻¹ := by
  classical
  have hAV := H.A_le_omega1 W W2 hD
  let i1 : A → wFix hD w := iota1 hD w hww hAV
  let f : G → G := fun a =>
    if ha : a ∈ A then thV t (n * (i1 ⟨a, ha⟩ : G) * n⁻¹) else 1
  have hfA : ∀ a ∈ A, f a ∈ A := by
    intro a ha
    dsimp only [f]
    rw [dif_pos ha]
    exact H.thV_mem_A W W2 hD
      (wFix_le_omega1 hD w (conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨a, ha⟩).2))
  have hfmul : ∀ a ∈ A, ∀ a' ∈ A, f (a * a') = f a * f a' := by
    intro a ha a' ha'
    dsimp only [f]
    rw [dif_pos (A.mul_mem ha ha'), dif_pos ha, dif_pos ha']
    have hι : (i1 ⟨a * a', A.mul_mem ha ha'⟩ : G) =
        (i1 ⟨a, ha⟩ : G) * (i1 ⟨a', ha'⟩ : G) := by
      dsimp only [i1]
      exact congrArg (fun x : wFix hD w => (x : G))
        (iota1_mul hD w hww hAV ⟨a, ha⟩ ⟨a', ha'⟩)
    rw [hι]
    have hxV : n * (i1 ⟨a, ha⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wFix_le_omega1 hD w (conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨a, ha⟩).2)
    have hyV : n * (i1 ⟨a', ha'⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wFix_le_omega1 hD w (conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨a', ha'⟩).2)
    calc thV t (n * ((i1 ⟨a, ha⟩ : G) * (i1 ⟨a', ha'⟩ : G)) * n⁻¹)
        = thV t ((n * (i1 ⟨a, ha⟩ : G) * n⁻¹) *
            (n * (i1 ⟨a', ha'⟩ : G) * n⁻¹)) := by
            congr 1
            group
      _ = thV t (n * (i1 ⟨a, ha⟩ : G) * n⁻¹) *
            thV t (n * (i1 ⟨a', ha'⟩ : G) * n⁻¹) := H.thV_mul W W2 hD hxV hyV
  have hfinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
    intro a ha b hb hab
    dsimp only [f] at hab
    rw [dif_pos ha, dif_pos hb] at hab
    have hya : n * (i1 ⟨a, ha⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wFix_le_omega1 hD w (conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨a, ha⟩).2)
    have hyb : n * (i1 ⟨b, hb⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wFix_le_omega1 hD w (conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨b, hb⟩).2)
    let ya : VSub hD := AbelianSub.mk (n * (i1 ⟨a, ha⟩ : G) * n⁻¹) hya
    let yb : VSub hD := AbelianSub.mk (n * (i1 ⟨b, hb⟩ : G) * n⁻¹) hyb
    have hyaFix : ya.val ∈ wFix hD w := by
      dsimp only [ya]
      rw [AbelianSub.val_mk]
      exact conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨a, ha⟩).2
    have hybFix : yb.val ∈ wFix hD w := by
      dsimp only [yb]
      rw [AbelianSub.val_mk]
      exact conj_mem_wFix_of_mem_wComm hD hn (i1 ⟨b, hb⟩).2
    have hth : thV t ya.val = thV t yb.val := by
      dsimp only [ya, yb]
      rw [AbelianSub.val_mk, AbelianSub.val_mk]
      exact hab
    have hyeq : ya = yb := thV_injective_on_wFix H W W2 hD hww hτw hyaFix hybFix hth
    have hval : (i1 ⟨a, ha⟩ : G) = (i1 ⟨b, hb⟩ : G) := by
      have h' := congrArg AbelianSub.val hyeq
      dsimp only [ya, yb] at h'
      rw [AbelianSub.val_mk, AbelianSub.val_mk] at h'
      have h'' : n * ((i1 ⟨a, ha⟩ : G) * n⁻¹) = n * ((i1 ⟨b, hb⟩ : G) * n⁻¹) := by
        simpa only [mul_assoc] using h'
      exact mul_right_cancel (mul_left_cancel h'')
    have hfix : (i1 ⟨a, ha⟩ : wFix hD w) = i1 ⟨b, hb⟩ := Subtype.ext hval
    exact congrArg Subtype.val
      (iota1_injective H W W2 hD hww hτw (by simpa only [i1] using hfix))
  obtain ⟨h₁, hh₁L, hh₁⟩ := W.surj f hfA hfmul hfinj
  have hh₁A : ∀ a ∈ A, h₁ * a * h₁⁻¹ ∈ A := by
    intro a ha
    rw [hh₁ a ha]
    exact hfA a ha
  have hh₁N : h₁ ∈ normalizer (A : Set G) := by
    have hmaple : A.map (MulAut.conj h₁).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hh₁A a ha
    have hcard : Nat.card (A.map (MulAut.conj h₁).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (f := (MulAut.conj h₁).toMonoidHom)
        (MulAut.conj h₁).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm))
  refine ⟨h₁, ⟨hh₁L, hh₁N⟩, ?_⟩
  intro v hv
  have hvV : v ∈ omega1 D hD.comm := wFix_le_omega1 hD w hv
  let yv : VSub hD := AbelianSub.mk v hvV
  have hyv : yv.val ∈ wFix hD w := by
    dsimp only [yv]
    rw [AbelianSub.val_mk]
    exact hv
  let a : A := ⟨thV t v, H.thV_mem_A W W2 hD hvV⟩
  have hv_eq : (i1 a : G) = v := by
    dsimp only [a, i1]
    have h := congrArg (fun x : wFix hD w => (x : G))
      (iota1_thV H W W2 hD hww hτw (y := yv) hyv)
    simpa only [yv, AbelianSub.val_mk] using h
  calc h₁ * v * h₁⁻¹
      = h₁ * (i1 a : G) * h₁⁻¹ := by rw [hv_eq]
    _ = (iota1 hD w hww hAV ⟨h₁ * a.val * h₁⁻¹, hh₁A a.val a.2⟩ : G) :=
          (iota1_conj_val H W W2 hD hww hτw hwH ⟨hh₁L, hh₁N⟩ a).symm
    _ = (iota1 hD w hww hAV ⟨f a.val, hfA a.val a.2⟩ : G) := by
          have hAeq : (⟨h₁ * a.val * h₁⁻¹, hh₁A a.val a.2⟩ : A) =
              ⟨f a.val, hfA a.val a.2⟩ := Subtype.ext (hh₁ a.val a.2)
          rw [hAeq]
    _ = n * (i1 a : G) * n⁻¹ := by
          have hfa : f a.val = thV t (n * (i1 a : G) * n⁻¹) := by
            dsimp only [f]
            rw [dif_pos a.2]
          have hmem : n * (i1 a : G) * n⁻¹ ∈ wFix hD w :=
            conj_mem_wFix_of_mem_wComm hD hn (i1 a).2
          let yv : VSub hD := AbelianSub.mk (n * (i1 a : G) * n⁻¹)
            (wFix_le_omega1 hD w hmem)
          have hyv : yv.val ∈ wFix hD w := by
            dsimp only [yv]
            rw [AbelianSub.val_mk]
            exact hmem
          have hAeq : (⟨f a.val, hfA a.val a.2⟩ : A) =
              ⟨thV t yv.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem yv)⟩ :=
            Subtype.ext (by simpa only [yv, AbelianSub.val_mk] using hfa)
          rw [hAeq]
          have h := congrArg (fun x : wFix hD w => (x : G))
            (iota1_thV H W W2 hD hww hτw (y := yv) hyv)
          simpa only [yv, AbelianSub.val_mk] using h
    _ = n * v * n⁻¹ := by rw [hv_eq]

theorem exists_mem_Hn_conj_eq_of_mem_wComm_wKer (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)} (hww : w * w = w)
    (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {n : G} (hn : n ∈ wComm hD w) :
    ∃ h₂ ∈ L ⊓ normalizer (A : Set G),
      ∀ v ∈ wKer hD w, h₂ * v * h₂⁻¹ = n * v * n⁻¹ := by
  classical
  have hAV := H.A_le_omega1 W W2 hD
  let i2 : A → wKer hD w := iota2 hD w hww hAV
  let f : G → G := fun a =>
    if ha : a ∈ A then thV t (n * (i2 ⟨a, ha⟩ : G) * n⁻¹) else 1
  have hfA : ∀ a ∈ A, f a ∈ A := by
    intro a ha
    dsimp only [f]
    rw [dif_pos ha]
    exact H.thV_mem_A W W2 hD
      (wKer_le_omega1 hD w (conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨a, ha⟩).2))
  have hfmul : ∀ a ∈ A, ∀ a' ∈ A, f (a * a') = f a * f a' := by
    intro a ha a' ha'
    dsimp only [f]
    rw [dif_pos (A.mul_mem ha ha'), dif_pos ha, dif_pos ha']
    have hι : (i2 ⟨a * a', A.mul_mem ha ha'⟩ : G) =
        (i2 ⟨a, ha⟩ : G) * (i2 ⟨a', ha'⟩ : G) := by
      dsimp only [i2]
      exact congrArg (fun x : wKer hD w => (x : G))
        (iota2_mul hD w hww hAV ⟨a, ha⟩ ⟨a', ha'⟩)
    rw [hι]
    have hxV : n * (i2 ⟨a, ha⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wKer_le_omega1 hD w (conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨a, ha⟩).2)
    have hyV : n * (i2 ⟨a', ha'⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wKer_le_omega1 hD w (conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨a', ha'⟩).2)
    calc thV t (n * ((i2 ⟨a, ha⟩ : G) * (i2 ⟨a', ha'⟩ : G)) * n⁻¹)
        = thV t ((n * (i2 ⟨a, ha⟩ : G) * n⁻¹) *
            (n * (i2 ⟨a', ha'⟩ : G) * n⁻¹)) := by
            congr 1
            group
      _ = thV t (n * (i2 ⟨a, ha⟩ : G) * n⁻¹) *
            thV t (n * (i2 ⟨a', ha'⟩ : G) * n⁻¹) := H.thV_mul W W2 hD hxV hyV
  have hfinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
    intro a ha b hb hab
    dsimp only [f] at hab
    rw [dif_pos ha, dif_pos hb] at hab
    have hya : n * (i2 ⟨a, ha⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wKer_le_omega1 hD w (conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨a, ha⟩).2)
    have hyb : n * (i2 ⟨b, hb⟩ : G) * n⁻¹ ∈ omega1 D hD.comm :=
      wKer_le_omega1 hD w (conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨b, hb⟩).2)
    let ya : VSub hD := AbelianSub.mk (n * (i2 ⟨a, ha⟩ : G) * n⁻¹) hya
    let yb : VSub hD := AbelianSub.mk (n * (i2 ⟨b, hb⟩ : G) * n⁻¹) hyb
    have hyaFix : ya.val ∈ wKer hD w := by
      dsimp only [ya]
      rw [AbelianSub.val_mk]
      exact conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨a, ha⟩).2
    have hybFix : yb.val ∈ wKer hD w := by
      dsimp only [yb]
      rw [AbelianSub.val_mk]
      exact conj_mem_wKer_of_mem_wComm hD hn (i2 ⟨b, hb⟩).2
    have hth : thV t ya.val = thV t yb.val := by
      dsimp only [ya, yb]
      rw [AbelianSub.val_mk, AbelianSub.val_mk]
      exact hab
    have hyeq : ya = yb := thV_injective_on_wKer H W W2 hD hww hτw hyaFix hybFix hth
    have hval : (i2 ⟨a, ha⟩ : G) = (i2 ⟨b, hb⟩ : G) := by
      have h' := congrArg AbelianSub.val hyeq
      dsimp only [ya, yb] at h'
      rw [AbelianSub.val_mk, AbelianSub.val_mk] at h'
      have h'' : n * ((i2 ⟨a, ha⟩ : G) * n⁻¹) = n * ((i2 ⟨b, hb⟩ : G) * n⁻¹) := by
        simpa only [mul_assoc] using h'
      exact mul_right_cancel (mul_left_cancel h'')
    have hfix : (i2 ⟨a, ha⟩ : wKer hD w) = i2 ⟨b, hb⟩ := Subtype.ext hval
    exact congrArg Subtype.val
      (iota2_injective H W W2 hD hww hτw (by simpa only [i2] using hfix))
  obtain ⟨h₂, hh₂L, hh₂⟩ := W.surj f hfA hfmul hfinj
  have hh₂A : ∀ a ∈ A, h₂ * a * h₂⁻¹ ∈ A := by
    intro a ha
    rw [hh₂ a ha]
    exact hfA a ha
  have hh₂N : h₂ ∈ normalizer (A : Set G) := by
    have hmaple : A.map (MulAut.conj h₂).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hh₂A a ha
    have hcard : Nat.card (A.map (MulAut.conj h₂).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (f := (MulAut.conj h₂).toMonoidHom)
        (MulAut.conj h₂).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm))
  refine ⟨h₂, ⟨hh₂L, hh₂N⟩, ?_⟩
  intro v hv
  have hvV : v ∈ omega1 D hD.comm := wKer_le_omega1 hD w hv
  let yv : VSub hD := AbelianSub.mk v hvV
  have hyv : yv.val ∈ wKer hD w := by
    dsimp only [yv]
    rw [AbelianSub.val_mk]
    exact hv
  let a : A := ⟨thV t v, H.thV_mem_A W W2 hD hvV⟩
  have hv_eq : (i2 a : G) = v := by
    dsimp only [a, i2]
    have h := congrArg (fun x : wKer hD w => (x : G))
      (iota2_thV H W W2 hD hww hτw (y := yv) hyv)
    simpa only [yv, AbelianSub.val_mk] using h
  calc h₂ * v * h₂⁻¹
      = h₂ * (i2 a : G) * h₂⁻¹ := by rw [hv_eq]
    _ = (iota2 hD w hww hAV ⟨h₂ * a.val * h₂⁻¹, hh₂A a.val a.2⟩ : G) :=
          (iota2_conj_val H W W2 hD hww hτw hwH ⟨hh₂L, hh₂N⟩ a).symm
    _ = (iota2 hD w hww hAV ⟨f a.val, hfA a.val a.2⟩ : G) := by
          have hAeq : (⟨h₂ * a.val * h₂⁻¹, hh₂A a.val a.2⟩ : A) =
              ⟨f a.val, hfA a.val a.2⟩ := Subtype.ext (hh₂ a.val a.2)
          rw [hAeq]
    _ = n * (i2 a : G) * n⁻¹ := by
          have hfa : f a.val = thV t (n * (i2 a : G) * n⁻¹) := by
            dsimp only [f]
            rw [dif_pos a.2]
          have hmem : n * (i2 a : G) * n⁻¹ ∈ wKer hD w :=
            conj_mem_wKer_of_mem_wComm hD hn (i2 a).2
          let yv : VSub hD := AbelianSub.mk (n * (i2 a : G) * n⁻¹)
            (wKer_le_omega1 hD w hmem)
          have hyv : yv.val ∈ wKer hD w := by
            dsimp only [yv]
            rw [AbelianSub.val_mk]
            exact hmem
          have hAeq : (⟨f a.val, hfA a.val a.2⟩ : A) =
              ⟨thV t yv.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem yv)⟩ :=
            Subtype.ext (by simpa only [yv, AbelianSub.val_mk] using hfa)
          rw [hAeq]
          have h := congrArg (fun x : wKer hD w => (x : G))
            (iota2_thV H W W2 hD hww hτw (y := yv) hyv)
          simpa only [yv, AbelianSub.val_mk] using h
    _ = n * v * n⁻¹ := by rw [hv_eq]

end CFSG.EvenSporadicStandard.ThStd
