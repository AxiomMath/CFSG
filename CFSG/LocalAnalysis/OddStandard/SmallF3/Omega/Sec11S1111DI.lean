module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma two_dvd_two_pow {m : ℕ} (hm : 1 ≤ m) : 2 ∣ 2 ^ m := by
  simpa only [pow_one] using pow_dvd_pow 2 hm

private lemma two_ne_zero_zmod_two_pow {m : ℕ} (hm : 2 ≤ m) :
    (2 : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  have hdvd : 2 ^ m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 ^ m)).mp h
  have hle : 2 ^ m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : 4 ≤ 2 ^ m := by
    have h := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hm
    norm_num at h
    exact h
  omega

private lemma zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
  have hv : x.val = 0 ∨ x.val = 1 := by
    have := ZMod.val_lt x
    omega
  rcases hv with h0 | h1
  · left; rw [hx, h0]; simp
  · right; rw [hx, h1]; simp

private lemma zmod_two_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmod_two_eq_zero_or_one x).resolve_left h

private lemma zmod_two_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 :=
  (zmod_two_eq_zero_or_one x).resolve_right h

private lemma eq_half_of_two_mul_eq_zero {m : ℕ} (hm : 2 ≤ m) {i : ZMod (2 ^ m)}
    (h : (2 : ZMod (2 ^ m)) * i = 0) (hi : i ≠ 0) : i = (2 ^ m / 2 : ℕ) := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  have hlt : 2 < 2 ^ m := by
    have h4 : 4 ≤ 2 ^ m := by
      have h := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hm
      norm_num at h
      exact h
    omega
  have hval0 : ((2 : ZMod (2 ^ m)) * i).val = 0 := (ZMod.val_eq_zero _).mpr h
  have hval : 2 * i.val % 2 ^ m = 0 := by
    have := hval0
    rw [ZMod.val_mul, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt hlt] at this
    exact this
  have hdvd : 2 ^ m ∣ 2 * i.val := Nat.dvd_of_mod_eq_zero hval
  obtain ⟨t, ht⟩ := hdvd
  have hiN : i.val < 2 ^ m := ZMod.val_lt i
  have hNpos : 0 < 2 ^ m := by positivity
  have ht2 : t < 2 := by
    have hlt2 : 2 * i.val < 2 * 2 ^ m :=
      (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hiN
    rw [ht, Nat.mul_comm 2 (2 ^ m)] at hlt2
    exact (Nat.mul_lt_mul_left hNpos).mp hlt2
  have ht01 : t = 0 ∨ t = 1 := by omega
  rcases ht01 with rfl | rfl
  · exfalso
    have hi0 : i.val = 0 := by
      have : 2 * i.val = 0 := by simpa using ht
      omega
    apply hi
    rw [← ZMod.natCast_zmod_val i, hi0]; simp
  · have hival : i.val = 2 ^ m / 2 := by
      have hmul : 2 * i.val = 2 * (2 ^ m / 2) := by
        rw [Nat.mul_div_cancel' (two_dvd_two_pow (by omega : 1 ≤ m))]
        simpa using ht
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmul
    rw [← ZMod.natCast_zmod_val i, hival]

private lemma two_mul_eq_zero_of_orderOf_r {m : ℕ} {i : ZMod (2 ^ m)}
    (h : orderOf (DihedralGroup.r i) = 2) : (2 : ZMod (2 ^ m)) * i = 0 := by
  have hp : (DihedralGroup.r i) ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one (DihedralGroup.r i)
    rwa [h] at hpow
  have hp' : DihedralGroup.r (i * (2 : ZMod (2 ^ m))) = DihedralGroup.r 0 := by
    simpa only [DihedralGroup.r_pow, DihedralGroup.r_zero, Nat.cast_ofNat] using hp
  have h2 : i * (2 : ZMod (2 ^ m)) = 0 := by
    have hp'' := hp'
    rw [DihedralGroup.r.injEq] at hp''
    simpa using hp''
  simpa [mul_comm] using h2

private lemma r_invol_unique {m : ℕ} (hm : 2 ≤ m) {i j : ZMod (2 ^ m)}
    (hi : orderOf (DihedralGroup.r i) = 2) (hj : orderOf (DihedralGroup.r j) = 2) :
    DihedralGroup.r i = DihedralGroup.r j := by
  have hi0 : (2 : ZMod (2 ^ m)) * i = 0 := two_mul_eq_zero_of_orderOf_r hi
  have hj0 : (2 : ZMod (2 ^ m)) * j = 0 := two_mul_eq_zero_of_orderOf_r hj
  have hine : i ≠ 0 := by
    rintro rfl
    rw [DihedralGroup.r_zero, orderOf_one] at hi
    omega
  have hjne : j ≠ 0 := by
    rintro rfl
    rw [DihedralGroup.r_zero, orderOf_one] at hj
    omega
  rw [eq_half_of_two_mul_eq_zero hm hi0 hine, eq_half_of_two_mul_eq_zero hm hj0 hjne]

private lemma zmod_two_mul_of_par_zero {m : ℕ} (hm1 : 1 ≤ m) {x : ZMod (2 ^ m)}
    (hx : ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) x = 0) :
    ∃ k : ZMod (2 ^ m), x = 2 * k := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  have hx'' : (ZMod.cast x : ZMod 2) = 0 := by
    simpa only [ZMod.castHom_apply] using hx
  have hx' : (x.val : ZMod 2) = 0 := by
    simpa only [ZMod.cast_eq_val] using hx''
  have hdvd : 2 ∣ x.val := (CharP.cast_eq_zero_iff (ZMod 2) 2 x.val).mp hx'
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨(q : ZMod (2 ^ m)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hq]
  push_cast
  ring

private lemma central_invol_is_rotation {m : ℕ} (hm : 2 ≤ m) {z : DihedralGroup (2 ^ m)}
    (hz2 : orderOf z = 2) (hzc : ∀ u : DihedralGroup (2 ^ m), z * u = u * z) :
    ∃ j, z = DihedralGroup.r j := by
  rcases z with j | j
  · exact ⟨j, rfl⟩
  · exfalso
    have hcomm := hzc (DihedralGroup.r 1)
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq] at hcomm
    have h1 : (1 : ZMod (2 ^ m)) = -1 :=
      add_left_cancel (a := j) (by simpa [sub_eq_add_neg] using hcomm)
    have htwo : (2 : ZMod (2 ^ m)) = 0 := by
      have h2' : (1 : ZMod (2 ^ m)) + 1 = 0 := by
        rw [add_eq_zero_iff_eq_neg]
        exact h1
      simpa [one_add_one_eq_two] using h2'
    exact two_ne_zero_zmod_two_pow hm htwo

private abbrev evenSub {m : ℕ} (hm : 1 ≤ m) : Subgroup (DihedralGroup (2 ^ m)) where
  carrier := {x | match x with
    | DihedralGroup.r i => ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) i = 0
    | DihedralGroup.sr i => ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) i = 0}
  mul_mem' := by
    rintro (a | a) (b | b) ha hb
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 0 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (a + b) = 0
      rw [map_add, ha', hb']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 0 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (b - a) = 0
      rw [map_sub, hb', ha']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 0 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (a + b) = 0
      rw [map_add, ha', hb']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 0 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (b - a) = 0
      rw [map_sub, hb', ha']; decide
  one_mem' := by
    change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (0 : ZMod (2 ^ m)) = 0
    rw [map_zero]
  inv_mem' := by
    rintro (a | a) ha
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (-a) = 0
      rw [map_neg, ha']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      exact ha'

private abbrev oddSub {m : ℕ} (hm : 1 ≤ m) : Subgroup (DihedralGroup (2 ^ m)) where
  carrier := {x | match x with
    | DihedralGroup.r i => ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) i = 0
    | DihedralGroup.sr i => ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) i = 1}
  mul_mem' := by
    rintro (a | a) (b | b) ha hb
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 0 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (a + b) = 0
      rw [map_add, ha', hb']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 1 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (b - a) = 1
      rw [map_sub, hb', ha']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 1 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 0 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (a + b) = 1
      rw [map_add, ha', hb']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 1 := ha
      have hb' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) b = 1 := hb
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (b - a) = 0
      rw [map_sub, hb', ha']; decide
  one_mem' := by
    change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (0 : ZMod (2 ^ m)) = 0
    rw [map_zero]
  inv_mem' := by
    rintro (a | a) ha
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 0 := ha
      change ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) (-a) = 0
      rw [map_neg, ha']; decide
    · have ha' : ZMod.castHom (two_dvd_two_pow hm) (ZMod 2) a = 1 := ha
      exact ha'

private lemma conj_sr_eq {m : ℕ} (hm1 : 1 ≤ m) {a c : ZMod (2 ^ m)}
    (h : ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) a
       = ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) c) :
    ∃ k : ZMod (2 ^ m), DihedralGroup.r k * DihedralGroup.sr a * (DihedralGroup.r k)⁻¹
      = DihedralGroup.sr c := by
  have hx : ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) (a - c) = 0 := by
    rw [map_sub, h]; exact sub_self _
  obtain ⟨k, hk⟩ := zmod_two_mul_of_par_zero hm1 hx
  have hc : a - 2 * k = c := by
    rw [← hk]
    abel
  refine ⟨k, ?_⟩
  rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r, ← hc]
  congr 1
  ring

theorem sec11_dihedral_invol_mem_aux {m : ℕ} (hm : 2 ≤ m) {Θ : Set (DihedralGroup (2 ^ m))}
    {z : DihedralGroup (2 ^ m)} (hgen : Subgroup.closure Θ = ⊤) (hΘ2 : ∀ s ∈ Θ, orderOf s = 2)
    (hconj : ∀ s ∈ Θ, ∀ u : DihedralGroup (2 ^ m), u * s * u⁻¹ ∈ Θ) (hz2 : orderOf z = 2)
    (hzc : ∀ u : DihedralGroup (2 ^ m), z * u = u * z) (hzΘ : z ∉ Θ)
    {d : DihedralGroup (2 ^ m)} (hd2 : orderOf d = 2) (hdz : d ≠ z) : d ∈ Θ := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨j, hzj⟩ := central_invol_is_rotation hm hz2 hzc
  have hzj2 : orderOf (DihedralGroup.r j) = 2 := by rwa [hzj] at hz2
  have hΘ_refl : ∀ s ∈ Θ, ∃ i, s = DihedralGroup.sr i := by
    intro s hs
    rcases s with i | i
    · exfalso
      have hi2 : orderOf (DihedralGroup.r i) = 2 := hΘ2 _ hs
      have hiz : DihedralGroup.r i = z := by
        rw [hzj]
        exact r_invol_unique hm hi2 hzj2
      exact hzΘ (hiz ▸ hs)
    · exact ⟨i, rfl⟩
  have h_exists_even : ∃ a : ZMod (2 ^ m), DihedralGroup.sr a ∈ Θ ∧
      ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) a = 0 := by
    by_contra h
    push_neg at h
    have hsub : Θ ⊆ oddSub hm1 := by
      intro s hs
      obtain ⟨i, rfl⟩ := hΘ_refl s hs
      change ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) i = 1
      exact zmod_two_ne_zero (h i hs)
    have htop : (⊤ : Subgroup (DihedralGroup (2 ^ m))) ≤ oddSub hm1 := by
      rw [← hgen]
      exact (Subgroup.closure_le (oddSub hm1)).mpr hsub
    have hmem : DihedralGroup.r 1 ∈ oddSub hm1 :=
      htop (Subgroup.mem_top (DihedralGroup.r 1))
    change ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) (1 : ZMod (2 ^ m)) = 0 at hmem
    have h1 : ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) (1 : ZMod (2 ^ m)) = 1 :=
      map_one _
    exact one_ne_zero (h1.symm.trans hmem)
  have h_exists_odd : ∃ b : ZMod (2 ^ m), DihedralGroup.sr b ∈ Θ ∧
      ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) b = 1 := by
    by_contra h
    push_neg at h
    have hsub : Θ ⊆ evenSub hm1 := by
      intro s hs
      obtain ⟨i, rfl⟩ := hΘ_refl s hs
      change ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) i = 0
      exact zmod_two_ne_one (h i hs)
    have htop : (⊤ : Subgroup (DihedralGroup (2 ^ m))) ≤ evenSub hm1 := by
      rw [← hgen]
      exact (Subgroup.closure_le (evenSub hm1)).mpr hsub
    have hmem : DihedralGroup.r 1 ∈ evenSub hm1 :=
      htop (Subgroup.mem_top (DihedralGroup.r 1))
    change ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) (1 : ZMod (2 ^ m)) = 0 at hmem
    have h1 : ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) (1 : ZMod (2 ^ m)) = 1 :=
      map_one _
    exact one_ne_zero (h1.symm.trans hmem)
  obtain ⟨a, haΘ, hapar⟩ := h_exists_even
  obtain ⟨b, hbΘ, hbpar⟩ := h_exists_odd
  rcases d with i | i
  · exfalso
    have hiz : DihedralGroup.r i = z := by
      rw [hzj]
      exact r_invol_unique hm hd2 hzj2
    exact hdz hiz
  · rcases zmod_two_eq_zero_or_one
        (ZMod.castHom (two_dvd_two_pow hm1) (ZMod 2) i) with hc | hc
    · obtain ⟨k, hk⟩ := conj_sr_eq (a := a) (c := i) hm1 (by rw [hapar, hc])
      rw [← hk]
      exact hconj (DihedralGroup.sr a) haΘ (DihedralGroup.r k)
    · obtain ⟨k, hk⟩ := conj_sr_eq (a := b) (c := i) hm1 (by rw [hbpar, hc])
      rw [← hk]
      exact hconj (DihedralGroup.sr b) hbΘ (DihedralGroup.r k)

theorem sec11_dihedral_invol_mem {E : Type*} [Group E] {D : Subgroup E} {m : ℕ} (hm : 2 ≤ m)
    (e : ↥D ≃* DihedralGroup (2 ^ m)) {Θ : Set E} {z : E} (hΘD : Θ ⊆ D)
    (hgen : Subgroup.closure Θ = D) (hΘ2 : ∀ s ∈ Θ, orderOf s = 2)
    (hconj : ∀ s ∈ Θ, ∀ u ∈ D, u * s * u⁻¹ ∈ Θ) (hzD : z ∈ D) (hz2 : orderOf z = 2)
    (hzc : ∀ u ∈ D, z * u = u * z) (hzΘ : z ∉ Θ) {d : E} (hd : d ∈ D) (hd2 : orderOf d = 2)
    (hdz : d ≠ z) : d ∈ Θ := by
  let S : Set ↥D := ((↑) : ↥D → E) ⁻¹' Θ
  let Θ' : Set (DihedralGroup (2 ^ m)) := (e : ↥D → DihedralGroup (2 ^ m)) '' S
  let z' : DihedralGroup (2 ^ m) := e ⟨z, hzD⟩
  let d' : DihedralGroup (2 ^ m) := e ⟨d, hd⟩
  have hS : Subgroup.closure S = ⊤ := by
    apply Subgroup.map_injective (f := D.subtype) Subtype.coe_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have hset : D.subtype '' S = Θ := by
      change (↑) '' (((↑) : ↥D → E) ⁻¹' Θ) = Θ
      rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
      exact Set.inter_eq_left.mpr hΘD
    rw [hset, hgen]
  have hgen' : Subgroup.closure Θ' = ⊤ := by
    have hmap := MonoidHom.map_closure e.toMonoidHom S
    rw [hS, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
    exact hmap.symm
  have hΘ2' : ∀ s ∈ Θ', orderOf s = 2 := by
    intro s hs
    obtain ⟨t, htS, rfl⟩ := hs
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hΘ2 (t : E) htS
  have hconj' : ∀ s ∈ Θ', ∀ u : DihedralGroup (2 ^ m), u * s * u⁻¹ ∈ Θ' := by
    intro s hs u
    obtain ⟨t, htS, rfl⟩ := hs
    obtain ⟨v, rfl⟩ := e.surjective u
    refine ⟨v * t * v⁻¹, ?_, ?_⟩
    · show ((v * t * v⁻¹ : ↥D) : E) ∈ Θ
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        hconj (t : E) htS (v : E) v.property
    · rw [map_mul, map_mul, map_inv]
  have hz2' : orderOf z' = 2 := by
    change orderOf (e ⟨z, hzD⟩) = 2
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2]
  have hzc' : ∀ u : DihedralGroup (2 ^ m), z' * u = u * z' := by
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    change e ⟨z, hzD⟩ * e v = e v * e ⟨z, hzD⟩
    rw [← map_mul, ← map_mul]
    rw [e.injective.eq_iff]
    apply Subtype.ext
    simpa using hzc (v : E) v.property
  have hzΘ' : z' ∉ Θ' := by
    rintro hz
    obtain ⟨t, htS, hzt⟩ := hz
    have htz : t = ⟨z, hzD⟩ := e.injective hzt
    exact hzΘ (by rwa [htz] at htS)
  have hd2' : orderOf d' = 2 := by
    change orderOf (e ⟨d, hd⟩) = 2
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hd2]
  have hdz' : d' ≠ z' := by
    intro h
    apply hdz
    have : (⟨d, hd⟩ : ↥D) = ⟨z, hzD⟩ := e.injective h
    exact congrArg Subtype.val this
  have hd'Θ' : d' ∈ Θ' :=
    sec11_dihedral_invol_mem_aux hm hgen' hΘ2' hconj' hz2' hzc' hzΘ' hd2' hdz'
  obtain ⟨t, htS, hdt⟩ := hd'Θ'
  have htd : (t : E) = d := congrArg Subtype.val (e.injective hdt)
  rw [← htd]
  exact htS

end CFSG.OddStandard.SmallF3.Omega
